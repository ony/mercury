/*
** Copyright (C) 1998 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
**      Detailed profiling module
**
**	Main Authors : conway
*/

#include        "mercury_imp.h"

#include	<stdio.h>
#include	<unistd.h>
#include	<errno.h>
#include	<string.h>

#include	"mercury_prof.h"
#include	"mercury_stack_layout.h"
#include	"mercury_wrapper.h"
#include        "mercury_std.h"

/*
** Global Variables
*/

#ifdef	MR_PROFILE_DEEP

/*
** Manufacture the root of the SCCId tree, except for the callee
** layout structure, which we don't know yet. It is filled in by
** MR_prof_init_globals(), which also creates the root SCCInstance.
*/

extern const MR_Stack_Layout_Entry mercury_data__layout__do_interpreter;


MR_CallSite MR_prof_main_callsite = {
	&mercury_data__layout__do_interpreter,
	(MR_Stack_Layout_Entry *) NULL,	/* don't know till runtime */
	"Mercury Engine",
	0
};

MR_MAKE_SCC_ID(MR_prof_root_scc_id, { &MR_prof_main_callsite }, { }, { });

MR_SCCInstance		*MR_prof_root_scc;

MR_InterCallProfile	MR_prof_root_proc = { { 0, 0, 0, 0 }, 0 };

MR_ProcCallProfile	*MR_prof_current_proc = NULL;

#ifdef MR_DEEP_PARENTS
MR_SCCInstance		*MR_prof_current_scc = NULL;
#endif

MR_Count		MR_prof_num_sigs=0;

#endif

/*
** Local function declarations
*/

#ifdef MR_PROFILE_DEEP
  MR_SCCInstance *MR_prof_allocate_scc_instance(const MR_SCCId *scc);
  static void MR_prof_dump_prof_tree(FILE *fp, MR_SCCInstance *scc);
  static void MR_prof_dump_fo_calls(FILE *fp, int n, int m, const MR_SCCId *id,
		MR_InterCallProfile **profs, const MR_CallSite **sites);
  static void MR_prof_dump_ho_calls(FILE *fp, int n, int m, const MR_SCCId *id,
		MR_HigherOrderCallProfile **profs, const MR_CallSite **sites);
  static void MR_prof_dump_cm_calls(FILE *fp, int n, int m, const MR_SCCId *id,
		MR_ClassMethodCallProfile **profs, const MR_CallSite **sites);
  static void MR_prof_dump_callbacks(FILE *fp, int m, const MR_SCCId *id,
		MR_CallBackCallProfile *cbacks);
  static void MR_prof_dump_call_data(FILE *fp, const char *prefix, int n,
		const MR_Stack_Layout_Entry *caller,
		const MR_Stack_Layout_Entry *callee, 
		MR_ProcCallProfile *prof, int child);
  static void MR_prof_dump_proc_call_profile(FILE *fp, MR_ProcCallProfile *p);
  static void MR_prof_dump_ppid(FILE *fp, const MR_Stack_Layout_Proc_Id *ppid);
  static void MR_prof_dump_SCCid(FILE *fp, const MR_SCCId *SCCid);
  static void MR_prof_dump_ppid_table(FILE *fp);
  static void MR_prof_dump_ppid_defn(FILE *fp, int ppid_num,
		const MR_Stack_Layout_Proc_Id *ppid);
  static void MR_prof_dump_SCCid_table(FILE *fp);
  static void MR_prof_output_call_site_list(FILE *fp, int n,
		const MR_CallSite **calls);
  static void MR_prof_dump_string(FILE *fp, const char *s);

  static const MR_SCCId *MR_prof_get_scc_id(const MR_Stack_Layout_Proc_Id *p);
#endif

/*----------------------------------------------------------------------------*/

#ifdef MR_PROFILE_DEEP

static const MR_SCCId *
MR_prof_get_scc_id(const MR_Stack_Layout_Proc_Id *p)
{
	const MR_SCCId *sccid;

	assert(p);

	sccid = p->MR_proc_user.MR_user_scc_id;
	if (MR_tag((const Word) sccid))
	{
		return MR_ENTRY_LAYOUT_SCC_ID((const MR_Stack_Layout_Entry *)
					MR_strip_tag((Word) sccid));
	} else {
		return sccid;
	}
}

void
MR_prof_init_globals(MR_Stack_Layout_Entry *proclayout)
{
	const MR_SCCId *root_scc_id;

	program_entry_layout = proclayout;

	MR_prof_main_callsite.callee = proclayout;

	MR_prof_current_proc = (MR_ProcCallProfile *) &MR_prof_root_proc;
	MR_scc_from_here(&MR_prof_root_scc_id);
	MR_prof_root_scc =
			((MR_InterCallProfile *)MR_prof_current_proc)->child;
}

MR_ProcCallProfile *
MR_prof_ensure_fo_call_slot(int site_num)
{
	MR_SCCInstance *scc;
	MR_InterCallProfile *tmp;

	scc = ((MR_InterCallProfile *)MR_prof_current_proc)->child;

	assert((scc != NULL) && (scc->fo_calls != NULL));

	if (scc->fo_calls[site_num] != NULL)
		return &(scc->fo_calls[site_num]->prof);
	
	tmp = (MR_InterCallProfile *)
		MR_malloc(sizeof(MR_InterCallProfile));
	tmp->prof.calls = 0;
	tmp->prof.successes = 0;
	tmp->prof.failures = 0;
	tmp->prof.quanta = 0;
		/*
		** Because this is an intra scc call, then the
		** child is the same as the parent.
		*/
	tmp->child = scc;

	scc->fo_calls[site_num] = tmp;

	return &(tmp->prof);
}

MR_ProcCallProfile *
MR_prof_ensure_fo_call_inter_slot(int site_num, const MR_SCCId *child_scc_id)
{
	MR_SCCInstance *scc;
	MR_InterCallProfile *tmp;

	scc = ((MR_InterCallProfile *)MR_prof_current_proc)->child;

	assert((scc != NULL) && (scc->fo_calls != NULL));

	assert(site_num < scc->scc->num_fo_calls);

	if (scc->fo_calls[site_num] != NULL)
		return &(scc->fo_calls[site_num]->prof);
	
	tmp = (MR_InterCallProfile *)
		MR_malloc(sizeof(MR_InterCallProfile));
	tmp->prof.calls = 0;
	tmp->prof.successes = 0;
	tmp->prof.failures = 0;
	tmp->prof.quanta = 0;
	tmp->child = NULL;
/*
	tmp->child = MR_prof_allocate_scc_instance(child_scc_id);
*/
	scc->fo_calls[site_num] = tmp;

	return &(tmp->prof);
}

MR_ProcCallProfile *
MR_prof_ensure_fo_call_inter_slot2(int site_num,
	const MR_Stack_Layout_Entry *proc_layout)
{
	const MR_SCCId *child_scc_id;

	child_scc_id = MR_ENTRY_LAYOUT_SCC_ID(proc_layout);
	return MR_prof_ensure_fo_call_inter_slot(site_num, child_scc_id);
}

MR_ProcCallProfile *
MR_prof_ensure_ho_call_inter_slot(int site_num,
	MR_Closure *closure)
{
	MR_SCCInstance *scc;

	scc = ((MR_InterCallProfile *)MR_prof_current_proc)->child;

	assert(scc);
	assert(site_num < scc->scc->num_ho_calls);

	return MR_prof_proc_const_call(&(scc->ho_calls[site_num]), closure);
}

MR_ProcCallProfile *
MR_prof_ensure_special_ho_call_inter_slot(int site_num, Code *code_ptr,
		const MR_Stack_Layout_Entry *entry_layout)
{
	MR_SCCInstance *scc;

	scc = ((MR_InterCallProfile *)MR_prof_current_proc)->child;

	assert(scc);
	return MR_prof_special_proc_const_call(&(scc->ho_calls[site_num]), code_ptr,
			&(entry_layout->MR_sle_proc_id));
}

MR_ProcCallProfile *
MR_prof_ensure_c_calls_mercury(const MR_Stack_Layout_Entry *layout)
{
	MR_SCCInstance *scc;
	MR_CallBackCallProfile *tmp;

	scc = ((MR_InterCallProfile *)MR_prof_current_proc)->child;

	assert(scc);

	tmp = (MR_CallBackCallProfile *)
		MR_malloc(sizeof(MR_CallBackCallProfile));
	tmp->prof.calls = 0;
	tmp->prof.successes = 0;
	tmp->prof.failures = 0;
	tmp->prof.quanta = 0;
	tmp->child = NULL;

	tmp->entry  = (MR_Stack_Layout_Entry *) &(layout->MR_sle_code_addr);
	tmp->proc_id = (MR_Stack_Layout_Proc_Id *) &(layout->MR_sle_proc_id);

	tmp->next = scc->callbacks;
	scc->callbacks = tmp;

	return &(tmp->prof);
}

MR_ProcCallProfile *
MR_prof_proc_const_call(MR_MultiCallProfile **call_list, MR_Closure *closure)
{
	MR_Stack_Layout_Proc_Id *proc_id;

	assert((call_list != NULL) && (closure != NULL));

	proc_id = closure->MR_closure_layout->proc_id;
	return MR_prof_special_proc_const_call(call_list, closure->MR_closure_code, proc_id);
}

MR_ProcCallProfile *
MR_prof_special_proc_const_call(MR_MultiCallProfile **call_list, Code *code_ptr, const MR_Stack_Layout_Proc_Id *proc_id)
{
	MR_MultiCallProfile *tmp;
	const MR_SCCId *child_scc_id;

	child_scc_id = MR_prof_get_scc_id(proc_id);

	/*
	** Search the list of HigherOrderCallProfiles for the proc we've been given.
	** This should probably use a move-to-front list to exploit locality.
	*/
	for(tmp = *call_list; tmp; tmp = tmp->next)
	{
		if (tmp->entry == code_ptr)
			return &(tmp->prof);
	}

	/*
	** If we didn't find the proc in the list, then allocate a new
	** HigherOrderCallProfile and stick it on the front of the list.
	*/

	tmp = (MR_HigherOrderCallProfile *)
		MR_malloc(sizeof(MR_HigherOrderCallProfile));
	tmp->prof.calls = 0;
	tmp->prof.successes = 0;
	tmp->prof.failures = 0;
	tmp->prof.quanta = 0;
	tmp->child = NULL;
/*
	tmp->child = MR_prof_allocate_scc_instance(child_scc_id);
*/
	tmp->entry = code_ptr;
	tmp->proc_id = proc_id;
	tmp->next = *call_list;

	*call_list = tmp;

	return &(tmp->prof);
}

MR_SCCInstance *
MR_prof_ensure_scc(const MR_SCCId *scc_id)
{
	MR_SCCInstance *inst;
	if (((MR_InterCallProfile *) MR_prof_current_proc)->child)
	{
	    	inst = ((MR_InterCallProfile *) MR_prof_current_proc)->child;
	} else {
		inst = MR_prof_allocate_scc_instance(scc_id);
		MR_prof_set_current_proc(inst);
#ifdef MR_DEEP_PARENTS
		inst->parent = MR_prof_current_scc;
#endif
	}

#ifdef MR_DEEP_PARENTS
	MR_prof_current_scc = inst;
#endif
	return inst;
}

MR_SCCInstance *
MR_prof_allocate_scc_instance(const MR_SCCId *child_scc_id)
{
	static int	scc_num=1;
	MR_SCCInstance *child;
	size_t nbytes;

		/*
		** If child_scc_id then we have encountered a leaf
		** procedure, so we don't need an MR_SCCInstance.
		*/
	if (child_scc_id == NULL)
	{
		return NULL;
	}

		/*
		** If we have have entered this SCC without leaving it
		** then `inst' will be non-null, and will point to the
		** root instance of this SCC.
		*/
	if (child_scc_id->cycle_check->inst != 0)
	{
		return child_scc_id->cycle_check->inst;
	}

	child = (MR_SCCInstance *)
		MR_malloc(sizeof(MR_SCCInstance));
	child->scc = child_scc_id;
	child->scc_num = scc_num++;
	if (child_scc_id->num_fo_calls > 0)
	{
		nbytes = sizeof(MR_InterCallProfile *)
				* child_scc_id->num_fo_calls;
		child->fo_calls = (MR_InterCallProfile **)
			MR_malloc(nbytes);
		memset(child->fo_calls, 0, nbytes);

	} else
		child->fo_calls = NULL;
	if (child_scc_id->num_ho_calls > 0)
	{
		nbytes = sizeof(MR_HigherOrderCallProfile *)
				* child_scc_id->num_ho_calls;
		child->ho_calls = (MR_HigherOrderCallProfile **)
			MR_malloc(nbytes);
		memset(child->ho_calls, 0, nbytes);
	} else
		child->ho_calls = NULL;
	if (child_scc_id->num_cm_calls > 0)
	{
		nbytes = sizeof(MR_ClassMethodCallProfile *)
				* child_scc_id->num_cm_calls;
		child->cm_calls = (MR_ClassMethodCallProfile **)
			MR_malloc(nbytes);
		memset(child->cm_calls, 0, nbytes);
	} else
		child->cm_calls = NULL;
	child->callbacks = NULL;
	child->marked = 0;

		/*
		** Set the root to point to this child.
		*/
	child_scc_id->cycle_check->inst = child;

	return child;
}

void
MR_prof_set_current_proc(MR_SCCInstance *inst)
{
	((MR_InterCallProfile *) MR_prof_current_proc)->child = inst;
}
#endif /* MR_PROFILE_CALLS */

/* ======================================================================== */

#ifdef MR_PROFILE_DEEP

/*
**	prof_time_profile:
**		Signal handler to be called whenever a profiling signal is
**		received. Saves the current code address into a hash table.
**		If the address already exists, it increments its count.
**	XXX
*/

void
prof_deep_time_profile(int signum);

void
prof_deep_time_profile(int signum)
{
	MR_prof_num_sigs++;
	MR_prof_current_proc->quanta++;

	return;
} /* end prof_time_profile() */

#endif /* MR_PROFILE_DEEP */

/* ======================================================================== */

#ifdef MR_PROFILE_DEEP

static MR_SCCInstance *instance_stack[1000];
static int isp=0;

#define MR_PPID_TABLE_SIZE	5021

typedef struct MR_PPID_NODE	{
	const	MR_Stack_Layout_Proc_Id	*ppid;
	int				ppid_num;
	struct	MR_PPID_NODE		*next;
} MR_PPIdNode;

static MR_PPIdNode	*MR_prof_ppid_table[MR_PPID_TABLE_SIZE]; 
static MR_prof_ppid_counter = 1;

typedef struct MR_SCCID_NODE	{
	const	MR_SCCId		*SCCid;
	int				SCCid_num;
	struct	MR_SCCID_NODE		*next;
} MR_SCCIdNode;

static MR_SCCIdNode	*MR_prof_SCCid_table[MR_PPID_TABLE_SIZE]; 
static MR_prof_SCCid_counter = 1;

static void
MR_prof_dump_prof_tree(FILE *fp, MR_SCCInstance *root)
{
	int kind;
	const MR_SCCId	*id;
	MR_SCCInstance *scc;
	
	isp = 0;
	instance_stack[isp++] = root;

	while (isp > 0)
	{
		scc = instance_stack[--isp];
		if (scc->marked)
			continue;
		scc->marked = 1;
		id = scc->scc;
		if (id->num_cm_calls != 0)
			kind = 3;
		else if (id->num_ho_calls != 0)
			kind = 2;
		else
			kind = 1;
		MR_prof_write_word(fp, kind);
		MR_prof_write_word(fp, scc->scc_num);
		MR_prof_dump_SCCid(fp, id);
		MR_prof_dump_fo_calls(fp, id->num_fo_calls, scc->scc_num,
			scc->scc, scc->fo_calls, id->fo_calls);
		if (kind > 1)
			MR_prof_dump_ho_calls(fp, id->num_ho_calls,
				scc->scc_num, scc->scc, scc->ho_calls,
				id->ho_calls);
		if (kind > 2)
			MR_prof_dump_cm_calls(fp, id->num_cm_calls,
				scc->scc_num, scc->scc, scc->cm_calls,
				id->cm_calls);
		MR_prof_dump_callbacks(fp, scc->scc_num, scc->scc,
			scc->callbacks);
	}
}

static void
MR_prof_dump_fo_calls(FILE *fp, int n, int scc_num, const MR_SCCId *SCCid,
			MR_InterCallProfile **profs, const MR_CallSite **sites)
{
	int i, child_num, count;

	for (count = 0, i = 0; i < n ; i++)
	{
		if (profs[i] != NULL)
			count++;
	}

	MR_prof_write_word(fp, count); /* end marker */

	for (i = 0; i < n ; i++)
	{
		if (profs[i] != NULL)
		{
			if (profs[i]->child != NULL)
			{
				child_num = profs[i]->child->scc_num;
				instance_stack[isp++] = profs[i]->child;
			} else
				child_num = 0;
			MR_prof_write_word(fp, i);
			MR_prof_write_word(fp, child_num);
			MR_prof_dump_proc_call_profile(fp, &(profs[i]->prof));
		}
	}
}

static void MR_prof_dump_proc_call_profile(FILE *fp, MR_ProcCallProfile *p)
{
	MR_prof_write_word(fp, p->calls);
	MR_prof_write_word(fp, p->successes);
	MR_prof_write_word(fp, p->failures);
	MR_prof_write_word(fp, p->quanta);
}

static void MR_prof_dump_string(FILE *fp, const char *s)
{
	int i,l;
	l = strlen(s);
	MR_prof_write_word(fp, l);
	for(i = 0; i < l ; i++)
		MR_prof_write_word(fp, s[i]);
}

static void MR_prof_dump_ho_calls(FILE *fp, int n, int scc_num,
		const MR_SCCId *SCCid, MR_HigherOrderCallProfile **profs,
		const MR_CallSite **sites)
{
	int i, child_num;
	MR_HigherOrderCallProfile *tmp;

	for (i = 0; i < n ; i++)
	{
		
		if (profs[i])
		{
			MR_prof_write_word(fp, i + 1);
					/* add 1 so we can use 0 as `end' */
			tmp = profs[i];
			while (tmp)
			{
				if (tmp->child != NULL)
				{
					child_num = tmp->child->scc_num;
					instance_stack[isp++] = tmp->child;
				} else
					child_num = 0;
				MR_prof_dump_ppid(fp, tmp->proc_id);
				MR_prof_write_word(fp, child_num);
				MR_prof_dump_proc_call_profile(fp,
						&(tmp->prof));
				tmp = tmp->next;
			}
			MR_prof_write_word(fp, 0); /* end of list */
		}
	}
	MR_prof_write_word(fp, 0); /* end of list */
}

static void MR_prof_dump_cm_calls(FILE *fp, int n, int scc_num,
		const MR_SCCId *scc, MR_ClassMethodCallProfile **profs,
		const MR_CallSite **sites)
{
	MR_prof_write_word(fp, 0); /* end marker */
}

static void MR_prof_dump_callbacks(FILE *fp, int scc_num, const MR_SCCId *SCCid,
		MR_CallBackCallProfile *cback)
{
	int child_num;

	while (cback != NULL)
	{
		/* MR_prof_dump_ppid(fp, (int) NULL); mercury caller */
		MR_prof_dump_ppid(fp, cback->proc_id);
		if (cback->child != NULL)
		{
			child_num = cback->child->scc_num;
			instance_stack[isp++] = cback->child;
		} else {
			child_num = 0;
		}
		MR_prof_write_word(fp, child_num);
		MR_prof_dump_proc_call_profile(fp, &(cback->prof));
		cback = cback->next;
	}
	MR_prof_write_word(fp, 0); /* end marker */
}

static void MR_prof_dump_call_data(FILE *fp, const char *prefix, int num,
		const MR_Stack_Layout_Entry *caller,
		const MR_Stack_Layout_Entry *callee, 
		MR_ProcCallProfile *prof, int child)
{

	MR_prof_write_word(fp, num);
	MR_prof_dump_ppid(fp, &(caller->MR_sle_proc_id));
	MR_prof_dump_ppid(fp, &(callee->MR_sle_proc_id));
	MR_prof_write_word(fp, prof->calls);
	MR_prof_write_word(fp, prof->successes);
	MR_prof_write_word(fp, prof->failures);
	MR_prof_write_word(fp, prof->quanta);
	MR_prof_write_word(fp, child);
}

static void MR_prof_dump_ppid(FILE *fp, const MR_Stack_Layout_Proc_Id *ppid)
{
	int num;
	unsigned ind;
	MR_PPIdNode *tmp;

	if (ppid)
	{
		ind = (((const unsigned) ppid) >> 3) % MR_PPID_TABLE_SIZE;
		tmp = MR_prof_ppid_table[ind];
		num = -1;
		while (tmp)
		{
			if (ppid == tmp->ppid)
			{
				num = tmp->ppid_num;
				break;
			} else {
				tmp = tmp->next;
			}
		}
		if (num < 0)
		{
			tmp = (MR_PPIdNode *)
					MR_malloc(sizeof(MR_PPIdNode));
			tmp->ppid = ppid;
			tmp->ppid_num = MR_prof_ppid_counter++;
			tmp->next = MR_prof_ppid_table[ind];
			MR_prof_ppid_table[ind] = tmp;
			num = tmp->ppid_num;
		}
	} else {
		num = 0;
	}
	MR_prof_write_word(fp, num);
}

static void MR_prof_dump_ppid_table(FILE *fp)
{
	int i;
	MR_PPIdNode *tmp;

	for (i = 0; i < MR_PPID_TABLE_SIZE; i++)
	{
		tmp = MR_prof_ppid_table[i];
		while (tmp)
		{
			MR_prof_dump_ppid_defn(fp, tmp->ppid_num, tmp->ppid);
			tmp = tmp->next;
		}
	}
	MR_prof_write_word(fp, 0); /* end marker */
}

static void MR_prof_dump_ppid_defn(FILE *fp, int ppid_num,
		const MR_Stack_Layout_Proc_Id *ppid)
{
	if (ppid->MR_proc_user.MR_user_pred_or_func <= MR_FUNCTION) {
		/* User defined pred or func */
		if (ppid->MR_proc_user.MR_user_pred_or_func == MR_PREDICATE)
			MR_prof_write_word(fp, 1);
		else
			MR_prof_write_word(fp, 2);
		MR_prof_write_word(fp, ppid_num);
		MR_prof_dump_string(fp, ppid->MR_proc_user.MR_user_decl_module);
		MR_prof_dump_string(fp, ppid->MR_proc_user.MR_user_name);
		MR_prof_write_word(fp, ppid->MR_proc_user.MR_user_arity);
		MR_prof_write_word(fp, ppid->MR_proc_user.MR_user_mode);
	} else {
		/* Compiler generated pred */
		MR_prof_write_word(fp, 3);
		MR_prof_write_word(fp, ppid_num);
		MR_prof_dump_string(fp, ppid->MR_proc_comp.MR_comp_type_name);
		MR_prof_dump_string(fp, ppid->MR_proc_comp.MR_comp_type_module);
		MR_prof_dump_string(fp, ppid->MR_proc_comp.MR_comp_def_module);
		MR_prof_dump_string(fp, ppid->MR_proc_comp.MR_comp_pred_name);
		MR_prof_write_word(fp, ppid->MR_proc_comp.MR_comp_arity);
		MR_prof_write_word(fp, ppid->MR_proc_comp.MR_comp_mode);
	}
}

static void MR_prof_dump_SCCid(FILE *fp, const MR_SCCId *SCCid)
{
	int ind, num;
	MR_SCCIdNode *tmp;

	if (SCCid)
	{
		ind = (((const int) SCCid) >> 3) % MR_PPID_TABLE_SIZE;
		tmp = MR_prof_SCCid_table[ind];
		num = -1;
		while (tmp)
		{
			if (SCCid == tmp->SCCid)
			{
				num = tmp->SCCid_num;
				break;
			} else {
				tmp = tmp->next;
			}
		}
		if (num < 0)
		{
			tmp = (MR_SCCIdNode *)
					MR_malloc(sizeof(MR_SCCIdNode));
			tmp->SCCid = SCCid;
			tmp->SCCid_num = MR_prof_SCCid_counter++;
			tmp->next = MR_prof_SCCid_table[ind];
			MR_prof_SCCid_table[ind] = tmp;
			num = tmp->SCCid_num;
		}
	} else {
		num = 0;
	}
	MR_prof_write_word(fp, num);
}

static void MR_prof_dump_SCCid_table(FILE *fp)
{
	int i,j;
	MR_SCCIdNode *tmp;

	for (i = 0; i < MR_PPID_TABLE_SIZE; i++)
	{
		tmp = MR_prof_SCCid_table[i];
		while (tmp)
		{
			assert(tmp->SCCid_num != 0);
			MR_prof_write_word(fp, tmp->SCCid_num);
			MR_prof_output_call_site_list(fp,
				tmp->SCCid->num_fo_calls,
				tmp->SCCid->fo_calls);
			MR_prof_output_call_site_list(fp,
				tmp->SCCid->num_ho_calls,
				tmp->SCCid->ho_calls);
			/*
			MR_prof_output_call_site_list(fp,
				tmp->SCCid->num_cm_calls,
				tmp->SCCid->cm_calls);
			*/
			tmp = tmp->next;
		}
	}
	MR_prof_write_word(fp, 0); /* end marker */
}

static void
MR_prof_output_call_site_list(FILE *fp, int n, const MR_CallSite **calls)
{
	int j;

	MR_prof_write_word(fp, n);
	for (j = 0 ; j < n ; j++)
	{
		if (calls[j]->caller)
		{
			MR_prof_dump_ppid(fp, &calls[j]->caller->MR_sle_proc_id);
		} else {
			MR_prof_write_word(fp, 0);
		}
		if (calls[j]->callee)
		{
			MR_prof_dump_ppid(fp, &calls[j]->callee->MR_sle_proc_id);
		} else {
			MR_prof_write_word(fp, 0);
		}
		MR_prof_write_word(fp, calls[j]->line);
	}
}

void
MR_prof_output_deep_tables(void)
{
	FILE *fp;

	fp = checked_fopen("Prof.data", "create", "w");

	MR_prof_dump_prof_tree(fp, MR_prof_root_scc);

	checked_fclose(fp, "Prof.data");

	fp = checked_fopen("Prof.decls", "create", "w");

	MR_prof_dump_SCCid_table(fp);

	MR_prof_dump_ppid_table(fp);

	checked_fclose(fp, "Prof.decls");

}

#endif /* MR_PROFILE_DEEP */

/* ======================================================================== */

#define MR_PROF_USE_7BIT_ENCODING

#ifdef MR_PROF_USE_7BIT_ENCODING

/*
** 7bit encoding is an arbitary length encoding that uses the topmost
** bit of each byte to mark whether there are any more bits to come.
** The 7bit groups are written least significant first.
*/
void
MR_prof_write_word(FILE *fp, Word w)
{
	Word tmp;

	do
	{
		tmp = w & 0x7f;
		w = w >> 7;
		if (w != 0)
			tmp = tmp | 0x80; 
		fputc(tmp, fp);
	} while (w != 0);
}

Word
MR_prof_read_word(FILE *fp, int *eof_marker)
{
	Word w = 0;
	int c, i=0;

	while ((c = fgetc(fp)) != EOF)
	{
		w = w | ((c & 0x7f) << i);
		if (!(c & 0x80))
			break;
		i+=7;
	}

	/*
	if (i+7 > sizeof(Word))
		fatal_error("MR_prof_read_word: overflow");
	*/

	*eof_marker = (c == EOF);

	return w;
}

#elif MR_PROF_USE_MULTI_ENCODING

#else
#error No encoding specified
#endif

/* ======================================================================== */
/* ======================================================================== */
