/*
** Copyright (C) 1995-1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** mercury_prof.h -- definitions for profiling.
** 
** This header gives information and declarations necessary for deep
** profiling. Other places for information are runtime/mercury_prof_deep.c
** and compiler/profiling.m.
**
** Deep profiling captures a snapshot of the performance of a program by
** using SIGPROFs to estimate how much time is spent in each procedure in
** the program. Unlike mprof, deep profiling does not make the assumption
** that each call to a procedure is equal in cost. Instead, keeps an
** annotated copy of the call tree, reduced into strongly connected
** components (SCCs), which is represented using structures called
** `MR_SCCInstance's. Each MR_SCCInstance is an instance of a static SCC
** from the program. The MR_SCCInstance structure stores information about
** the number of times each procedure called in that dynamic instance of the
** corresponding static SCC was called, succeeded, failed, and the number of
** SIGPROFs that occured while we were in that procedure. Each
** MR_SCCInstance also has a pointer to a static structure MR_SCCId which
** records the static information about the call-sites in that SCC.
**
** Deep profiling works by annotating the generated code to create and
** maintain the reduced call-tree. It uses the global variable:
**	MR_prof_current_proc which points to the MR_ProcCallProfile which
**		stores the counts mentioned above for the current procedure.
**		Note that this is part of the *caller's* MR_SCCInstance, not
**		the callee's MR_SCCInstance.
*/

#ifndef MERCURY_PROF_DEEP_H
#define MERCURY_PROF_DEEP_H

#ifdef MR_PROFILE_DEEP

#include "mercury_types.h"		/* for `Word' */
#include "mercury_stack_layout.h"	/* for `MR_Stack_Layout_Entry *' */
#include "mercury_ho_call.h"		/* for `MR_Closure *' */

#define MR_IF_PROFILE_DEEP(x)	x

#define MR_DEEP_PARENTS

/*
** The SCCId structures are generated as part of the static data
** along with the stack-layout data.
*/

typedef struct MR_SCC_ID {
	const int			num_fo_calls;
	const struct MR_CALL_SITE	**fo_calls;
	const int			num_ho_calls;
	const struct MR_CALL_SITE	**ho_calls;
	const int			num_cm_calls;
	const struct MR_CALL_SITE	**cm_calls;
	struct MR_CYCLE_CHECK		*cycle_check;
} MR_SCCId;

typedef struct MR_CALL_SITE {
	const MR_Stack_Layout_Entry	*caller;
	const MR_Stack_Layout_Entry	*callee;
	const char			*file;
	const int			line;
} MR_CallSite;

typedef struct MR_CYCLE_CHECK {
	struct MR_SCC_INSTANCE	*inst;
} MR_CycleCheck;

#define MR_MAKE_SCC_ID(nm, focs, hocs, cmcs)				    \
	const MR_CallSite *MR_PASTE2(nm, _focs)[] = focs;		    \
	const MR_CallSite *MR_PASTE2(nm, _hocs)[] = hocs;		    \
	const MR_CallSite *MR_PASTE2(nm, _cmcs)[] = cmcs;		    \
	MR_CycleCheck	  MR_PASTE2(nm, _cycchk) = {			    \
		(MR_SCCInstance *) NULL					    \
	};								    \
	const MR_SCCId nm = {						    \
			sizeof(MR_PASTE2(nm, _focs))/sizeof(MR_CallSite *), \
			MR_PASTE2(nm, _focs),				    \
			sizeof(MR_PASTE2(nm, _hocs))/sizeof(MR_CallSite *), \
			MR_PASTE2(nm, _hocs),				    \
			sizeof(MR_PASTE2(nm, _cmcs))/sizeof(MR_CallSite *), \
			MR_PASTE2(nm, _cmcs),				    \
			&MR_PASTE2(nm, _cycchk)				    \
		}

#define MR_REFER_SCC_ID(l)	&mercury__scc_##l

#define MR_SCC_INST(s)		((Word)(((MR_SCCId *) (s))->cycle_check->inst))

#define MR_SET_SCC_INST(s, v)						\
	((((MR_SCCId *) (s))->cycle_check->inst) = (MR_SCCInstance *) (v))

#define MR_DECL_SLE(nm)							\
	extern const struct mercury_data__layout__##nm##_struct		\
			mercury_data__layout__##nm

#define MR_REF_SLE(nm)	(const MR_Stack_Layout_Entry *)			\
				&mercury_data__layout__##nm

#define MR_REF_SLEc(nm)	(const MR_Stack_Layout_Entry *)			\
					&mercury_data__layout__##nm,

#define MR_MAKE_CALL_SITE(nm, cer, cee, fl, li)				\
	MR_DECL_SLE(cer);						\
	MR_DECL_SLE(cee);						\
	MR_CallSite nm = { MR_REF_SLE(cer), MR_REF_SLE(cee), fl, li }

#define MR_MAKE_HO_CALL_SITE(nm, cer, fl, li)				\
	MR_DECL_SLE(cer);						\
	MR_CallSite nm = {						\
		MR_REF_SLE(cer),					\
		(const MR_Stack_Layout_Entry *) NULL,			\
		fl,							\
		li							\
	}

typedef unsigned long	MR_Count;

/*
** A MR_ProcCallProfile contains the data that we wish to record
** about call sites; ie
**	the number of calls
**	the number of times that the call succeeded
**	the number of times that the call failed
**	(#calls <= #successes + #failures)
*/
typedef struct MR_PROC_CALL_PROFILE {
	MR_Count		calls;
	MR_Count		successes;
	MR_Count		failures;
	MR_Count		quanta;
} MR_ProcCallProfile;

typedef struct MR_SCC_INSTANCE {
#ifdef MR_DEEP_PARENTS
    	struct MR_SCC_INSTANCE		*parent;
#endif
	const MR_SCCId			*scc;
	int				scc_num;
	struct MR_INTER_CALL_PROFILE	**fo_calls;
	struct MR_MULTI_CALL_PROFILE	**ho_calls;
	struct MR_MULTI_CALL_PROFILE	**cm_calls;
	struct MR_MULTI_CALL_PROFILE	*callbacks;
	char				marked;
} MR_SCCInstance;

	/*
	** For first order calls, we know the caller and the unique callee
	** at compile time, so all we need to store is the profile and a
	** pointer to the child MR_SCCInstance.
	*/
typedef struct MR_INTER_CALL_PROFILE {
	MR_ProcCallProfile	prof;
	struct MR_SCC_INSTANCE	*child;
}  MR_InterCallProfile;

	/*
	** For higher order calls (including class method calls) and
	** callbacks from C, we know the caller at compile time, but not
	** the callee. Indeed, since there may be multiple closures passed
	** to the same call site, we keep a linked list of the different
	** closures that were passed. We keep the address of the entry
	** point as an index, and a pointer to the MR_Stack_Layout_Proc_Id
	** for that procedure. We need the former, because the latter may
	** not be unique, and we need a unique key to identify the
	** procedure.
	**
	** Note that for class method calls, since the closure is dependent
	** on the type of which the typeclass is an instance, we can only
	** get multiple closures if multiple types are used. This is harder
	** than it sounds, since we're talking about dynamic instances of
	** the call-site, not the single static instance. In fact, it is only
	** possible if existentially quantified types are used.
	*/
typedef struct MR_MULTI_CALL_PROFILE {
	MR_ProcCallProfile		prof;
	struct MR_SCC_INSTANCE		*child;
	struct MR_MULTI_CALL_PROFILE	*next;
	Code				*entry;
	const MR_Stack_Layout_Proc_Id	*proc_id;
} MR_MultiCallProfile;;

typedef MR_MultiCallProfile MR_HigherOrderCallProfile;

typedef MR_MultiCallProfile MR_ClassMethodCallProfile;

typedef MR_MultiCallProfile MR_CallBackCallProfile;

void MR_prof_init_globals(MR_Stack_Layout_Entry *proclayout);

/*
** This variable holds the address of the "current" CallProfile struct
** so that when a profiling interrupt occurs, the profiler can simply
** increment the appropriate counter.
*/

extern	MR_ProcCallProfile * volatile	MR_prof_current_proc;

/*
** We only need to keep a pointer to the current MR_SCCInstance when
** we are including parent pointers in the nodes of the call graph.
** In this case it is needed so that we know where to link to.
*/
#ifdef MR_DEEP_PARENTS
extern	MR_SCCInstance	   * volatile	MR_prof_current_scc;
#endif

extern MR_InterCallProfile	MR_prof_root_proc;
extern	MR_Count		MR_prof_num_sigs;

#define	MR_intra_scc_call(new_slot)	\
		MR_prof_ensure_fo_call_slot((new_slot))

#define	MR_local_inter_scc(new_slot, scc_id)	\
		MR_prof_ensure_fo_call_inter_slot(	\
			(new_slot), (const MR_SCCId *) (scc_id))

#define MR_nonlocal_inter_scc(new_slot, playt) \
		MR_prof_ensure_fo_call_inter_slot2(	\
			(new_slot), (const MR_Stack_Layout_Entry *) (playt))

#define MR_ho_call(new_slot, closure) \
		MR_prof_ensure_ho_call_inter_slot(	\
			(new_slot), (MR_Closure *) (closure))

#define MR_special_ho_call(new_slot, cptr, playt) \
		MR_prof_ensure_special_ho_call_inter_slot(	\
			(new_slot), (Code *) (cptr), \
			(const MR_Stack_Layout_Entry *) (playt))

#define MR_prof_c_calls_mercury(playt) \
		MR_prof_ensure_c_calls_mercury(	\
			(const MR_Stack_Layout_Entry *) (playt))

/*
#define MR_scc_from_current_proc()	\
		(((MR_InterCallProfile *) MR_prof_current_proc)->child)
*/

#define MR_scc_from_here(scc_id)	\
		MR_prof_ensure_scc((const MR_SCCId *)(scc_id))

int MR_prof_check_current_scc(const Word *c);

static int MR_prof_debugging_dummy;

MR_ProcCallProfile *
	MR_prof_ensure_fo_call_slot(int site_num);

MR_ProcCallProfile *
	MR_prof_ensure_fo_call_inter_slot(int site_num,
		const MR_SCCId *child_scc);

MR_ProcCallProfile *
	MR_prof_ensure_fo_call_inter_slot2(int site_num,
		const MR_Stack_Layout_Entry *callee);

MR_ProcCallProfile *
	MR_prof_ensure_ho_call_inter_slot(int site_num,
		MR_Closure *closure);

MR_ProcCallProfile *
	MR_prof_ensure_special_ho_call_inter_slot(int site_num,
		Code *code_ptr, const MR_Stack_Layout_Entry *playt);

MR_ProcCallProfile *
	MR_prof_proc_const_call(MR_MultiCallProfile **call_list,
		MR_Closure *proc);

MR_ProcCallProfile *
	MR_prof_special_proc_const_call(MR_MultiCallProfile **call_list,
		Code *code_ptr, const MR_Stack_Layout_Proc_Id *proc);

MR_ProcCallProfile *
	MR_prof_ensure_c_calls_mercury(const MR_Stack_Layout_Entry *playt);

MR_SCCInstance *
	MR_prof_ensure_scc(const MR_SCCId *id);

void
MR_prof_set_current_proc(MR_SCCInstance *inst);

void
MR_prof_output_deep_tables(void);

#else

#define MR_MAKE_SCC_ID(x, y, z, w)

#define MR_MAKE_CALL_SITE(x, y, z, w, v)

#define MR_IF_PROFILE_DEEP(x)

#endif

void
MR_prof_write_word(FILE *fp, Word w);

Word
MR_prof_read_word(FILE *fp, int *eof_marker);

#endif	/* not MERCURY_PROF_DEEP_H */
