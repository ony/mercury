/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
**	Deep profiling module
**
**	Authors: conway, zs
*/

#include "mercury_imp.h"
#include "mercury_ho_call.h"
#include "mercury_stack_layout.h"
#include "mercury_prof_time.h"
#include "mercury_deep_profiling.h"

#ifdef MR_DEEP_PROFILING

#include <stdio.h>

MR_CallSiteStatic	MR_main_parent_call_site_statics[1] =
{
	{ MR_callback, NULL, NULL, "Mercury runtime", 0, "" }
};

MR_User_ProcStatic	MR_main_parent_proc_static =
{
	{ MR_PREDICATE, "Mercury runtime", "Mercury runtime",
	  "Mercury runtime", 0, 0 },
	"Mercury runtime",
	1,
	&MR_main_parent_call_site_statics[0],
#ifdef	MR_USE_ACTIVATION_COUNTS
	0,
#endif
	NULL
};

MR_CallSiteDynamic	*MR_main_parent_call_site_dynamics[1] =
{
	NULL
};

MR_ProcDynamic		MR_main_parent_proc_dynamic =
{
	(MR_ProcStatic *) &MR_main_parent_proc_static,
	&MR_main_parent_call_site_dynamics[0]
};

MR_CallSiteDynamic	MR_main_grandparent_call_site_dynamic =
{
	&MR_main_parent_proc_dynamic,
	{
#ifdef	MR_DEEP_PROFILING_CALL_COUNTS
	0, 0, 0, 0,
#endif
#ifdef	MR_DEEP_PROFILING_TIMING
	0,
#endif
#ifdef	MR_DEEP_PROFILING_MEMORY
	0, 0
#endif
	},
	0
};

MR_CallSiteDynamic	*MR_current_call_site_dynamic =
				&MR_main_grandparent_call_site_dynamic;
MR_CallSiteDynamic	*MR_next_call_site_dynamic = NULL;
MR_CallSiteDynList	**MR_current_callback_site =
				(MR_CallSiteDynList **)
				&MR_main_parent_call_site_dynamics[0];
bool	 		MR_inside_deep_profiling_code = FALSE;
unsigned long	 	MR_quanta_inside_deep_profiling_code = 0L;
unsigned long	 	MR_quanta_outside_deep_profiling_code = 0L;

#ifdef	MR_DEEP_PROFILING_STATISTICS

int	MR_number_of_profiling_entries = 0;
int	MR_number_of_activation_loads = 0;
int	MR_amount_of_memory = 0;
int	MR_profiling_tree_memory = 0;
int	MR_dictionary_search_lengths[MR_MAX_CLOSURE_LIST_LENGTH];
int	MR_closure_search_lengths[MR_MAX_CLOSURE_LIST_LENGTH];

#endif	/* MR_DEEP_PROFILING_STATISTICS */

void
MR_deep_assert_failed(const char *cond, const char *filename, int linenumber)
{
	char	buf[1024];

	sprintf(buf, "Deep profiling assertion failed, %s:%d\n%s\n",
		filename, linenumber, cond);
	MR_fatal_error(buf);
}

void
MR_setup_callback(void *entry)
{
	MR_CallSiteDynList	*csd_list;
	MR_CallSiteDynamic	*csd;

	MR_enter_instrumentation();
	csd_list = *MR_current_callback_site;
	while (csd_list != NULL)
	{
		if (csd_list->MR_csdlist_key == entry) {
			MR_next_call_site_dynamic =
				csd_list->MR_csdlist_call_site;
			MR_leave_instrumentation();
			return;
		}

		csd_list = csd_list->MR_csdlist_next;
	}

	MR_new_call_site_dynamic(csd);

	csd_list = MR_PROFILING_MALLOC(MR_CallSiteDynList);
	csd_list->MR_csdlist_key = entry;
	csd_list->MR_csdlist_call_site = csd;
	csd_list->MR_csdlist_next = *MR_current_callback_site;
	*MR_current_callback_site = csd_list;

	MR_next_call_site_dynamic = csd;
	MR_leave_instrumentation();
}

#ifdef MR_DEEP_PROFILING_STATISTICS

int	MR_deep_prof_search_len;

void
MR_deep_profile_update_special_history(MR_TypeCtorInfo type_ctor_info)
{
	MR_dictionary_search_lengths[MR_deep_prof_search_len]++;
}

void
MR_deep_profile_update_closure_history(MR_Closure *closure)
{
	MR_closure_search_lengths[MR_deep_prof_search_len]++;
}

#endif	/* MR_DEEP_PROFILING_STATISTICS */

/*----------------------------------------------------------------------------*/

/*
** Functions for writing out the data at the end of the execution.
*/

static	void	MR_write_out_call_site_static(FILE *fp,
			const MR_CallSiteStatic *ptr);
static	void	MR_write_out_call_site_dynamic(FILE *fp,
			const MR_CallSiteDynamic *ptr);

static	void	MR_write_out_proc_dynamic(FILE *fp, const MR_ProcDynamic *ptr);
static	void	MR_write_out_ho_call_site_ptrs(FILE *fp,
			const MR_ProcDynamic *ptr,
			const MR_CallSiteDynList *dynlist);
static	void	MR_write_out_ho_call_site_nodes(FILE *fp,
			MR_CallSiteDynList *dynlist);

/*
static	void	MR_write_out_proc_layout(FILE *fp,
			const MR_Proc_Layout *layout);
*/

typedef enum node_kind {
	kind_csd, kind_pd, kind_css, kind_ps
} MR_NodeKind;

static	void	MR_write_csd_ptr(FILE *fp, const MR_CallSiteDynamic *ptr);
static	void	MR_write_ptr(FILE *fp, MR_NodeKind kind, const int node_id);
static	void	MR_write_kind(FILE *fp, MR_CallSite_Kind kind);
static	void	MR_write_byte(FILE *fp, const char byte);
static	void	MR_write_num(FILE *fp, unsigned long num);
static	void	MR_write_string(FILE *fp, const char *ptr);

/*----------------------------------------------------------------------------*/
/*
** We need a couple of hash tables, so here are some structures for handling
** them....
*/
typedef struct MR_Profiling_Hash_Node_Struct {
	const void				*item;
	int					id;
	bool					written;
	struct MR_Profiling_Hash_Node_Struct	*next;
} MR_ProfilingHashNode;

typedef struct {
	int			last_id;
	int			length;
	MR_ProfilingHashNode	**nodes;
} MR_ProfilingHashTable;

static	MR_ProfilingHashTable	*MR_create_hash_table(int size);
static	bool			MR_hash_table_insert(
					MR_ProfilingHashTable *table,
					const void *ptr,
					int *id, bool *already_written,
					bool init_written);
static	void			MR_hash_table_flag_written(
					MR_ProfilingHashTable *table,
					const void *ptr);

static	MR_ProfilingHashTable	*MR_call_site_dynamic_table;
static	MR_ProfilingHashTable	*MR_call_site_static_table;
static	MR_ProfilingHashTable	*MR_proc_dynamic_table;
static	MR_ProfilingHashTable	*MR_proc_static_table;

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

/*
** A convenient prime for the size of the node hash tables.
** The compiler contains nearly 10,000 preds, so a width of 10007
** (requiring about 40K of storage - not onerous compared to the
** size of the tree) will yield chain lengths of about 1 for the
** MR_needed_proc_statics table. For the MR_seen_nodes table, which
** stores all the MR_ProcDynamic nodes that have been seen, the average
** chain length will be longer - a typical run of the compiler can have
** as many as 50,000 nodes, so we don't want the table any narrower than this.
*/

static	const int	MR_hash_table_size = 10007;

#ifdef	MR_DEEP_PROFILING_DEBUG
static	FILE		*debug_fp;
#endif

void
MR_write_out_profiling_tree(FILE *fp)
{
	int			i;
	MR_ProfilingHashNode	*n;
	MR_Proc_Id		*pid;
	int			root_pd_id;

#ifdef	MR_DEEP_PROFILING_DEBUG
	debug_fp = fopen("Deep.debug", "w");
	if (debug_fp == NULL) {
		debug_fp = stderr;
	}
#endif

	MR_write_num(fp, MR_quanta_inside_deep_profiling_code);
	MR_write_num(fp, MR_quanta_outside_deep_profiling_code);

	MR_call_site_dynamic_table = MR_create_hash_table(MR_hash_table_size);
	MR_call_site_static_table  = MR_create_hash_table(MR_hash_table_size);
	MR_proc_dynamic_table = MR_create_hash_table(MR_hash_table_size);
	MR_proc_static_table  = MR_create_hash_table(MR_hash_table_size);

	if (MR_hash_table_insert(MR_proc_dynamic_table,
		&MR_main_parent_proc_dynamic, &root_pd_id, NULL, FALSE))
	{
		MR_fatal_error(
			"MR_write_out_profiling_tree: root seen before");
	}

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(debug_fp, "root = %p, %d\n",
		&MR_main_parent_proc_dynamic, root_pd_id);
#endif

	MR_write_byte(fp, MR_deep_token_root);
	MR_write_ptr(fp, kind_pd, root_pd_id);

	MR_write_out_proc_dynamic(fp, &MR_main_parent_proc_dynamic);

	MR_write_out_proc_static(fp,
		(MR_ProcStatic *) &MR_main_parent_proc_static);
	MR_deep_assert(MR_address_of_write_out_proc_statics != NULL);
	(*MR_address_of_write_out_proc_statics)(fp);

#ifdef MR_DEEP_PROFILING_STATISTICS
	if (! MR_print_deep_profiling_statistics) {
		return;
	}

	fprintf(stderr, "Amount of memory accounted for: %d\n",
		MR_amount_of_memory);
	fprintf(stderr, "There were %d activation increments\n",
		MR_number_of_profiling_entries);
	fprintf(stderr, "There were %d outermost_activation_ptr uses\n",
		MR_number_of_activation_loads);
	fprintf(stderr, "Closure/TypeInfo search length histogram:\n");

	for (i = 0; i < MR_MAX_CLOSURE_LIST_LENGTH; i++) {
		fprintf(stderr, "\t%3d : %12d %12d\n", i,
			MR_closure_search_lengths[i],
			MR_dictionary_search_lengths[i]);
	}
#endif
}

void
MR_write_out_proc_static(FILE *fp, const MR_ProcStatic *ptr)
{
	int	ps_id;
	int	css_id;
	bool	already_written;
	int	i;

	if (ptr == NULL) {
		MR_fatal_error("MR_write_out_proc_static: null ps");
	}

	(void) MR_hash_table_insert(MR_proc_static_table, ptr,
		&ps_id, &already_written, TRUE);

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(debug_fp, "proc_static %p/%d\n", ptr, ps_id);
	fprintf(debug_fp, "  filename \"%s\", %d call sites\n",
		ptr->MR_ps_file_name, ptr->MR_ps_num_call_sites);
#endif

	if (already_written) {
		MR_fatal_error("MR_write_out_proc_static: seen ps");
	}

	MR_hash_table_flag_written(MR_proc_static_table, ptr);

	MR_write_byte(fp, MR_deep_token_proc_static);
	MR_write_ptr(fp, kind_ps, ps_id);

	if (MR_PROC_ID_COMPILER_GENERATED(ptr->MR_ps_proc_id)) {
#ifdef MR_DEEP_PROFILING_DEBUG
		fprintf(debug_fp, "  compiler %s/%s/%s/%s/%d/%d\n",
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_type_name,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_type_module,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_def_module,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_pred_name,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_arity,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_mode);
#endif

		MR_write_byte(fp, MR_deep_token_isa_compiler_generated);
		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_type_name);
		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_type_module);
		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_def_module);
		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_pred_name);
		MR_write_num(fp,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_arity);
		MR_write_num(fp,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_mode);
	} else {
#ifdef MR_DEEP_PROFILING_DEBUG
		fprintf(debug_fp, "  user %d/%s/%s/%s/%d/%d\n",
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_pred_or_func,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_decl_module,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_def_module,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_name,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_arity,
			ptr->MR_ps_proc_id.MR_proc_comp.MR_comp_mode);
#endif

		if (ptr->MR_ps_proc_id.MR_proc_user.MR_user_pred_or_func
			== MR_PREDICATE)
		{
			MR_write_byte(fp, MR_deep_token_isa_predicate);
		} else {
			MR_write_byte(fp, MR_deep_token_isa_function);
		}

		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_decl_module);
		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_def_module);
		MR_write_string(fp,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_name);
		MR_write_num(fp,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_arity);
		MR_write_num(fp,
			ptr->MR_ps_proc_id.MR_proc_user.MR_user_mode);
	}

	MR_write_string(fp, ptr->MR_ps_file_name);
	MR_write_num(fp, ptr->MR_ps_num_call_sites);

	for (i = 0; i < ptr->MR_ps_num_call_sites; i++) {
		(void) MR_hash_table_insert(MR_call_site_static_table,
			&ptr->MR_ps_call_sites[i], &css_id, NULL, FALSE);

#ifdef MR_DEEP_PROFILING_DEBUG
		fprintf(debug_fp,
			"call site id %d in proc_static %p/%d -> %d\n",
			i, ptr, ps_id, css_id);
#endif

		MR_write_ptr(fp, kind_css, css_id);
	}

	for (i = 0; i < ptr->MR_ps_num_call_sites; i++) {
#ifdef MR_DEEP_PROFILING_DEBUG
		fprintf(debug_fp, "in proc_static %p/%d, call site %d\n",
			ptr, ps_id, i);
#endif

		MR_write_out_call_site_static(fp, &ptr->MR_ps_call_sites[i]);
	}
}

static void
MR_write_out_call_site_static(FILE *fp, const MR_CallSiteStatic *ptr)
{
	int	css_id;
	int	ps_id;
	bool	already_written;

	if (ptr == NULL) {
		MR_fatal_error("MR_write_out_call_site_static: null css");
	}

	(void) MR_hash_table_insert(MR_call_site_static_table, ptr,
		&css_id, &already_written, TRUE);

	if (already_written) {
		MR_fatal_error("MR_write_out_call_site_static: seen css");
	}

	MR_hash_table_flag_written(MR_call_site_static_table, ptr);

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(debug_fp, "call_site_static %p/%d\n", ptr, css_id);
	fprintf(debug_fp,
		"  filename \"%s\", linenum %d, goal path %s, kind %d\n",
		ptr->MR_css_file_name, ptr->MR_css_line_number,
		ptr->MR_css_goal_path, ptr->MR_css_kind);
#endif

	MR_write_byte(fp, MR_deep_token_call_site_static);
	MR_write_ptr(fp, kind_css, css_id);
	MR_write_kind(fp, ptr->MR_css_kind);
	if (ptr->MR_css_kind == MR_normal_call) {
		(void) MR_hash_table_insert(MR_proc_static_table,
			ptr->MR_css_callee_ptr_if_known, &ps_id, NULL, FALSE);
#ifdef MR_DEEP_PROFILING_DEBUG
		fprintf(debug_fp, "  callee %p/%d\n",
			ptr->MR_css_callee_ptr_if_known, ps_id);
#endif
		MR_write_num(fp, ps_id);
		if (ptr->MR_css_type_subst_if_known != NULL) {
			MR_write_string(fp,
				ptr->MR_css_type_subst_if_known);
		} else {
			MR_write_string(fp, "");
		}
	}
	/* XXX MR_css_file_name */
	MR_write_num(fp, ptr->MR_css_line_number);
	MR_write_string(fp, ptr->MR_css_goal_path);
}

static void
MR_write_out_call_site_dynamic(FILE *fp, const MR_CallSiteDynamic *ptr)
{
	int	bitmask = 0;
	int	csd_id;
	int	pd_id;

	if (ptr == NULL) {
		return;
	}

#ifdef MR_DEEP_PROFILING_STATISTICS
	MR_amount_of_memory += sizeof(MR_CallSiteDynamic);
#endif

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(debug_fp, "call_site_dynamic %p: callee proc_dynamic %p\n",
		ptr, ptr->MR_csd_callee_ptr);
#endif

	MR_write_byte(fp, MR_deep_token_call_site_dynamic);
	if (! MR_hash_table_insert(MR_call_site_dynamic_table, ptr,
		&csd_id, NULL, TRUE))
	{
		MR_fatal_error(
			"MR_write_out_call_site_dynamic: insert succeeded");
	}

	MR_write_ptr(fp, kind_csd, csd_id);
	if (ptr->MR_csd_callee_ptr == NULL) {
		pd_id = 0;
	} else {
		(void) MR_hash_table_insert(MR_proc_dynamic_table,
			ptr->MR_csd_callee_ptr, &pd_id, NULL, FALSE);
	}

	MR_write_ptr(fp, kind_pd, pd_id);

#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	if (ptr->MR_csd_own.MR_own_calls != 0)
		bitmask |= 0x0001;
	if (ptr->MR_csd_own.MR_own_exits != 0)
		bitmask |= 0x0002;
	if (ptr->MR_csd_own.MR_own_fails != 0)
		bitmask |= 0x0004;
	if (ptr->MR_csd_own.MR_own_redos != 0)
		bitmask |= 0x0008;
#endif
#ifdef MR_DEEP_PROFILING_TIMING
	if (ptr->MR_csd_own.MR_own_quanta != 0)
		bitmask |= 0x0010;
#endif
#ifdef MR_DEEP_PROFILING_MEMORY
	if (ptr->MR_csd_own.MR_own_allocs != 0)
		bitmask |= 0x0020;
	if (ptr->MR_csd_own.MR_own_words != 0)
		bitmask |= 0x0040;
#endif

	MR_write_num(fp, bitmask);

#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	if (ptr->MR_csd_own.MR_own_calls != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_calls);
	if (ptr->MR_csd_own.MR_own_exits != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_exits);
	if (ptr->MR_csd_own.MR_own_fails != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_fails);
	if (ptr->MR_csd_own.MR_own_redos != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_redos);
#endif

#ifdef MR_DEEP_PROFILING_TIMING
	if (ptr->MR_csd_own.MR_own_quanta != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_quanta);
#endif

#ifdef MR_DEEP_PROFILING_MEMORY
	if (ptr->MR_csd_own.MR_own_allocs != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_allocs);
	if (ptr->MR_csd_own.MR_own_words != 0)
		MR_write_num(fp, ptr->MR_csd_own.MR_own_words);
#endif

	MR_write_out_proc_dynamic(fp, ptr->MR_csd_callee_ptr);
}

static void
MR_write_out_proc_dynamic(FILE *fp, const MR_ProcDynamic *ptr)
{
	int	i;
	int	pd_id;
	int	ps_id;
	bool	already_written;

	/*
	** This shouldn't really happen except that we don't have correct
	** handling of nondet pragma_foreign_code yet.
	*/

	if (ptr == NULL) {
		return;
	}

	if (! MR_hash_table_insert(MR_proc_dynamic_table, ptr,
		&pd_id, &already_written, TRUE))
	{
		MR_fatal_error("MR_write_out_proc_dynamic: unseen pd");
	}

	if (already_written) {
		return;
	}

	MR_hash_table_flag_written(MR_proc_dynamic_table, ptr);
	(void) MR_hash_table_insert(MR_proc_static_table,
		ptr->MR_pd_proc_static, &ps_id, NULL, FALSE);

#ifdef MR_DEEP_PROFILING_STATISTICS
	MR_amount_of_memory += sizeof(MR_ProcDynamic);
	MR_amount_of_memory += sizeof(MR_CallSiteDynamic*) *
		ptr->MR_pd_proc_static->MR_ps_num_call_sites;
#endif

	MR_write_byte(fp, MR_deep_token_proc_dynamic);
	MR_write_ptr(fp, kind_pd, pd_id);
	MR_write_ptr(fp, kind_ps, ps_id);
	MR_write_num(fp, ptr->MR_pd_proc_static->MR_ps_num_call_sites);

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(debug_fp, "proc_dynamic %p/%d, proc_static %p/%d\n",
		ptr, pd_id, ptr->MR_pd_proc_static, ps_id);
#endif

	for (i = 0; i < ptr->MR_pd_proc_static->MR_ps_num_call_sites; i++) {
		MR_write_kind(fp, ptr->MR_pd_proc_static->
			MR_ps_call_sites[i].MR_css_kind);
		switch (ptr->MR_pd_proc_static->
			MR_ps_call_sites[i].MR_css_kind)
		{
			case MR_normal_call:
#ifdef MR_DEEP_PROFILING_DEBUG
				fprintf(debug_fp, "  normal call from pd %p to pd %p\n",
					ptr, ptr->MR_pd_call_site_ptr_ptrs[i]);
#endif
				MR_write_csd_ptr(fp,
					ptr->MR_pd_call_site_ptr_ptrs[i]);
				break;

			case MR_special_call:
			case MR_higher_order_call:
			case MR_method_call:
			case MR_callback:
				MR_write_out_ho_call_site_ptrs(fp, ptr,
					(MR_CallSiteDynList *)
					ptr->MR_pd_call_site_ptr_ptrs[i]);
				break;
		}
	}

	for (i = 0; i < ptr->MR_pd_proc_static->MR_ps_num_call_sites; i++) {
		switch (ptr->MR_pd_proc_static->
				MR_ps_call_sites[i].MR_css_kind)
		{
			case MR_normal_call:
				MR_write_out_call_site_dynamic(fp,
					ptr->MR_pd_call_site_ptr_ptrs[i]);
				break;

			case MR_special_call:
			case MR_higher_order_call:
			case MR_method_call:
			case MR_callback:
				MR_write_out_ho_call_site_nodes(fp,
					(MR_CallSiteDynList *)
					ptr->MR_pd_call_site_ptr_ptrs[i]);
				break;
		}
	}
}

static void
MR_write_out_ho_call_site_ptrs(FILE *fp, const MR_ProcDynamic *ptr,
	const MR_CallSiteDynList *dynlist)
{
	while (dynlist != NULL) {
#ifdef MR_DEEP_PROFILING_STATISTICS
		MR_amount_of_memory += sizeof(MR_CallSiteDynList);
#endif
#ifdef MR_DEEP_PROFILING_DEBUG
		fprintf(debug_fp, "  multi call from pd %p to pd %p\n",
			ptr, dynlist->MR_csdlist_call_site);
#endif
		MR_write_csd_ptr(fp, dynlist->MR_csdlist_call_site);
		dynlist = dynlist->MR_csdlist_next;
	}
	MR_write_byte(fp, MR_deep_token_end);
}

static void
MR_write_out_ho_call_site_nodes(FILE *fp, MR_CallSiteDynList *dynlist)
{
	while (dynlist != NULL) {
		MR_write_out_call_site_dynamic(fp,
			dynlist->MR_csdlist_call_site);
		dynlist = dynlist->MR_csdlist_next;
	}
}

static void
MR_write_csd_ptr(FILE *fp, const MR_CallSiteDynamic *ptr)
{
	int	csd_id;

	if (ptr == NULL) {
		csd_id = 0;
	} else {
		(void) MR_hash_table_insert(MR_call_site_dynamic_table, ptr,
			&csd_id, NULL, FALSE);
	}

	MR_write_ptr(fp, kind_csd, csd_id);
}

static void
MR_write_ptr(FILE *fp, MR_NodeKind kind, int node_id)
{
#ifdef	MR_DEEP_PROFILING_DETAIL_DEBUG
	fprintf(debug_fp, "ptr: %d\n", node_id);
#endif

	/* MR_write_byte(fp, (int) kind); */
	MR_write_num(fp, node_id);
}

static void
MR_write_kind(FILE *fp, MR_CallSite_Kind kind)
{
	int	byte;

#ifdef	MR_DEEP_PROFILING_DETAIL_DEBUG
	fprintf(debug_fp, "call_site_kind: %d\n", (int) kind);
#endif

	/* convert from a MR_CallSite_Kind to an MR_Profiling_Encoding_Token */
	byte = (int) kind +
		((int) MR_deep_token_normal_call - (int) MR_normal_call);
	if (byte < MR_deep_token_normal_call || byte > MR_deep_token_callback)
	{
		MR_fatal_error("MR_write_kind: bad kind %d %d\n",
			(int) kind, byte);
	}

	MR_write_byte(fp, byte);
}

static void
MR_write_byte(FILE *fp, const char byte)
{
#ifdef	MR_DEEP_PROFILING_DETAIL_DEBUG
	fprintf(debug_fp, "byte: %d\n", (int) byte);
#endif
	fputc(byte, fp);
}

static void
MR_write_num(FILE *fp, unsigned long num)
{
	unsigned char	pieces[sizeof(unsigned long) * 8 / 7 + 1];
	int		i;

#ifdef	MR_DEEP_PROFILING_DETAIL_DEBUG
	fprintf(debug_fp, "num: %ld\n", num);
#endif

	MR_deep_assert((int) num >= 0);

	i = 0;
	do {
		pieces[i] = num & 0x7f;
		num = num >> 7;
		i++;
	} while (num != 0);

	i--;

	while (i > 0) {
		fputc(pieces[i--] | 0x80, fp);
	}
	fputc(pieces[0], fp);
}

static void
MR_write_string(FILE *fp, const char *ptr)
{
	int	i, len;

#ifdef	MR_DEEP_PROFILING_DETAIL_DEBUG
	fprintf(debug_fp, "string: <%s>\n", ptr);
#endif

	len = strlen(ptr);
	MR_write_num(fp, len);
	for (i = 0; i < len; i++) {
		fputc(ptr[i], fp);
	}
}

/*----------------------------------------------------------------------------*/

static MR_ProfilingHashTable *
MR_create_hash_table(int size)
{
	MR_ProfilingHashTable *ptr;
	ptr = MR_NEW(MR_ProfilingHashTable);
	ptr->length = size;
	ptr->last_id = 0;
	ptr->nodes = MR_NEW_ARRAY(MR_ProfilingHashNode *, size);

	return ptr;
}

static bool
MR_hash_table_insert(MR_ProfilingHashTable *table, const void *ptr,
	int *id, bool *already_written, bool init_written)
{
	int			hash;
	MR_ProfilingHashNode	*node;

	if (ptr == NULL) {
		MR_fatal_error("NULL ptr in MR_hash_table_insert");
	}

	hash = ((unsigned int) ptr >> 2) % table->length;

	node = table->nodes[hash];
	while (node != NULL) {
		if (node->item == ptr) {
			*id = node->id;
			if (already_written != NULL) {
				*already_written = node->written;
			}
			return TRUE;
		}
		node = node->next;
	}

	node = MR_NEW(MR_ProfilingHashNode);
	node->item = ptr;
	node->id = ++table->last_id;
	node->written = init_written;
	node->next = table->nodes[hash];
	table->nodes[hash] = node;

	*id = node->id;
	if (already_written != NULL) {
		*already_written = FALSE;
	}

	return FALSE;
}

static void
MR_hash_table_flag_written(MR_ProfilingHashTable *table, const void *ptr)
{
	int			hash;
	MR_ProfilingHashNode	*node;

	if (ptr == NULL) {
		MR_fatal_error("NULL ptr in MR_hash_table_flag_written");
	}

	hash = ((unsigned int) ptr >> 2) % table->length;

	node = table->nodes[hash];
	while (node != NULL) {
		if (node->item == ptr) {
			node->written = TRUE;
			return;
		}
		node = node->next;
	}

	MR_fatal_error("MR_hash_table_flag_written: did not find node");
}

void
MR_deep_prof_init(void)
{
	MR_init_time_profile_method();
}

#ifdef MR_DEEP_PROFILING_TIMING

static	void	MR_deep_tick_handler(int signum);

void
MR_deep_prof_turn_on_time_profiling(void)
{
	MR_turn_on_time_profiling(MR_deep_tick_handler);
}

void
MR_deep_prof_turn_off_time_profiling(void)
{
	MR_turn_off_time_profiling();
}

static void
MR_deep_tick_handler(/* unused */ int signum)
{
	if (MR_inside_deep_profiling_code) {
		MR_quanta_inside_deep_profiling_code++;
	} else {
		MR_quanta_outside_deep_profiling_code++;
		MR_current_call_site_dynamic->MR_csd_own.MR_own_quanta++;
	}
}

#endif /* MR_DEEP_PROFILING_TIMING */

#endif	/* MR_DEEP_PROFILING */
