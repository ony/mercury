/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
**	Deep profiling module
**
**	Main Author : conway
*/
#include "mercury_imp.h"
#include "mercury_ho_call.h"
#include "mercury_stack_layout.h"
#include "mercury_deep_profiling.h"

#ifdef MR_DEEP_PROFILING

#include <stdio.h>

MR_CallSiteDynamic MR_mainCallSite = { NULL };

MR_CallSiteDynamic *MR_rootCallSites[] = {
	&MR_mainCallSite,
	NULL
};

volatile MR_CallSiteDynamic
		*MR_parent_call_site_dynamic = NULL;

#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
volatile MR_CallSiteDynamic
		*MR_next_call_site_dynamic = &MR_mainCallSite;
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
volatile MR_Bool MR_inside_deep_profiling_code = FALSE;
#endif

volatile MR_CallSiteDynamic
		*MR_current_call_site_dynamic = &MR_mainCallSite;

volatile MR_CallSiteDynamic
		**MR_current_callback_site = &(MR_rootCallSites[1]);

#ifdef MR_DEEP_PROFILING_STATISTICS
int MR_number_of_profiling_entries = 0;
int MR_number_of_activation_loads = 0;
int MR_profiling_tree_memory = 0;
int MR_dictionary_search_lengths[MR_MAX_CLOSURE_LIST_LENGTH];
int MR_dictionary_history_counter;
struct MR_DICTIONARY_SEARCH_HISTORY_STRUCT
	MR_dictionary_history[MR_HISTORY_LENGTH];
int MR_closure_search_lengths[MR_MAX_CLOSURE_LIST_LENGTH];
int MR_closure_history_counter;
struct MR_CLOSURE_SEARCH_HISTORY_STRUCT
	MR_closure_history[MR_HISTORY_LENGTH];
int MR_history_thresh = 15;

#endif

void
MR_prepare_for_callback(void *entry)
{
    MR_CallSiteDynList *tmp;
    MR_CallSiteDynamic *tmp2;

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = TRUE;
#endif

    tmp = (MR_CallSiteDynList*) *MR_current_callback_site;
    while (tmp)
    {
    	if (tmp->key == entry)
	{
	    MR_parent_call_site_dynamic = MR_current_callback_site;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
	    MR_next_call_site_dynamic = tmp->call_site;
#else
	    MR_current_call_site_dynamic = tmp->call_site;
#endif
	    return;
	}
	tmp = tmp->next;
    }
    
    tmp2 = MR_NEW(MR_CallSiteDynamic);
    tmp2->call_site_callee_ptr = NULL;

    tmp = MR_NEW(MR_CallSiteDynList);
    tmp->key = entry;
    tmp->call_site = tmp2;
    tmp->next = (MR_CallSiteDynList *) *MR_current_callback_site;
    *MR_current_callback_site = (MR_CallSiteDynamic *) tmp;

    MR_parent_call_site_dynamic = MR_current_callback_site;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
    MR_next_call_site_dynamic = tmp2;
#else
    MR_current_call_site_dynamic = tmp2;
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = FALSE;
#endif

}
/*----------------------------------------------------------------------------*/

/*
** Functions for writing out the data at the end of the execution.
*/

static	void	MR_write_out_callsite_static(FILE *fp,
			const MR_CallSiteStatic *ptr);
static	void	MR_write_out_callsite_dynamic(FILE *fp,
			const MR_CallSiteDynamic *ptr);

static	void	MR_write_out_proc_static(FILE *fp, const MR_ProcStatic *ptr);
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

#ifdef MR_DEEP_PROFILING_STATISTICS

int MR_amount_of_memory = 0;

#endif /* MR_DEEP_PROFILING_STATISTICS */

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

static const int MR_hash_table_size = 10007;

void
MR_write_out_profiling_tree(FILE *fp)
{
	int			i;
	MR_ProfilingHashNode	*n;
	MR_Proc_Id		*pid;
	int			root_node_id;

	MR_call_site_dynamic_table = MR_create_hash_table(MR_hash_table_size);
	MR_call_site_static_table  = MR_create_hash_table(MR_hash_table_size);
	MR_proc_dynamic_table = MR_create_hash_table(MR_hash_table_size);
	MR_proc_static_table  = MR_create_hash_table(MR_hash_table_size);

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(stderr, "root = %p\n", &MR_mainCallSite);
#endif
	MR_write_byte(fp, root);
	if (MR_hash_table_insert(MR_call_site_dynamic_table, &MR_mainCallSite,
		&root_node_id, NULL, FALSE))
	{
		MR_fatal_error(
			"MR_write_out_profiling_tree: root seen before");
	}

	MR_write_ptr(fp, kind_csd, root_node_id);

	MR_write_out_callsite_dynamic(fp, &MR_mainCallSite);

	for (i = 0; i < MR_proc_static_table->length; i++) {
		n = MR_proc_static_table->nodes[i];
		while (n != NULL) {
			MR_write_out_proc_static(fp,
				(const MR_ProcStatic *) n->item);
			n = n->next;
		}
	}

#ifdef MR_DEEP_PROFILING_STATISTICS
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

	fprintf(stderr, "Recent closures searched in long lists:\n");
	for (i = 0; i < MR_closure_history_counter; i++) {
		pid = &(MR_closure_history[i].closure->closure_id->proc_id);
		if (pid->MR_proc_user.MR_user_pred_or_func > MR_FUNCTION) {
			fprintf(stderr,
				"%s:%s `%s' (%d times)\n",
				pid->MR_proc_comp.MR_comp_type_module,
				pid->MR_proc_comp.MR_comp_type_name,
				pid->MR_proc_comp.MR_comp_pred_name,
				MR_closure_history[i].count);
		} else {
			fprintf(stderr,
				"%s:%s/%d-%d (%d times)\n",
				pid->MR_proc_user.MR_user_decl_module,
				pid->MR_proc_user.MR_user_name,
				pid->MR_proc_user.MR_user_arity,
				pid->MR_proc_user.MR_user_mode,
				MR_closure_history[i].count);
		}
	}

	fprintf(stderr, "Recent typeinfos searched in long lists:\n");
	for (i = 0; i < MR_dictionary_history_counter; i++) {
		fprintf(stderr, "%s:%s/%d (%d times)\n",
			MR_dictionary_history[i].type_ctor->
				type_ctor_module_name,
			MR_dictionary_history[i].type_ctor->type_ctor_name,
			MR_dictionary_history[i].type_ctor->arity,
			MR_dictionary_history[i].count);
	}
#endif
}

static void
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

	if (already_written) {
		MR_fatal_error("MR_write_out_proc_static: seen ps");
	}

	MR_hash_table_flag_written(MR_proc_static_table, ptr);

	MR_write_byte(fp, proc_static);
	MR_write_ptr(fp, kind_ps, ps_id);
	MR_write_string(fp, ptr->proc_id);
	MR_write_num(fp, ptr->num_call_sites);

	for (i = 0; i < ptr->num_call_sites; i++) {
		(void) MR_hash_table_insert(MR_call_site_static_table,
			ptr->call_sites[i], &css_id, NULL, FALSE);
		MR_write_ptr(fp, kind_css, css_id);
	}

	for (i = 0; i < ptr->num_call_sites; i++) {
		MR_write_out_callsite_static(fp, ptr->call_sites[i]);
	}
}

static void
MR_write_out_callsite_static(FILE *fp, const MR_CallSiteStatic *ptr)
{
	int	css_id;
	bool	already_written;

	if (ptr == NULL) {
		MR_fatal_error("MR_write_out_callsite_static: null css");
	}

	MR_write_byte(fp, callsite_static);
	(void) MR_hash_table_insert(MR_call_site_static_table, ptr,
		&css_id, &already_written, TRUE);

	if (already_written) {
		MR_fatal_error("MR_write_out_callsite_static: seen css");
	}

	MR_hash_table_flag_written(MR_call_site_static_table, ptr);

	MR_write_ptr(fp, kind_css, css_id);
	MR_write_byte(fp, ptr->call_site_kind);
	MR_write_string(fp, ptr->call_site_id);
}

static void
MR_write_out_callsite_dynamic(FILE *fp, const MR_CallSiteDynamic *ptr)
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
	fprintf(stderr, "%p -> { %p };\n", ptr, ptr->call_site_callee_ptr);
#endif
	MR_write_byte(fp, callsite_dynamic);
	if (! MR_hash_table_insert(MR_call_site_dynamic_table, ptr,
		&csd_id, NULL, TRUE))
	{
		MR_fatal_error(
			"MR_write_out_callsite_dynamic: insert succeeded");
	}

	MR_write_ptr(fp, kind_csd, csd_id);
	if (ptr->call_site_callee_ptr == NULL) {
		pd_id = 0;
	} else {
		(void) MR_hash_table_insert(MR_proc_dynamic_table,
			ptr->call_site_callee_ptr, &pd_id, NULL, FALSE);
	}

	MR_write_ptr(fp, kind_pd, pd_id);

#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	if (ptr->profiling_metrics.calls != 0)
		bitmask |= 0x0001;
	if (ptr->profiling_metrics.exits != 0)
		bitmask |= 0x0002;
	if (ptr->profiling_metrics.fails != 0)
		bitmask |= 0x0004;
	if (ptr->profiling_metrics.redos != 0)
		bitmask |= 0x0008;
#endif
#ifdef MR_DEEP_PROFILING_TIMING
	if (ptr->profiling_metrics.quanta != 0)
		bitmask |= 0x0010;
#endif
#ifdef MR_DEEP_PROFILING_MEMORY
	if (ptr->profiling_metrics.memory != 0)
		bitmask |= 0x0020;
#endif

	MR_write_num(fp, bitmask);

#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	if (ptr->profiling_metrics.calls != 0)
		MR_write_num(fp, ptr->profiling_metrics.calls);
	if (ptr->profiling_metrics.exits != 0)
		MR_write_num(fp, ptr->profiling_metrics.exits);
	if (ptr->profiling_metrics.fails != 0)
		MR_write_num(fp, ptr->profiling_metrics.fails);
	if (ptr->profiling_metrics.redos != 0)
		MR_write_num(fp, ptr->profiling_metrics.redos);
#endif

#ifdef MR_DEEP_PROFILING_TIMING
	if (ptr->profiling_metrics.quanta != 0)
		MR_write_num(fp, ptr->profiling_metrics.quanta);
#endif

#ifdef MR_DEEP_PROFILING_MEMORY
	if (ptr->profiling_metrics.memory != 0)
		MR_write_num(fp, ptr->profiling_metrics.memory);
#endif

	MR_write_out_proc_dynamic(fp, ptr->call_site_callee_ptr);
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
	(void) MR_hash_table_insert(MR_proc_static_table, ptr->proc_static,
		&ps_id, NULL, FALSE);

#ifdef MR_DEEP_PROFILING_STATISTICS
	MR_amount_of_memory += sizeof(MR_ProcDynamic);
	MR_amount_of_memory +=
		sizeof(MR_CallSiteDynamic*) * ptr->proc_static->num_call_sites;
#endif

	MR_write_byte(fp, proc_dynamic);
	MR_write_ptr(fp, kind_pd, pd_id);
	MR_write_ptr(fp, kind_ps, ps_id);
	MR_write_num(fp, ptr->proc_static->num_call_sites);

#ifdef MR_DEEP_PROFILING_DEBUG
	fprintf(stderr, "%p [label \"%s\"];\n", ptr, ptr->proc_static->proc_id);
#endif
	for (i = 0; i < ptr->proc_static->num_call_sites; i++) {
		MR_write_byte(fp,
			ptr->proc_static->call_sites[i]->call_site_kind);
		switch (ptr->proc_static->call_sites[i]->call_site_kind) {
			case normal:
#ifdef MR_DEEP_PROFILING_DEBUG
				fprintf(stderr, "%p -> { %p };\n",
					ptr, ptr->call_site_ptr_ptrs[i]);
#endif
				MR_write_csd_ptr(fp,
					ptr->call_site_ptr_ptrs[i]);
				break;

			case higher_order:
			case typeclass_method:
			case callback:
				MR_write_out_ho_call_site_ptrs(fp, ptr,
					(MR_CallSiteDynList *)
					ptr->call_site_ptr_ptrs[i]);
				break;
		}
	}

	for (i = 0; i < ptr->proc_static->num_call_sites; i++) {
		switch (ptr->proc_static->call_sites[i]->call_site_kind) {
			case normal:
				MR_write_out_callsite_dynamic(fp,
					ptr->call_site_ptr_ptrs[i]);
				break;

			case higher_order:
			case typeclass_method:
			case callback:
				MR_write_out_ho_call_site_nodes(fp,
					(MR_CallSiteDynList *)
					ptr->call_site_ptr_ptrs[i]);
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
		fprintf(stderr, "%p -> { %p };\n", ptr, dynlist->call_site);
#endif
		MR_write_csd_ptr(fp, dynlist->call_site);
		dynlist = dynlist->next;
	}
	MR_write_byte(fp, end);
}

static void
MR_write_out_ho_call_site_nodes(FILE *fp, MR_CallSiteDynList *dynlist)
{
	while (dynlist != NULL) {
		MR_write_out_callsite_dynamic(fp, dynlist->call_site);
		dynlist = dynlist->next;
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
	/* MR_write_byte(fp, (int) kind); */
	MR_write_num(fp, node_id);
}

static void
MR_write_byte(FILE *fp, const char byte)
{
	fputc(byte, fp);
}

static void
MR_write_num(FILE *fp, unsigned long num)
{
	unsigned char	pieces[sizeof(unsigned long) * 8 / 7 + 1];
	int		i;

	assert((int) num >= 0);

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

#endif	/* MR_DEEP_PROFILING */
