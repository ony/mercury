/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
**      Deep profiling module
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
}
/*----------------------------------------------------------------------------*/

/*
** Functions for writing out the data at the end of the execution.
*/

void MR_write_out_profiling_tree(FILE *fp);

void MR_write_out_callsite_static(FILE *fp, const MR_CallSiteStatic *ptr);
void MR_write_out_callsite_dynamic(FILE *fp, const MR_CallSiteDynamic *ptr);

void MR_write_out_proc_static(FILE *fp, const MR_ProcStatic *ptr);
void MR_write_out_proc_dynamic(FILE *fp, const MR_ProcDynamic *ptr);

/*
void MR_write_out_proc_layout(FILE *fp, const MR_Stack_Layout_Entry *layout);
*/

void MR_write_byte(FILE *fp, const char byte);
void MR_write_ptr(FILE *fp, const void *ptr);
void MR_write_num(FILE *fp, unsigned long num);
void MR_write_string(FILE *fp, const char *ptr);

/*----------------------------------------------------------------------------*/
/*
** We need a couple of hash tables, so here are some structures for handling
** them....
*/
typedef struct MR_PROFILING_HASH_NODE {
    const void			  *item;
    struct MR_PROFILING_HASH_NODE *next;
} MR_ProfilingHashNode;

typedef struct MR_PROFILING_HASH_TABLE {
    int				length;
    MR_ProfilingHashNode	**nodes;
} MR_ProfilingHashTable;

MR_ProfilingHashTable *MR_create_hash_table(int size);
MR_Bool MR_hash_table_insert(MR_ProfilingHashTable *table, const void *ptr);
MR_Bool MR_hash_table_present(MR_ProfilingHashTable *table, const void *ptr);

/*
** We need a hash table to store the *seen* MR_ProcDynamic nodes so we don't
** go into a loop when we encounter a cycle in the graph.
*/
static MR_ProfilingHashTable *MR_seen_nodes;

/*
** We also need a table to keep track of which MR_ProcStatic structures
** we need to write out.
*/
static MR_ProfilingHashTable *MR_needed_proc_statics;

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
    int i;
    MR_ProfilingHashNode *n;

    MR_seen_nodes = MR_create_hash_table(MR_hash_table_size);
    MR_needed_proc_statics = MR_create_hash_table(MR_hash_table_size);

#ifdef MR_DEEP_PROFILING_DEBUG
    fprintf(stderr, "root = %p\n", &MR_mainCallSite);
#endif
    MR_write_byte(fp, root);
    MR_write_ptr(fp, &MR_mainCallSite);

    MR_write_out_callsite_dynamic(fp, &MR_mainCallSite);

    for (i=0; i < MR_needed_proc_statics->length; i++)
    {
	n = MR_needed_proc_statics->nodes[i];
	while (n)
	{
	    MR_write_out_proc_static(fp, (const MR_ProcStatic *) n->item);
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
    fprintf(stderr, "Clousre/TypeInfo search length histogram:\n");
    for (i=0; i < MR_MAX_CLOSURE_LIST_LENGTH; i++)
	fprintf(stderr, "\t%3d : %12d %12d\n", i,
			MR_closure_search_lengths[i],
			MR_dictionary_search_lengths[i]);

    fprintf(stderr, "Recent closures searched in long lists:\n");
    for (i=0; i < MR_closure_history_counter; i++)
    {
	    MR_Proc_Id *pid = &(MR_closure_history[i].closure->closure_id->proc_id);
	    if (pid->MR_proc_user.MR_user_pred_or_func > MR_FUNCTION)
	    {
		    fprintf(stderr,
			"%s:%s `%s' (%d times)\n",
			pid->MR_proc_comp.MR_comp_type_module,
			pid->MR_proc_comp.MR_comp_type_name,
			pid->MR_proc_comp.MR_comp_pred_name,
			MR_closure_history[i].count);
	    }
	    else
	    {
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
    for (i=0; i < MR_dictionary_history_counter; i++)
    {
	    fprintf(stderr, "%s:%s/%d (%d times)\n",
		MR_dictionary_history[i].type_ctor->type_ctor_module_name,
		MR_dictionary_history[i].type_ctor->type_ctor_name,
		MR_dictionary_history[i].type_ctor->arity,
		MR_dictionary_history[i].count);
    }
#endif
}

void
MR_write_out_callsite_static(FILE *fp, const MR_CallSiteStatic *ptr)
{
    MR_write_byte(fp, callsite_static);
    MR_write_ptr(fp, ptr);
    MR_write_byte(fp, ptr->call_site_kind);
    MR_write_string(fp, ptr->call_site_id);
}

void
MR_write_out_proc_static(FILE *fp, const MR_ProcStatic *ptr)
{
    int i;

    MR_write_byte(fp, proc_static);
    MR_write_ptr(fp, ptr);
    MR_write_string(fp, ptr->proc_id);
    MR_write_num(fp, ptr->num_call_sites);

    for (i=0; i < ptr->num_call_sites; i++)
    {
	MR_write_ptr(fp, ptr->call_sites[i]);
    }

    for (i=0; i < ptr->num_call_sites; i++)
    {
	MR_write_out_callsite_static(fp, ptr->call_sites[i]);
    }
}

void
MR_write_out_callsite_dynamic(FILE *fp, const MR_CallSiteDynamic *ptr)
{
    int bitmask = 0;
    if (!ptr)
	return;

#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_amount_of_memory += sizeof(MR_CallSiteDynamic);
#endif

#ifdef MR_DEEP_PROFILING_DEBUG
    fprintf(stderr, "%p -> { %p };\n", ptr, ptr->call_site_callee_ptr);
#endif
    MR_write_byte(fp, callsite_dynamic);
    MR_write_ptr(fp, ptr);
    MR_write_ptr(fp, ptr->call_site_callee_ptr);

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

void
MR_write_out_proc_dynamic(FILE *fp, const MR_ProcDynamic *ptr)
{
    int i;

    /* This shouldn't really happen except that we don't have correct
     * handling of nondet pragma c code yet */
    if (!ptr)
	return;

    /* If we've seen this node alread, then don't write it again! */
    if (MR_hash_table_insert(MR_seen_nodes, ptr))
    {
	return;
    }

    MR_hash_table_insert(MR_needed_proc_statics, ptr->proc_static);

#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_amount_of_memory += sizeof(MR_ProcDynamic);
    MR_amount_of_memory +=
	    sizeof(MR_CallSiteDynamic*) * ptr->proc_static->num_call_sites;
#endif

    MR_write_byte(fp, proc_dynamic);
    MR_write_ptr(fp, ptr);
    MR_write_ptr(fp, ptr->proc_static);
    MR_write_num(fp, ptr->proc_static->num_call_sites);

#ifdef MR_DEEP_PROFILING_DEBUG
    fprintf(stderr, "%p [label \"%s\";\n", ptr, ptr->proc_static->proc_id);
#endif
    for (i=0; i < ptr->proc_static->num_call_sites; i++)
    {
        MR_write_byte(fp, ptr->proc_static->call_sites[i]->call_site_kind);
	switch (ptr->proc_static->call_sites[i]->call_site_kind)
	{
	    case normal :
#ifdef MR_DEEP_PROFILING_DEBUG
    fprintf(stderr, "%p -> { %p };\n", ptr, ptr->call_site_ptr_ptrs[i]);
#endif
		MR_write_ptr(fp, ptr->call_site_ptr_ptrs[i]);
		break;
	    case higher_order:
	    case typeclass_method:
	    case callback:
	    {
		MR_CallSiteDynList *tmp;
		tmp = (MR_CallSiteDynList *) ptr->call_site_ptr_ptrs[i]; 
		while (tmp)
		{
#ifdef MR_DEEP_PROFILING_STATISTICS
		    MR_amount_of_memory += sizeof(MR_CallSiteDynList);
#endif
#ifdef MR_DEEP_PROFILING_DEBUG
		    fprintf(stderr, "%p -> { %p };\n", ptr, tmp->call_site);
#endif
		    MR_write_ptr(fp, tmp->call_site);
		    tmp = tmp->next;
		}
	        MR_write_byte(fp, end);
	    }
	}
    }

    for (i=0; i < ptr->proc_static->num_call_sites; i++)
    {
	switch (ptr->proc_static->call_sites[i]->call_site_kind)
	{
	    case normal :
		MR_write_out_callsite_dynamic(fp, ptr->call_site_ptr_ptrs[i]);
		break;
	    case higher_order:
	    case typeclass_method:
	    case callback:
	    {
		MR_CallSiteDynList *tmp;
		tmp = (MR_CallSiteDynList *) ptr->call_site_ptr_ptrs[i]; 
		while (tmp)
		{
		    MR_write_out_callsite_dynamic(fp, tmp->call_site);
		    tmp = tmp->next;
		}
	    }
	}
    }
}

/*
void
MR_write_out_proc_layout(FILE *fp, const MR_Stack_Layout_Entry *layout)
{
    if (!MR_ENTRY_LAYOUT_COMPILER_GENERATED(layout))
    {
	if (layout->MR_sle_proc_id.MR_proc_user.MR_user_pred_or_func
		== MR_PREDICATE)
	{
	    MR_write_byte(fp, isa_prediate);
	}
	else
	{
	    MR_write_byte(fp, isa_function);
	}
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_user.MR_user_decl_module);
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_user.MR_user_def_module);
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_user.MR_user_name);
	MR_write_num(fp,
		layout->MR_sle_proc_id.MR_proc_user.MR_user_arity);
	MR_write_num(fp,
		layout->MR_sle_proc_id.MR_proc_user.MR_user_mode);
    }
    else
    {
	MR_write_byte(fp, isa_compiler_generated);
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_comp.MR_comp_type_name);
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_comp.MR_comp_type_module);
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_comp.MR_comp_def_module);
	MR_write_string(fp,
		layout->MR_sle_proc_id.MR_proc_comp.MR_comp_pred_name);
	MR_write_num(fp,
		layout->MR_sle_proc_id.MR_proc_comp.MR_comp_arity);
	MR_write_num(fp,
		layout->MR_sle_proc_id.MR_proc_comp.MR_comp_mode);
    }
}
*/

void
MR_write_byte(FILE *fp, const char byte)
{
    fputc(byte, fp);
}

void
MR_write_ptr(FILE *fp, const void *ptr)
{
    MR_write_num(fp, (unsigned long) ptr);
}

void
MR_write_num(FILE *fp, unsigned long num)
{
    unsigned char pieces[sizeof(unsigned long) * 8 / 7 + 1];
    int i;

    assert((int)num >= 0);

    i=0;
    do
    {
	pieces[i] = num & 0x7f;
	num = num >> 7;
	i++;
    } while (num != 0);

    i--;

    while (i > 0)
    {
	fputc(pieces[i--] | 0x80, fp);
    }
    fputc(pieces[0], fp);
}

void
MR_write_string(FILE *fp, const char *ptr)
{
    int i, len;

    len = strlen(ptr);
    MR_write_num(fp, len);
    for (i = 0; i < len; i++)
    {
	fputc(ptr[i], fp);
    }
}
/*----------------------------------------------------------------------------*/

MR_ProfilingHashTable *
MR_create_hash_table(int size)
{
    MR_ProfilingHashTable *ptr;
    ptr = MR_NEW(MR_ProfilingHashTable);
    ptr->length = size;
    ptr->nodes = MR_NEW_ARRAY(MR_ProfilingHashNode *, size);

    return ptr;
}

MR_Bool
MR_hash_table_insert(MR_ProfilingHashTable *table, const void *ptr)
{
    int hash;
    MR_ProfilingHashNode *node;

    hash = ((unsigned int) ptr >> 2) % table->length;

    node = table->nodes[hash];
    while (node)
    {
	if (node->item == ptr)
	{
	    return TRUE;
	}
	node = node->next;
    }
    node = MR_NEW(MR_ProfilingHashNode);
    node->item = ptr;
    node->next = table->nodes[hash];
    table->nodes[hash] = node;
    return FALSE;
}

MR_Bool
MR_hash_table_present(MR_ProfilingHashTable *table, const void *ptr)
{
    int hash;
    MR_ProfilingHashNode *node;

    hash = ((unsigned int) ptr >> 2) % table->length;

    node = table->nodes[hash];
    while (node)
    {
	if (node->item == ptr)
	{
	    return TRUE;
	}
	node = node->next;
    }
    return FALSE;
}

#endif  /* MR_DEEP_PROFILING */
