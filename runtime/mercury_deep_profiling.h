/*
** Copyright (C) 2001 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
*/

/*
** mercury_deep_profiling.h -- definitions for deep profiling.
*/

#ifndef MERCURY_DEEP_PROFILING_H
#define MERCURY_DEEP_PROFILING_H

#include "mercury_stack_layout.h"
#include "mercury_ho_call.h"

/* These should be controled by command line options */
#define MR_DEEP_PROFILING_CALL_COUNTS
#define MR_DEEP_PROFILING_TIMING
#define MR_DEEP_PROFILING_MEMORY

typedef enum MR_CALLSITE_KIND {
	normal,
	higher_order,
	typeclass_method,
	callback
} MR_CallsiteKind;

typedef struct MR_CallSiteStatic_Struct		MR_CallSiteStatic;
typedef struct MR_CallSiteDynamic_Struct	MR_CallSiteDynamic;
typedef struct MR_ProcStatic_Struct		MR_ProcStatic;
typedef struct MR_ProcDynamic_Struct		MR_ProcDynamic;
typedef struct MR_ProfilingMetrics_Struct	MR_ProfilingMetrics;

typedef struct MR_CallSiteDynList_Struct	MR_CallSiteDynList;

struct MR_ProfilingMetrics_Struct {
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	unsigned		calls;
	unsigned		exits;
	unsigned		fails;
	unsigned		redos;
#endif
#ifdef MR_DEEP_PROFILING_TIMING
	unsigned		quanta;
#endif
#ifdef MR_DEEP_PROFILING_MEMORY
	unsigned		memory;
#endif
};

struct MR_CallSiteStatic_Struct {
    	MR_CallsiteKind				call_site_kind;
	MR_ConstString				call_site_id;
};

struct MR_ProcStatic_Struct {
	MR_ConstString				proc_id;	/* XXX */
	int					num_call_sites;
	MR_CallSiteStatic			**call_sites;
#ifdef MR_USE_ACTIVATION_COUNTS
	int					activation_count;
#endif
	MR_ProcDynamic				*outermost_activation_ptr;
};

struct MR_CallSiteDynamic_Struct {
	MR_ProcDynamic				*call_site_callee_ptr;
	MR_ProfilingMetrics			profiling_metrics;
};

struct MR_ProcDynamic_Struct {
	MR_ProcStatic				*proc_static;
	MR_CallSiteDynamic			**call_site_ptr_ptrs;
};

struct MR_CallSiteDynList_Struct {
	MR_CallSiteDynamic			*call_site;
	const void				*key;
	MR_CallSiteDynList			*next;
};

typedef enum {
	end = 0,
	root,
	callsite_static,
	callsite_dynamic,
	proc_static,
	proc_dynamic,
	normal_call,
	higher_order_call,
	callbacks,
	isa_prediate,
	isa_function,
	isa_compiler_generated
} MR_Profile_Encoding_Tokens;

extern	volatile MR_CallSiteDynamic		*MR_parent_call_site_dynamic;
extern	volatile MR_CallSiteDynamic		*MR_next_call_site_dynamic;
extern	volatile MR_CallSiteDynamic		*MR_current_call_site_dynamic;
extern	volatile MR_CallSiteDynamic		**MR_current_callback_site;
#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
extern	volatile MR_Bool			MR_inside_deep_profiling_code;
#endif

extern	MR_CallSiteDynamic			*MR_rootCallSites[];

#ifdef MR_DEEP_PROFILING_STATISTICS
extern int MR_number_of_profiling_entries;
extern int MR_number_of_activation_loads;
extern int MR_amount_of_memory;
extern int MR_profiling_tree_memory;
#define MR_MAX_CLOSURE_LIST_LENGTH 256
#define MR_HISTORY_LENGTH 4096
extern int MR_dictionary_search_lengths[MR_MAX_CLOSURE_LIST_LENGTH];
extern int MR_dictionary_history_counter;
extern struct MR_DICTIONARY_SEARCH_HISTORY_STRUCT {
	MR_TypeCtorInfo type_ctor;
	int		count;
} MR_dictionary_history[MR_HISTORY_LENGTH];
extern int MR_closure_search_lengths[MR_MAX_CLOSURE_LIST_LENGTH];
extern int MR_closure_history_counter;
extern struct MR_CLOSURE_SEARCH_HISTORY_STRUCT {
	MR_Closure_Layout	*closure;
	int			count;
} MR_closure_history[MR_HISTORY_LENGTH];
extern int MR_history_thresh;
#endif

extern	void MR_prepare_for_callback(void *entry);

#define MR_PROFILING_MALLOC(type) MR_NEW(type)
#define MR_PROFILING_MALLOC_ARRAY(type, nelems) MR_NEW_ARRAY(type, nelems)

#endif	/* not MERCURY_DEEP_PROFILING_H */
