%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: profiling_builtin.m.
% Main author: conway.
% Stability: low.

% This file is automatically imported into every module
% when deep profiling is enabled.
% It contains support predicates used for deep profiling.
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module profiling_builtin.

:- interface.

:- type proc_static.
:- type call_site_dynamic.
:- type call_site_dynamic_addr.
:- type proc_dynamic.

:- impure pred make_new_csd_for_normal_call(call_site_dynamic::in, int::in)
		is det.

:- impure pred make_new_csd_for_special_call(call_site_dynamic::in, int::in,
		c_pointer::in) is det.

:- impure pred make_new_csd_for_ho_call(call_site_dynamic::in, int::in,
			c_pointer::in) is det.

:- impure pred make_new_csd_for_foreign_call(call_site_dynamic::in, int::in)
		is det.

:- impure pred det_call_port_code(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out) is det.

:- impure pred det_call_port_code(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out,
		proc_dynamic::out) is det.

:- impure pred det_exit_port_code(call_site_dynamic::in,
			call_site_dynamic::in) is det.

:- impure pred det_exit_port_code(call_site_dynamic::in,
			call_site_dynamic::in,
			proc_dynamic::in) is det.

:- impure pred semi_call_port_code(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out) is det.

:- impure pred semi_call_port_code(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out,
		proc_dynamic::out) is det.


:- impure pred semi_exit_port_code(call_site_dynamic::in,
			call_site_dynamic::in) is det.

:- impure pred semi_exit_port_code(call_site_dynamic::in,
			call_site_dynamic::in,
			proc_dynamic::in) is det.

:- impure pred semi_fail_port_code(call_site_dynamic::in,
			call_site_dynamic::in) is failure.

:- impure pred semi_fail_port_code(call_site_dynamic::in,
			call_site_dynamic::in,
			proc_dynamic::in) is failure.

:- impure pred non_call_port_code(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out,
		proc_dynamic::out) is det.

:- impure pred non_call_port_code(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out,
		proc_dynamic::out, proc_dynamic::out) is det.

:- impure pred non_exit_port_code(call_site_dynamic::in, call_site_dynamic::in,
		proc_dynamic::in) is det.

:- impure pred non_exit_port_code(call_site_dynamic::in, call_site_dynamic::in)
		is det.

:- impure pred non_redo_port_code1(call_site_dynamic::in, proc_dynamic::in)
		is failure.

:- impure pred non_redo_port_code2(call_site_dynamic::in, proc_dynamic::in)
		is failure.

:- impure pred non_fail_port_code(call_site_dynamic::in, call_site_dynamic::in)
		is failure.

:- impure pred non_fail_port_code(call_site_dynamic::in, call_site_dynamic::in,
		proc_dynamic::in) is failure.

:- impure pred set_outermost_activation_ptr(call_site_dynamic::in,
		proc_dynamic::in) is det.

:- impure pred save_and_zero_activation_info(call_site_dynamic::in,
		int::out, proc_dynamic::out) is det.

:- impure pred rezero_activation_info(call_site_dynamic::in) is det.

:- impure pred reset_activation_info(call_site_dynamic::in,
		int::in, proc_dynamic::in) is det.

:- impure pred set_current_csd(call_site_dynamic::in) is det.

:- impure pred save_recursion_depth_count(call_site_dynamic::in,
		int::in, int::out) is det.

:- impure pred restore_recursion_depth_count_exit(
		call_site_dynamic::in, int::in, int::in) is det.

:- impure pred restore_recursion_depth_count_fail(
		call_site_dynamic::in, int::in, int::in) is det.

%------------------------------------------------------------------------------%
:- implementation.

:- type proc_static ---> proc_static(c_pointer).
:- type call_site_dynamic ---> call_site_dynamic(c_pointer).
:- type call_site_dynamic_addr ---> call_site_dynamic_addr(c_pointer).
:- type proc_dynamic ---> proc_dynamic(c_pointer).

:- pragma c_header_code("
#ifdef MR_DEEP_PROFILING
    #include ""mercury_deep_profiling.h""
    #include ""mercury_ho_call.h""
    #include <stdio.h>
#endif
").

%------------------------------------------------------------------------------%
% Activation count versions
%------------------------------------------------------------------------------%

det_call_port_code(ProcDescr, TopCSD, MiddleCSD) :-
	impure create_proc_dynamic1(ProcDescr, TopCSD, MiddleCSD),
	%impure increment_activation_count(MiddleCSD),
	impure increment_call_count(MiddleCSD).

det_exit_port_code(TopCSD, MiddleCSD) :-
	impure increment_exit_count(MiddleCSD),
	impure decrement_activation_count(MiddleCSD),
	impure set_current_csd(TopCSD).

semi_call_port_code(ProcDescr, TopCSD, MiddleCSD) :-
	impure create_proc_dynamic1(ProcDescr, TopCSD, MiddleCSD),
	%impure increment_activation_count(MiddleCSD),
	impure increment_call_count(MiddleCSD).

semi_exit_port_code(TopCSD, MiddleCSD) :-
	impure increment_exit_count(MiddleCSD),
	impure decrement_activation_count(MiddleCSD),
	impure set_current_csd(TopCSD).

semi_fail_port_code(TopCSD, MiddleCSD) :-
	impure increment_fail_count(MiddleCSD),
	impure decrement_activation_count(MiddleCSD),
	impure set_current_csd(TopCSD),
	fail.

non_call_port_code(ProcDescr, TopCSD, MiddleCSD, NewActivationPtr) :-
	impure create_proc_dynamic1(ProcDescr, TopCSD, MiddleCSD,
			_OldActivationPtr, NewActivationPtr),
	%impure increment_activation_count(MiddleCSD),
	impure increment_call_count(MiddleCSD).

non_exit_port_code(TopCSD, MiddleCSD) :-
	impure increment_exit_count(MiddleCSD),
	impure decrement_activation_count(MiddleCSD),
	impure set_current_csd(TopCSD).

non_fail_port_code(TopCSD, MiddleCSD) :-
	impure increment_fail_count(MiddleCSD),
	impure decrement_activation_count(MiddleCSD),
	impure set_current_csd(TopCSD),
	fail.

non_redo_port_code1(MiddleCSD, NewOutermostProcDyn) :-
	impure set_current_csd(MiddleCSD),
	impure increment_redo_count(MiddleCSD),
	impure increment_activation_count(MiddleCSD, NewOutermostProcDyn),
	fail.

%------------------------------------------------------------------------------%
% Non-activation count versions
%------------------------------------------------------------------------------%

det_call_port_code(ProcDescr, TopCSD, MiddleCSD, OldActivationPtr) :-
	impure create_proc_dynamic2(ProcDescr, TopCSD, MiddleCSD,
			OldActivationPtr, _NewActivationPtr),
	impure increment_call_count(MiddleCSD).

det_exit_port_code(TopCSD, MiddleCSD, OutermostActivationPtr) :-
	impure increment_exit_count(MiddleCSD),
	impure set_outermost_activation_ptr(MiddleCSD, OutermostActivationPtr),
	impure set_current_csd(TopCSD).

semi_call_port_code(ProcDescr, TopCSD, MiddleCSD, OldActivationPtr) :-
	impure create_proc_dynamic2(ProcDescr, TopCSD, MiddleCSD,
			OldActivationPtr, _NewActivationPtr),
	impure increment_call_count(MiddleCSD).


semi_exit_port_code(TopCSD, MiddleCSD, OutermostActivationPtr) :-
	impure increment_exit_count(MiddleCSD),
	impure set_outermost_activation_ptr(MiddleCSD, OutermostActivationPtr),
	impure set_current_csd(TopCSD).

semi_fail_port_code(TopCSD, MiddleCSD, OutermostActivationPtr) :-
	impure increment_fail_count(MiddleCSD),
	impure set_outermost_activation_ptr(MiddleCSD, OutermostActivationPtr),
	impure set_current_csd(TopCSD),
	fail.

non_call_port_code(ProcDescr, TopCSD, MiddleCSD,
		OldActivationPtr, NewActivationPtr) :-
	impure create_proc_dynamic2(ProcDescr, TopCSD, MiddleCSD,
			OldActivationPtr, NewActivationPtr),
	impure increment_call_count(MiddleCSD).

non_exit_port_code(TopCSD, MiddleCSD, OldOutermostProcDyn) :-
	impure increment_exit_count(MiddleCSD),
	impure set_outermost_activation_ptr(MiddleCSD, OldOutermostProcDyn),
	impure set_current_csd(TopCSD).

non_redo_port_code2(MiddleCSD, NewOutermostProcDyn) :-
	impure set_current_csd(MiddleCSD),
	impure increment_redo_count(MiddleCSD),
	impure set_outermost_activation_ptr(MiddleCSD, NewOutermostProcDyn),
	fail.

non_fail_port_code(TopCSD, MiddleCSD, OldOutermostProcDyn) :-
	impure increment_fail_count(MiddleCSD),
	impure set_outermost_activation_ptr(MiddleCSD, OldOutermostProcDyn),
	impure set_current_csd(TopCSD),
	fail.

:- impure pred get_parent_and_curr_csd(call_site_dynamic::out,
			call_site_dynamic::out) is det.

:- pragma c_code(get_parent_and_curr_csd(Top::out, Middle::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
    Top = (Word) MR_parent_call_site_dynamic;
    Middle = (Word) MR_current_call_site_dynamic;
#endif
}").


:- pragma c_code(set_current_csd(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING

    MR_current_call_site_dynamic = (MR_CallSiteDynamic *) CSD;
#endif
}").

:- impure pred create_proc_dynamic1(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out) is det.

create_proc_dynamic1(ProcDescr, TopCSD, MiddleCSD) :-
	impure create_proc_dynamic1(ProcDescr, TopCSD, MiddleCSD, _, _).

:- impure pred create_proc_dynamic1(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out,
		proc_dynamic::out, proc_dynamic::out) is det.

:- pragma c_code(create_proc_dynamic1(Proc_descr::in, TopCSD::out,
			MiddleCSD::out, OldPtr::out, NewPtr::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifndef MR_USE_ACTIVATION_COUNTS
    fatal_error(""create_proc_dynamic1 called when not using activation counts!"");
#else
    MR_CallSiteDynamic *csd;
    MR_ProcStatic  *ps = (MR_ProcStatic *) Proc_descr;

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = TRUE;
#endif

#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
    MR_current_call_site_dynamic = MR_next_call_site_dynamic;
#endif
    csd = MR_current_call_site_dynamic;

    TopCSD = (MR_Word) MR_parent_call_site_dynamic;
    MiddleCSD = (MR_Word) MR_current_call_site_dynamic;
    OldPtr = (Word) ps->outermost_activation_ptr;

    MR_assert(ps->activation_count == 0 || ps->outermost_activation_ptr != NULL);

    if (csd->call_site_callee_ptr)
    {
    	if (ps->activation_count++ == 0)
		ps->outermost_activation_ptr = csd->call_site_callee_ptr;
    }
    else if (ps->activation_count++)
    {

#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_number_of_activation_loads++;
#endif

    	csd->call_site_callee_ptr = ps->outermost_activation_ptr;
    }
    else
    {
    	int i;
    	MR_ProcDynamic *proc_dyn = MR_PROFILING_MALLOC(MR_ProcDynamic);

#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_number_of_profiling_entries++;
#endif

	proc_dyn->proc_static = ps;
	proc_dyn->call_site_ptr_ptrs =
		MR_PROFILING_MALLOC_ARRAY(MR_CallSiteDynamic *, ps->num_call_sites);
	for (i=0; i < ps->num_call_sites; i++)
	{
	    proc_dyn->call_site_ptr_ptrs[i] = NULL;
	}
    	csd->call_site_callee_ptr = proc_dyn;
	ps->outermost_activation_ptr = proc_dyn;
    }

    NewPtr = (Word) ps->outermost_activation_ptr;

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = FALSE;
#endif

#endif
#endif
}").

:- impure pred create_proc_dynamic2(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out) is det.

create_proc_dynamic2(ProcDescr, TopCSD, MiddleCSD) :-
	impure create_proc_dynamic2(ProcDescr, TopCSD, MiddleCSD, _, _).

:- impure pred create_proc_dynamic2(proc_static::in,
		call_site_dynamic::out, call_site_dynamic::out,
		proc_dynamic::out, proc_dynamic::out) is det.

:- pragma c_code(create_proc_dynamic2(Proc_descr::in, TopCSD::out,
			MiddleCSD::out, OldPtr::out, NewPtr::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
    fatal_error(""create_proc_dynamic2 called when using activation counts!"");
#else
    MR_CallSiteDynamic *csd = MR_current_call_site_dynamic;
    MR_ProcStatic  *ps = (MR_ProcStatic *) Proc_descr;

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = TRUE;
#endif

    TopCSD = (MR_Word) MR_parent_call_site_dynamic;
    MiddleCSD = (MR_Word) MR_current_call_site_dynamic;
    OldPtr = (Word) ps->outermost_activation_ptr;

#ifdef MR_DEEP_PROFILING_DEBUG
    fprintf(stderr, ""entering %s\n"", ps->proc_id);
    fprintf(stderr, ""\toutermost_activation_ptr = %p\n"", ps->outermost_activation_ptr);
#endif

    if (csd->call_site_callee_ptr)
    {
    }
    else if (ps->outermost_activation_ptr)
    {
    	csd->call_site_callee_ptr = ps->outermost_activation_ptr;
    }
    else
    {
    	int i;
    	MR_ProcDynamic *proc_dyn = MR_PROFILING_MALLOC(MR_ProcDynamic);

	proc_dyn->proc_static = ps;
	proc_dyn->call_site_ptr_ptrs =
		MR_PROFILING_MALLOC_ARRAY(MR_CallSiteDynamic *, ps->num_call_sites);

	for (i=0; i < ps->num_call_sites; i++)
	{
	    proc_dyn->call_site_ptr_ptrs[i] = NULL;
	}

    	csd->call_site_callee_ptr = proc_dyn;
    }

    ps->outermost_activation_ptr = csd->call_site_callee_ptr;

    NewPtr = (Word) ps->outermost_activation_ptr;

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = FALSE;
#endif

#endif
#endif
}").

:- impure pred increment_activation_count(call_site_dynamic::in) is det.

:- pragma c_code(increment_activation_count(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    MR_assert(csd == MR_current_call_site_dynamic);

#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_number_of_profiling_entries++;
#endif

    MR_assert(csd->call_site_callee_ptr->proc_static->activation_count >= 0);
    csd->call_site_callee_ptr->proc_static->activation_count++;

#else
    fatal_error(""increment_activation_count: no activation_count"");
#endif
#endif
}").

:- impure pred increment_activation_count(call_site_dynamic::in,
		proc_dynamic::in) is det.

:- pragma c_code(increment_activation_count(CSD::in, PD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    MR_assert(csd == MR_current_call_site_dynamic);

    csd->call_site_callee_ptr->proc_static->activation_count++;
    csd->call_site_callee_ptr->proc_static->outermost_activation_ptr
    		= (MR_ProcDynamic*) PD;
#else
    fatal_error(""increment_activation_count: no activation_count"");
#endif
#endif
}").

:- impure pred increment_activation_count(call_site_dynamic::in,
		int::out, proc_dynamic::out) is det.

:- pragma c_code(increment_activation_count(CSD::in, X::out, Y::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    MR_assert(csd == MR_current_call_site_dynamic);

    csd->call_site_callee_ptr->proc_static->activation_count++;
    X = csd->call_site_callee_ptr->proc_static->activation_count;
    Y = (MR_Word) csd->call_site_callee_ptr
    			->proc_static->outermost_activation_ptr;
#else
    fatal_error(""increment_activation_count: no activation_count"");
#endif
#endif
}").

:- impure pred decrement_activation_count(call_site_dynamic::in) is det.

:- pragma c_code(decrement_activation_count(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    MR_assert(csd == MR_current_call_site_dynamic);

    csd->call_site_callee_ptr->proc_static->activation_count--;
    MR_assert(csd->call_site_callee_ptr->proc_static->activation_count >= 0);
#else
    fatal_error(""increment_activation_count: no activation_count"");
#endif
#endif
}").

:- pragma c_code(set_outermost_activation_ptr(CSD::in, Ptr::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
    MR_ProcDynamic *proc_dyn = (MR_ProcDynamic *) Ptr;

    csd->call_site_callee_ptr->proc_static->outermost_activation_ptr = proc_dyn;
#endif
}").

:- pragma c_code(make_new_csd_for_normal_call(CSD::in, N::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
    MR_CallSiteDynamic *tmp;

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = TRUE;
#endif

    MR_assert(csd == MR_current_call_site_dynamic);

    if (!(tmp = csd->call_site_callee_ptr->call_site_ptr_ptrs[N]))
    {
    	tmp = MR_PROFILING_MALLOC(MR_CallSiteDynamic);

	tmp->call_site_callee_ptr = NULL;
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	tmp->profiling_metrics.calls = 0;
	tmp->profiling_metrics.exits = 0;
	tmp->profiling_metrics.fails = 0;
	tmp->profiling_metrics.redos = 0;
#endif
#ifdef MR_DEEP_PROFILING_TIMING
	tmp->profiling_metrics.quanta = 0;
#endif
#ifdef MR_DEEP_PROFILING_MEMORY
	tmp->profiling_metrics.memory_mallocs = 0;
	tmp->profiling_metrics.memory_words = 0;
#endif
	csd->call_site_callee_ptr->call_site_ptr_ptrs[N] = tmp;
    }

    MR_parent_call_site_dynamic = MR_current_call_site_dynamic;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
    MR_next_call_site_dynamic = tmp;
#else
    MR_current_call_site_dynamic = tmp;
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = FALSE;
#endif

#endif
}").

:- pragma c_code(make_new_csd_for_special_call(CSD::in, N::in, TInfo::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
    MR_CallSiteDynList *tmp;
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
    MR_CallSiteDynList *prev = NULL;
#endif
    MR_TypeCtorInfo	type_ctor_info;
    MR_TypeInfo		type_info;
    int			done = 0;
#ifdef MR_DEEP_PROFILING_STATISTICS
    int			slen = 0;
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = TRUE;
#endif

    MR_assert(csd == MR_current_call_site_dynamic);

    type_info = (MR_TypeInfo) TInfo;
    type_ctor_info = MR_TYPEINFO_GET_TYPE_CTOR_INFO(type_info);

    tmp = (MR_CallSiteDynList*)csd->call_site_callee_ptr->call_site_ptr_ptrs[N];

    while (tmp)
    {
#ifdef MR_DEEP_PROFILING_STATISTICS
	slen++;
#endif
    	if (tmp->key == (void *) (type_ctor_info->unify_pred))
	{
	    MR_parent_call_site_dynamic = MR_current_call_site_dynamic;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
	    MR_next_call_site_dynamic = tmp->call_site;
#else
	    MR_current_call_site_dynamic = tmp->call_site;
#endif

	    done = 1;
	    break;
	}
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
	prev = tmp;
#endif
	tmp = tmp->next;
    }
#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_dictionary_search_lengths[slen]++;
    if (slen >=MR_history_thresh && MR_dictionary_history_counter < MR_HISTORY_LENGTH)
    {
    	int i;
	for (i=0; i < MR_dictionary_history_counter; i++)
	{
	    if (MR_dictionary_history[i].type_ctor == type_ctor_info)
	        break;
	}

	if (i == MR_dictionary_history_counter)
	{
	    MR_dictionary_history_counter++;
	    MR_dictionary_history[i].type_ctor = type_ctor_info;
	    MR_dictionary_history[i].count = 0;
	}
	MR_dictionary_history[i].count++;
    }
#endif

    if (!done)
    {
    	MR_CallSiteDynamic *tmp2;
    	tmp2 = MR_PROFILING_MALLOC(MR_CallSiteDynamic);
	tmp2->call_site_callee_ptr = NULL;
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	tmp2->profiling_metrics.calls = 0;
	tmp2->profiling_metrics.exits = 0;
	tmp2->profiling_metrics.fails = 0;
	tmp2->profiling_metrics.redos = 0;
#endif
#ifdef MR_DEEP_PROFILING_TIMING
	tmp2->profiling_metrics.quanta = 0;
#endif
#ifdef MR_DEEP_PROFILING_MEMORY
	tmp2->profiling_metrics.memory_mallocs = 0;
	tmp2->profiling_metrics.memory_words = 0;
#endif
	
	tmp = MR_PROFILING_MALLOC(MR_CallSiteDynList);
	tmp->key = (void *) (type_ctor_info->unify_pred);
	tmp->call_site = tmp2;
	tmp->next = (MR_CallSiteDynList*)
		csd->call_site_callee_ptr->call_site_ptr_ptrs[N];

	csd->call_site_callee_ptr->call_site_ptr_ptrs[N]
		= (MR_CallSiteDynamic*) tmp;

	MR_parent_call_site_dynamic = MR_current_call_site_dynamic;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
	MR_next_call_site_dynamic = tmp2;
#else
	MR_current_call_site_dynamic = tmp2;
#endif
    }
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
    else
    {
    	if (prev != NULL)
	{
	    prev->next = tmp->next;
	    
	    tmp->next = (MR_CallSiteDynList*)
		csd->call_site_callee_ptr->call_site_ptr_ptrs[N];

	    csd->call_site_callee_ptr->call_site_ptr_ptrs[N]
		= (MR_CallSiteDynamic*) tmp;

	}
    }
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = FALSE;
#endif

#endif
}").

:- pragma c_code(make_new_csd_for_ho_call(CSD::in, N::in, Closure::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
    MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
    MR_Closure *closure = (MR_Closure *) Closure;
    MR_CallSiteDynList *tmp;
    void *key;
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
    MR_CallSiteDynList *prev = NULL;
#endif
    int done = 0;
#ifdef MR_DEEP_PROFILING_STATISTICS
    int			slen = 0;
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = TRUE;
#endif

    MR_assert(csd == MR_current_call_site_dynamic);

#ifdef MR_DEEP_PROFILING_KEY_USES_ID
    key = (void *) (closure->MR_closure_layout);
#else
    key = (void *) (closure->MR_closure_code);
#endif
    tmp = (MR_CallSiteDynList*)csd->call_site_callee_ptr->call_site_ptr_ptrs[N];

    while (tmp)
    {
#ifdef MR_DEEP_PROFILING_STATISTICS
	slen++;
#endif
    	if (tmp->key == key)
	{
	    MR_parent_call_site_dynamic = MR_current_call_site_dynamic;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
	    MR_next_call_site_dynamic = tmp->call_site;
#else
	    MR_current_call_site_dynamic = tmp->call_site;
#endif

	    done = 1;
	    break;
	}
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
	prev = tmp;
#endif
	tmp = tmp->next;
    }
#ifdef MR_DEEP_PROFILING_STATISTICS
    MR_closure_search_lengths[slen]++;
    if (slen >=MR_history_thresh && MR_closure_history_counter < MR_HISTORY_LENGTH)
    {
        int i;
        for (i = 0; i < MR_closure_history_counter; i++)
        {
	    if (MR_closure_history[i].closure == closure->MR_closure_layout)
		break;
	}
	if (i == MR_closure_history_counter)
	{
	    MR_closure_history_counter++;
	    MR_closure_history[i].closure = closure->MR_closure_layout;
	    MR_closure_history[i].count = 0;
	}
	MR_closure_history[i].count++;
    }
#endif

    if (!done)
    {
    	MR_CallSiteDynamic *tmp2;
    	tmp2 = MR_PROFILING_MALLOC(MR_CallSiteDynamic);
	tmp2->call_site_callee_ptr = NULL;
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	tmp2->profiling_metrics.calls = 0;
	tmp2->profiling_metrics.exits = 0;
	tmp2->profiling_metrics.fails = 0;
	tmp2->profiling_metrics.redos = 0;
#endif
#ifdef MR_DEEP_PROFILING_TIMING
	tmp2->profiling_metrics.quanta = 0;
#endif
#ifdef MR_DEEP_PROFILING_MEMORY
	tmp2->profiling_metrics.memory_mallocs = 0;
	tmp2->profiling_metrics.memory_words = 0;
#endif
	
	tmp = MR_PROFILING_MALLOC(MR_CallSiteDynList);
	tmp->key = key;
	tmp->call_site = tmp2;
	tmp->next = (MR_CallSiteDynList*)
		csd->call_site_callee_ptr->call_site_ptr_ptrs[N];
	csd->call_site_callee_ptr->call_site_ptr_ptrs[N]
		= (MR_CallSiteDynamic*) tmp;

	MR_parent_call_site_dynamic = MR_current_call_site_dynamic;
#ifdef MR_DEEP_PROFILING_DELAYED_CSD_UPDATE
	MR_next_call_site_dynamic = tmp2;
#else
	MR_current_call_site_dynamic = tmp2;
#endif
    }
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
    else
    {
    	if (prev != NULL)
	{
	    prev->next = tmp->next;
	    
	    tmp->next = (MR_CallSiteDynList*)
		csd->call_site_callee_ptr->call_site_ptr_ptrs[N];

	    csd->call_site_callee_ptr->call_site_ptr_ptrs[N]
		= (MR_CallSiteDynamic*) tmp;

	}
    }
#endif

#ifdef MR_DEEP_PROFILING_IGNORE_INSTRUMENTATION
    MR_inside_deep_profiling_code = FALSE;
#endif

#endif
}").

:- pragma c_code(make_new_csd_for_foreign_call(CSD::in, N::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    MR_assert(csd == MR_current_call_site_dynamic);

    MR_current_callback_site =
    	&(csd->call_site_callee_ptr->call_site_ptr_ptrs[N]);
#endif
}").

:- impure pred increment_call_count(call_site_dynamic::in) is det.
:- pragma c_code(increment_call_count(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    assert(csd == MR_current_call_site_dynamic);
    csd->profiling_metrics.calls++;
#endif
#endif
}").

:- impure pred increment_exit_count(call_site_dynamic::in) is det.
:- pragma c_code(increment_exit_count(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    assert(csd == MR_current_call_site_dynamic);
    csd->profiling_metrics.exits++;
#endif
#endif
}").

:- impure pred increment_redo_count(call_site_dynamic::in) is det.
:- pragma c_code(increment_redo_count(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    csd->profiling_metrics.redos++;
#endif
#endif
}").

:- impure pred increment_fail_count(call_site_dynamic::in) is det.
:- pragma c_code(increment_fail_count(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_CALL_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    assert(csd == MR_current_call_site_dynamic);
    csd->profiling_metrics.fails++;
#endif
#endif
}").


:- pragma c_code(save_and_zero_activation_info(CSD::in, Count::out, Ptr::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    Count = csd->call_site_callee_ptr->proc_static->activation_count;
    csd->call_site_callee_ptr->proc_static->activation_count = 0;
    Ptr = (Word)
    	csd->call_site_callee_ptr->proc_static->outermost_activation_ptr;
    csd->call_site_callee_ptr->proc_static->outermost_activation_ptr = NULL;

#else
    fatal_error(""save_and_zero_activation_info: no activation_count"");
#endif
#endif
}").

:- pragma c_code(rezero_activation_info(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    csd->call_site_callee_ptr->proc_static->activation_count = 0;
    csd->call_site_callee_ptr->proc_static->outermost_activation_ptr = NULL;

#else
    fatal_error(""save_and_zero_activation_info: no activation_count"");
#endif
#endif
}").

:- pragma c_code(reset_activation_info(CSD::in, Count::in, Ptr::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;

    assert(csd == MR_current_call_site_dynamic);
    csd->call_site_callee_ptr->proc_static->activation_count = Count;
    csd->call_site_callee_ptr->proc_static->outermost_activation_ptr
    	= (MR_ProcDynamic *) Ptr;

#else
    fatal_error(""reset_activation_info: no activation_count"");
#endif
#endif
}").

:- pragma c_code(save_recursion_depth_count(CSD::in, CSN::in, Count::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_TAIL_RECURSION
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
	MR_CallSiteDynamic *inner_csd;
	
	inner_csd = csd->call_site_dynamic->proc_static->
			call_site_ptr_ptrs[CSN];
	
	if (inner_csd != NULL) {
		Count = inner_csd->depth_count;
	} else {
		Count = 0;
	}
#else
	fatal_error(""save_recursion_depth_count: no depth counts"");
#endif
#endif
}").

:- pragma c_code(restore_recursion_depth_count_exit(
		CSD::in, CSN::in, OuterCount::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_TAIL_RECURSION
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
	MR_CallSiteDynamic *inner_csd;
	int inner_count;
	
	inner_csd = csd->call_site_dynamic->proc_static->
			call_site_ptr_ptrs[CSN];
	inner_count = inner_csd->depth_count;
	inner_csd->depth_count = 0;

	inner_csd->profiling_metrics->calls += inner_count;
	inner_csd->profiling_metrics->exits += inner_count;

	inner_csd->depth_count = OuterCount;
#else
	fatal_error(""save_recursion_depth_count: no depth counts"");
#endif
#endif
}").

:- pragma c_code(restore_recursion_depth_count_fail(
		CSD::in, CSN::in, OuterCount::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_TAIL_RECURSION
	MR_CallSiteDynamic *csd = (MR_CallSiteDynamic *) CSD;
	MR_CallSiteDynamic *inner_csd;
	int inner_count;
	
	inner_csd = csd->call_site_dynamic->proc_static->
			call_site_ptr_ptrs[CSN];
	inner_count = inner_csd->depth_count;
	inner_csd->depth_count = 0;

	inner_csd->profiling_metrics->calls += inner_count;
	inner_csd->profiling_metrics->fails += inner_count;

	inner_csd->depth_count = OuterCount;
#else
	fatal_error(""save_recursion_depth_count: no depth counts"");
#endif
#endif
}").

