%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%
%
% File: profiling_builtin.m.
% Authors: conway, zs.
% Stability: low.
%
% This file is automatically imported into every module
% when deep profiling is enabled.
% It contains support predicates used for deep profiling.
%
%---------------------------------------------------------------------------%

:- module profiling_builtin.

:- interface.

:- type proc_static.
:- type proc_dynamic.
:- type call_site_dynamic.

:- impure pred prepare_for_normal_call(call_site_dynamic::in, int::in) is det.

:- impure pred prepare_for_special_call(call_site_dynamic::in, int::in,
	c_pointer::in) is det.

:- impure pred prepare_for_ho_call(call_site_dynamic::in, int::in,
	c_pointer::in) is det.

:- impure pred prepare_for_callback(call_site_dynamic::in, int::in) is det.

:- impure pred det_call_port_code_ac(proc_static::in,
	call_site_dynamic::out, call_site_dynamic::out) is det.

:- impure pred det_call_port_code_sr(proc_static::in, call_site_dynamic::out,
	call_site_dynamic::out, proc_dynamic::out) is det.

:- impure pred det_exit_port_code_ac(call_site_dynamic::in,
	call_site_dynamic::in) is det.

:- impure pred det_exit_port_code_sr(call_site_dynamic::in,
	call_site_dynamic::in, proc_dynamic::in) is det.

:- impure pred semi_call_port_code_ac(proc_static::in,
	call_site_dynamic::out, call_site_dynamic::out) is det.

:- impure pred semi_call_port_code_sr(proc_static::in, call_site_dynamic::out,
	call_site_dynamic::out, proc_dynamic::out) is det.

:- impure pred semi_exit_port_code_ac(call_site_dynamic::in,
	call_site_dynamic::in) is det.

:- impure pred semi_exit_port_code_sr(call_site_dynamic::in,
	call_site_dynamic::in, proc_dynamic::in) is det.

:- impure pred semi_fail_port_code_ac(call_site_dynamic::in,
	call_site_dynamic::in) is failure.

:- impure pred semi_fail_port_code_sr(call_site_dynamic::in,
	call_site_dynamic::in, proc_dynamic::in) is failure.

:- impure pred non_call_port_code_ac(proc_static::in, call_site_dynamic::out,
	call_site_dynamic::out, proc_dynamic::out) is det.

:- impure pred non_call_port_code_sr(proc_static::in, call_site_dynamic::out,
	call_site_dynamic::out, proc_dynamic::out, proc_dynamic::out) is det.

:- impure pred non_exit_port_code_ac(call_site_dynamic::in,
	call_site_dynamic::in) is det.

:- impure pred non_exit_port_code_sr(call_site_dynamic::in,
	call_site_dynamic::in, proc_dynamic::in) is det.

:- impure pred non_redo_port_code_ac(call_site_dynamic::in, proc_dynamic::in)
	is failure.

:- impure pred non_redo_port_code_sr(call_site_dynamic::in, proc_dynamic::in)
	is failure.

:- impure pred non_fail_port_code_ac(call_site_dynamic::in,
	call_site_dynamic::in) is failure.

:- impure pred non_fail_port_code_sr(call_site_dynamic::in,
	call_site_dynamic::in, proc_dynamic::in) is failure.

:- impure pred inner_call_port_code(proc_static::in, call_site_dynamic::out)
	is det.

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

%---------------------------------------------------------------------------%

:- implementation.

:- type proc_static		---> proc_static(c_pointer).
:- type proc_dynamic		---> proc_dynamic(c_pointer).
:- type call_site_dynamic	---> call_site_dynamic(c_pointer).

:- pragma foreign_decl("C", "
#ifndef	MR_DEEP_PROFILING_GUARD
#define	MR_DEEP_PROFILING_GUARD

#ifdef	MR_DEEP_PROFILING

#include ""mercury_deep_profiling.h""
#include ""mercury_ho_call.h""
#include <stdio.h>

#endif	/* MR_DEEP_PROFILING */

#endif	/* MR_DEEP_PROFILING_GUARD */
").

%---------------------------------------------------------------------------%
% Call port procedures
%---------------------------------------------------------------------------%

:- pragma c_code(det_call_port_code_ac(ProcStatic::in, TopCSD::out,
		MiddleCSD::out),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: ProcStatic, TopCSD, MiddleCSD */
#define procname	""det_call_port_code_ac""
#define version_ac
#undef need_new_outermost
#include ""mercury_deep_call_port_body.h""
#undef procname
#undef version_ac
}").

:- pragma c_code(semi_call_port_code_ac(ProcStatic::in, TopCSD::out,
		MiddleCSD::out),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: ProcStatic, TopCSD, MiddleCSD */
#define procname	""semi_call_port_code_ac""
#define version_ac
#undef need_new_outermost
#include ""mercury_deep_call_port_body.h""
#undef procname
#undef version_ac
}").

:- pragma c_code(non_call_port_code_ac(ProcStatic::in, TopCSD::out,
		MiddleCSD::out, NewOutermostActivationPtr::out),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: ProcStatic, TopCSD, MiddleCSD */
/* shut up warning: NewOutermostActivationPtr */
#define procname	""non_call_port_code_ac""
#define version_ac
#define need_new_outermost
#include ""mercury_deep_call_port_body.h""
#undef procname
#undef version_ac
#undef need_new_outermost
}").

:- pragma c_code(det_call_port_code_sr(ProcStatic::in, TopCSD::out,
		MiddleCSD::out, OldOutermostActivationPtr::out),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: ProcStatic, TopCSD, MiddleCSD */
/* shut up warning: OldOutermostActivationPtr */
#define procname	""det_call_port_code_sr""
#define version_sr
#undef need_new_outermost
#include ""mercury_deep_call_port_body.h""
#undef procname
#undef version_sr
}").

:- pragma c_code(semi_call_port_code_sr(ProcStatic::in, TopCSD::out,
		MiddleCSD::out, OldOutermostActivationPtr::out),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: ProcStatic, TopCSD, MiddleCSD */
/* shut up warning: OldOutermostActivationPtr */
#define procname	""semi_call_port_code_sr""
#define version_sr
#undef need_new_outermost
#include ""mercury_deep_call_port_body.h""
#undef procname
#undef version_sr
}").

:- pragma c_code(non_call_port_code_sr(ProcStatic::in, TopCSD::out,
		MiddleCSD::out, OldOutermostActivationPtr::out,
		NewOutermostActivationPtr::out),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: ProcStatic, TopCSD, MiddleCSD */
/* shut up warning: OldOutermostActivationPtr, NewOutermostActivationPtr */
#define procname	""non_call_port_code_sr""
#define version_sr
#define need_new_outermost
#include ""mercury_deep_call_port_body.h""
#undef procname
#undef version_sr
#undef need_new_outermost
}").

%---------------------------------------------------------------------------%
% Exit/Fail port procedures
%---------------------------------------------------------------------------%

:- pragma c_code(det_exit_port_code_ac(TopCSD::in, MiddleCSD::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD */
#define procname	""det_exit_port_code_ac""
#define exit_port
#define version_ac
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef exit_port
#undef version_ac
}").

:- pragma c_code(det_exit_port_code_sr(TopCSD::in, MiddleCSD::in,
		OldOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD, OldOutermostActivationPtr */
#define procname	""det_exit_port_code_sr""
#define exit_port
#define version_sr
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef exit_port
#undef version_sr
}").

:- pragma c_code(semi_exit_port_code_ac(TopCSD::in, MiddleCSD::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD */
#define procname	""semi_exit_port_code_ac""
#define exit_port
#define version_ac
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef exit_port
#undef version_ac
}").

:- pragma c_code(semi_exit_port_code_sr(TopCSD::in, MiddleCSD::in,
		OldOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD, OldOutermostActivationPtr */
#define procname	""semi_exit_port_code_sr""
#define exit_port
#define version_sr
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef exit_port
#undef version_sr
}").

:- pragma c_code(semi_fail_port_code_ac(TopCSD::in, MiddleCSD::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD */
#define procname	""semi_exit_port_code_ac""
#define fail_port
#define version_ac
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef fail_port
#undef version_ac
}").

:- pragma c_code(semi_fail_port_code_sr(TopCSD::in, MiddleCSD::in,
		OldOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD, OldOutermostActivationPtr */
#define procname	""semi_fail_port_code_sr""
#define fail_port
#define version_sr
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef fail_port
#undef version_sr
}").

:- pragma c_code(non_exit_port_code_ac(TopCSD::in, MiddleCSD::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD */
#define procname	""non_exit_port_code_ac""
#define exit_port
#define version_ac
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef exit_port
#undef version_ac
}").

:- pragma c_code(non_exit_port_code_sr(TopCSD::in, MiddleCSD::in,
		OldOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD, OldOutermostActivationPtr */
#define procname	""non_exit_port_code_sr""
#define exit_port
#define version_sr
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef exit_port
#undef version_sr
}").

:- pragma c_code(non_fail_port_code_ac(TopCSD::in, MiddleCSD::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD */
#define procname	""non_exit_port_code_ac""
#define fail_port
#define version_ac
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef fail_port
#undef version_ac
}").

:- pragma c_code(non_fail_port_code_sr(TopCSD::in, MiddleCSD::in,
		OldOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: TopCSD, MiddleCSD, OldOutermostActivationPtr */
#define procname	""non_fail_port_code_sr""
#define fail_port
#define version_sr
#include ""mercury_deep_leave_port_body.h""
#undef procname
#undef fail_port
#undef version_sr
}").

%---------------------------------------------------------------------------%
% Redo port procedures
%---------------------------------------------------------------------------%

:- pragma c_code(non_redo_port_code_ac(MiddleCSD::in,
		NewOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: MiddleCSD, NewOutermostActivationPtr */
#define procname	""non_redo_port_code_ac""
#define version_ac
#include ""mercury_deep_redo_port_body.h""
#undef procname
#undef version_ac
}").

:- pragma c_code(non_redo_port_code_sr(MiddleCSD::in,
		NewOutermostActivationPtr::in),
		[thread_safe, will_not_call_mercury],
"{
/* shut up warning: MiddleCSD, NewOutermostActivationPtr */
#define procname	""non_redo_port_code_sr""
#define version_sr
#include ""mercury_deep_redo_port_body.h""
#undef procname
#undef version_sr
}").

%---------------------------------------------------------------------------%
% Procedures that prepare for calls
%---------------------------------------------------------------------------%

:- pragma c_code(prepare_for_normal_call(CSD::in, N::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_CallSiteDynamic	*csd;
	MR_ProcDynamic		*pd;
	MR_CallSiteDynamic	*child_csd;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	MR_deep_assert(csd == MR_current_call_site_dynamic);
	pd = csd->MR_csd_callee_ptr;
	MR_deep_assert(pd != NULL);

	child_csd = pd->MR_pd_call_site_ptr_ptrs[N];
	if (child_csd == NULL) {
		MR_new_call_site_dynamic(child_csd);
		pd->MR_pd_call_site_ptr_ptrs[N] = child_csd;
	}

	MR_next_call_site_dynamic = child_csd;
	MR_leave_instrumentation();
#else
	MR_fatal_error(""prepare_for_normal_call: deep profiling not enabled"");
#endif
}").

:- pragma c_code(prepare_for_special_call(CSD::in, CSN::in, TInfo::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_CallSiteDynamic	*csd;
	MR_ProcDynamic		*pd;
	MR_CallSiteDynList	*csdlist;
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
	MR_CallSiteDynList	*prev = NULL;
#endif
	MR_TypeCtorInfo		type_ctor_info;
	MR_TypeInfo		type_info;
	void			*void_key;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	MR_deep_assert(csd == MR_current_call_site_dynamic);
	pd = csd->MR_csd_callee_ptr;
	MR_deep_assert(pd != NULL);

	type_info = (MR_TypeInfo) TInfo;
	type_ctor_info = MR_TYPEINFO_GET_TYPE_CTOR_INFO(type_info);

	void_key = (void *) type_ctor_info;
	MR_search_csdlist(csdlist, prev, pd, CSN, void_key);
	MR_maybe_deep_profile_update_special_history(type_ctor_info);
	if (csdlist != NULL) {
		MR_next_call_site_dynamic = csdlist->MR_csdlist_call_site;
	} else {
		MR_CallSiteDynamic	*newcsd;

		MR_new_call_site_dynamic(newcsd);
		MR_make_and_link_csdlist(csdlist, newcsd, pd, CSN, void_key);
		MR_next_call_site_dynamic = newcsd;
	}

	MR_leave_instrumentation();
#else
	MR_fatal_error(""prepare_for_special_call: deep profiling not enabled"");
#endif
}").

:- pragma c_code(prepare_for_ho_call(CSD::in, CSN::in, Closure::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_CallSiteDynamic	*csd;
	MR_ProcDynamic		*pd;
	MR_Closure		*closure;
	MR_CallSiteDynList	*csdlist;
	void			*void_key;
#ifdef MR_DEEP_PROFILING_MOVE_TO_FRONT_LISTS
	MR_CallSiteDynList	*prev = NULL;
#endif

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	closure = (MR_Closure *) Closure;
	MR_deep_assert(csd == MR_current_call_site_dynamic);
	pd = csd->MR_csd_callee_ptr;
	MR_deep_assert(pd != NULL);

#ifdef MR_DEEP_PROFILING_KEY_USES_ID
	void_key = (void *) (closure->MR_closure_layout);
#else
	void_key = (void *) (closure->MR_closure_code);
#endif

	MR_search_csdlist(csdlist, prev, pd, CSN, void_key);
	MR_maybe_deep_profile_update_closure_history(closure);

	if (csdlist != NULL) {
		MR_next_call_site_dynamic = csdlist->MR_csdlist_call_site;
	} else {
		MR_CallSiteDynamic	*newcsd;

		MR_new_call_site_dynamic(newcsd);
		MR_make_and_link_csdlist(csdlist, newcsd, pd, CSN, void_key);
		MR_next_call_site_dynamic = newcsd;
	}

	MR_leave_instrumentation();
#else
	MR_fatal_error(""prepare_for_ho_call: deep profiling not enabled"");
#endif
}").

:- pragma c_code(prepare_for_callback(CSD::in, N::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_CallSiteDynamic	*csd;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	MR_deep_assert(csd == MR_current_call_site_dynamic);
	MR_deep_assert(csd->MR_csd_callee_ptr != NULL);

	MR_current_callback_site = (MR_CallSiteDynList **)
		&(csd->MR_csd_callee_ptr->MR_pd_call_site_ptr_ptrs[N]);
	MR_leave_instrumentation();
#else
	MR_fatal_error(""prepare_for_callback: deep profiling not enabled"");
#endif
}").

%---------------------------------------------------------------------------%
% Procedures needed for handling directly recursive procedures
%---------------------------------------------------------------------------%

:- pragma c_code(inner_call_port_code(ProcStatic::in, MiddleCSD::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifndef MR_USE_ACTIVATION_COUNTS
	MR_fatal_error(""create_proc_dynamic_inner called when not using activation counts!"");
#else
	MR_CallSiteDynamic	*csd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();

#ifdef	MR_DEEP_PROFILING_LOWLEVEL_DEBUG
	MR_print_deep_prof_vars(stdout);
#endif

	MiddleCSD = (MR_Word) MR_next_call_site_dynamic;
	MR_current_call_site_dynamic = MR_next_call_site_dynamic;
	csd = MR_current_call_site_dynamic;
	csd->MR_csd_depth_count++;
	ps = (MR_ProcStatic *) ProcStatic;

	MR_deep_assert(ps->MR_ps_outermost_activation_ptr != NULL);

	if (csd->MR_csd_callee_ptr == NULL) {
		csd->MR_csd_callee_ptr = ps->MR_ps_outermost_activation_ptr;
	}

	MR_leave_instrumentation();
#endif
#else
	MR_fatal_error(""create_proc_dynamic_inner: deep profiling not enabled"");
#endif
}").

:- pragma c_code(set_current_csd(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_current_call_site_dynamic = (MR_CallSiteDynamic *) CSD;
#else
	MR_fatal_error(""set_current_csd: deep profiling not enabled"");
#endif
}").

:- impure pred increment_activation_count(call_site_dynamic::in,
	proc_dynamic::in) is det.

:- pragma c_code(increment_activation_count(CSD::in, PD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic	*csd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	MR_deep_assert(csd == MR_current_call_site_dynamic);

	ps = csd->MR_csd_callee_ptr->MR_pd_proc_static;
	ps->MR_ps_activation_count++;
	ps->MR_ps_outermost_activation_ptr = (MR_ProcDynamic *) PD;
	MR_leave_instrumentation();
#else
	MR_fatal_error(""increment_activation_count: no activation_count"");
#endif
#else
	MR_fatal_error(""increment_activation_count: deep profiling not enabled"");
#endif
}").

:- pragma c_code(set_outermost_activation_ptr(CSD::in, Ptr::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
	MR_CallSiteDynamic	*csd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	ps = csd->MR_csd_callee_ptr->MR_pd_proc_static;
	ps->MR_ps_outermost_activation_ptr = (MR_ProcDynamic *) Ptr;
	MR_leave_instrumentation();
#endif
}").

:- pragma c_code(save_and_zero_activation_info(CSD::in, Count::out, Ptr::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic	*csd;
	MR_ProcDynamic		*pd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	pd = csd->MR_csd_callee_ptr;
	ps = pd->MR_pd_proc_static;

	Count = ps->MR_ps_activation_count;
	ps->MR_ps_activation_count = 0;
	Ptr = (MR_Word) ps->MR_ps_outermost_activation_ptr;
	ps->MR_ps_outermost_activation_ptr = NULL;
	MR_leave_instrumentation();
#else
	MR_fatal_error(""save_and_zero_activation_info: no activation_count"");
#endif
#else
	MR_fatal_error(""save_and_zero_activation_info: deep profiling not enabled"");
#endif
}").

:- pragma c_code(rezero_activation_info(CSD::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic	*csd;
	MR_ProcDynamic		*pd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	pd = csd->MR_csd_callee_ptr;
	ps = pd->MR_pd_proc_static;

	ps->MR_ps_activation_count = 0;
	ps->MR_ps_outermost_activation_ptr = NULL;
	MR_leave_instrumentation();
#else
	MR_fatal_error(""rezero_activation_info: no activation_count"");
#endif
#else
	MR_fatal_error(""rezero_activation_info: deep profiling not enabled"");
#endif
}").

:- pragma c_code(reset_activation_info(CSD::in, Count::in, Ptr::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_USE_ACTIVATION_COUNTS
	MR_CallSiteDynamic	*csd;
	MR_ProcDynamic		*pd;
	MR_ProcStatic		*ps;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	MR_deep_assert(csd == MR_current_call_site_dynamic);
	pd = csd->MR_csd_callee_ptr;
	ps = pd->MR_pd_proc_static;

	ps->MR_ps_activation_count = Count;
	ps->MR_ps_outermost_activation_ptr = (MR_ProcDynamic *) Ptr;
	MR_leave_instrumentation();
#else
	MR_fatal_error(""reset_activation_info: no activation_count"");
#endif
#else
	MR_fatal_error(""reset_activation_info: deep profiling not enabled"");
#endif
}").

:- pragma c_code(save_recursion_depth_count(CSD::in, CSN::in, Count::out),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_TAIL_RECURSION
	MR_CallSiteDynamic	*csd;
	MR_CallSiteDynamic	*inner_csd;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	inner_csd = csd->MR_csd_callee_ptr->MR_pd_call_site_ptr_ptrs[CSN];

	if (inner_csd != NULL) {
		Count = inner_csd->MR_csd_depth_count;
	} else {
		Count = 0;
	}
	MR_leave_instrumentation();
#else
	MR_fatal_error(""save_recursion_depth_count: no depth counts"");
#endif
#else
	MR_fatal_error(""save_recursion_depth_count: deep profiling not enabled"");
#endif
}").

:- pragma c_code(restore_recursion_depth_count_exit(
		CSD::in, CSN::in, OuterCount::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_TAIL_RECURSION
	MR_CallSiteDynamic	*csd;
	MR_CallSiteDynamic	*inner_csd;
	int			inner_count;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	inner_csd = csd->MR_csd_callee_ptr->MR_pd_call_site_ptr_ptrs[CSN];

	if (inner_csd != NULL) {
		inner_count = inner_csd->MR_csd_depth_count;

		inner_csd->MR_csd_own.MR_own_calls += inner_count;
		inner_csd->MR_csd_own.MR_own_exits += inner_count;

		inner_csd->MR_csd_depth_count = OuterCount;
	} else {
		MR_deep_assert(OuterCount == 0);
	}
	MR_leave_instrumentation();
#else
	MR_fatal_error(""restore_recursion_depth_count_exit: no depth counts"");
#endif
#else
	MR_fatal_error(""restore_recursion_depth_count_exit: deep profiling not enabled"");
#endif
}").

:- pragma c_code(restore_recursion_depth_count_fail(
		CSD::in, CSN::in, OuterCount::in),
		[thread_safe, will_not_call_mercury], "{
#ifdef MR_DEEP_PROFILING
#ifdef MR_DEEP_PROFILING_TAIL_RECURSION
	MR_CallSiteDynamic	*csd;
	MR_CallSiteDynamic	*inner_csd;
	int			inner_count;

	MR_enter_instrumentation();
	csd = (MR_CallSiteDynamic *) CSD;
	inner_csd = csd->MR_csd_callee_ptr->MR_pd_call_site_ptr_ptrs[CSN];

	if (inner_csd != NULL) {
		inner_count = inner_csd->MR_csd_depth_count;

		inner_csd->MR_csd_own.MR_own_calls += inner_count;
		inner_csd->MR_csd_own.MR_own_fails += inner_count;

		inner_csd->MR_csd_depth_count = OuterCount;
	} else {
		MR_deep_assert(OuterCount == 0);
	}
	MR_leave_instrumentation();
#else
	MR_fatal_error(""restore_recursion_depth_count_fail: no depth counts"");
#endif
#else
	MR_fatal_error(""restore_recursion_depth_count_fail: deep profiling not enabled"");
#endif
}").
