%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module deep:util.

:- interface.

:- pred valid_clique_ptr(deep::in, clique_ptr::in) is semidet.
:- pred valid_proc_dynamic_ptr(deep::in, proc_dynamic_ptr::in) is semidet.
:- pred valid_proc_static_ptr(deep::in, proc_static_ptr::in) is semidet.
:- pred valid_call_site_dynamic_ptr(deep::in, call_site_dynamic_ptr::in)
	is semidet.
:- pred valid_call_site_static_ptr(deep::in, call_site_static_ptr::in)
	is semidet.

:- pred valid_proc_dynamic_ptr_raw(proc_dynamics::in, proc_dynamic_ptr::in)
	is semidet.
:- pred valid_proc_static_ptr_raw(proc_statics::in, proc_static_ptr::in)
	is semidet.
:- pred valid_call_site_dynamic_ptr_raw(call_site_dynamics::in,
	call_site_dynamic_ptr::in) is semidet.
:- pred valid_call_site_static_ptr_raw(call_site_statics::in,
	call_site_static_ptr::in) is semidet.

:- pred lookup_call_site_dynamics(call_site_dynamics::in,
	call_site_dynamic_ptr::in, call_site_dynamic::out) is det.
:- pred lookup_call_site_statics(call_site_statics::in,
	call_site_static_ptr::in, call_site_static::out) is det.
:- pred lookup_proc_dynamics(proc_dynamics::in,
	proc_dynamic_ptr::in, proc_dynamic::out) is det.
:- pred lookup_proc_statics(proc_statics::in,
	proc_static_ptr::in, proc_static::out) is det.
:- pred lookup_clique_index(array(clique_ptr)::in,
	proc_dynamic_ptr::in, clique_ptr::out) is det.
:- pred lookup_clique_members(array(list(proc_dynamic_ptr))::in,
	clique_ptr::in, list(proc_dynamic_ptr)::out) is det.
:- pred lookup_clique_parents(array(call_site_dynamic_ptr)::in,
	clique_ptr::in, call_site_dynamic_ptr::out) is det.
:- pred lookup_clique_maybe_child(array(maybe(clique_ptr))::in,
	call_site_dynamic_ptr::in, maybe(clique_ptr)::out) is det.
:- pred lookup_call_site_static_map(call_site_static_map::in,
	call_site_dynamic_ptr::in, call_site_static_ptr::out) is det.

:- pred deep_lookup_call_site_dynamics(deep::in, call_site_dynamic_ptr::in,
	call_site_dynamic::out) is det.
:- pred deep_lookup_call_site_statics(deep::in, call_site_static_ptr::in,
	call_site_static::out) is det.
:- pred deep_lookup_proc_dynamics(deep::in, proc_dynamic_ptr::in,
	proc_dynamic::out) is det.
:- pred deep_lookup_proc_statics(deep::in, proc_static_ptr::in,
	proc_static::out) is det.
:- pred deep_lookup_clique_index(deep::in, proc_dynamic_ptr::in,
	clique_ptr::out) is det.
:- pred deep_lookup_clique_members(deep::in, clique_ptr::in,
	list(proc_dynamic_ptr)::out) is det.
:- pred deep_lookup_clique_parents(deep::in, clique_ptr::in,
	call_site_dynamic_ptr::out) is det.
:- pred deep_lookup_clique_maybe_child(deep::in, call_site_dynamic_ptr::in,
	maybe(clique_ptr)::out) is det.
:- pred deep_lookup_call_site_static_map(deep::in, call_site_dynamic_ptr::in,
	call_site_static_ptr::out) is det.
:- pred deep_lookup_call_site_calls(deep::in, call_site_static_ptr::in,
	map(proc_static_ptr, list(call_site_dynamic_ptr))::out) is det.
:- pred deep_lookup_proc_dynamic_sites(deep::in, proc_dynamic_ptr::in,
	array(call_site_array_slot)::out) is det.

:- pred deep_lookup_pd_own(deep::in, proc_dynamic_ptr::in,
	own_prof_info::out) is det.
:- pred deep_lookup_pd_desc(deep::in, proc_dynamic_ptr::in,
	inherit_prof_info::out) is det.
:- pred deep_lookup_csd_own(deep::in, call_site_dynamic_ptr::in,
	own_prof_info::out) is det.
:- pred deep_lookup_csd_desc(deep::in, call_site_dynamic_ptr::in,
	inherit_prof_info::out) is det.
:- pred deep_lookup_ps_own(deep::in, proc_static_ptr::in,
	own_prof_info::out) is det.
:- pred deep_lookup_ps_desc(deep::in, proc_static_ptr::in,
	inherit_prof_info::out) is det.
:- pred deep_lookup_css_own(deep::in, call_site_static_ptr::in,
	own_prof_info::out) is det.
:- pred deep_lookup_css_desc(deep::in, call_site_static_ptr::in,
	inherit_prof_info::out) is det.

:- pred update_call_site_dynamics(call_site_dynamics::array_di,
	call_site_dynamic_ptr::in, call_site_dynamic::in,
	call_site_dynamics::array_uo) is det.
:- pred update_call_site_statics(call_site_statics::array_di,
	call_site_static_ptr::in, call_site_static::in,
	call_site_statics::array_uo) is det.
:- pred update_proc_dynamics(proc_dynamics::array_di,
	proc_dynamic_ptr::in, proc_dynamic::in,
	proc_dynamics::array_uo) is det.
:- pred update_proc_statics(proc_statics::array_di,
	proc_static_ptr::in, proc_static::in, proc_statics::array_uo) is det.
:- pred update_call_site_static_map(call_site_static_map::array_di,
	call_site_dynamic_ptr::in, call_site_static_ptr::in,
	call_site_static_map::array_uo) is det.

:- pred deep_update_csd_desc(deep::in, call_site_dynamic_ptr::in,
	inherit_prof_info::in, deep::out) is det.
:- pred deep_update_pd_desc(deep::in, proc_dynamic_ptr::in,
	inherit_prof_info::in, deep::out) is det.
:- pred deep_update_pd_own(deep::in, proc_dynamic_ptr::in,
	own_prof_info::in, deep::out) is det.

:- implementation.

valid_clique_ptr(Deep, clique_ptr(CliqueNum)) :-
	CliqueNum > 0,
	array__in_bounds(Deep ^ clique_members, CliqueNum).

valid_proc_dynamic_ptr(Deep, proc_dynamic_ptr(PDI)) :-
	PDI > 0,
	array__in_bounds(Deep ^ proc_dynamics, PDI).

valid_proc_static_ptr(Deep, proc_static_ptr(PSI)) :-
	PSI > 0,
	array__in_bounds(Deep ^ proc_statics, PSI).

valid_call_site_dynamic_ptr(Deep, call_site_dynamic_ptr(CSDI)) :-
	CSDI > 0,
	array__in_bounds(Deep ^ call_site_dynamics, CSDI).

valid_call_site_static_ptr(Deep, call_site_static_ptr(CSSI)) :-
	CSSI > 0,
	array__in_bounds(Deep ^ call_site_statics, CSSI).

%-----------------------------------------------------------------------------%

valid_proc_dynamic_ptr_raw(ProcDynamics, proc_dynamic_ptr(PDI)) :-
	PDI > 0,
	array__in_bounds(ProcDynamics, PDI).

valid_proc_static_ptr_raw(ProcStatics, proc_static_ptr(PSI)) :-
	PSI > 0,
	array__in_bounds(ProcStatics, PSI).

valid_call_site_dynamic_ptr_raw(CallSiteDynamics,
		call_site_dynamic_ptr(CSDI)) :-
	CSDI > 0,
	array__in_bounds(CallSiteDynamics, CSDI).

valid_call_site_static_ptr_raw(CallSiteStatics, call_site_static_ptr(CSSI)) :-
	CSSI > 0,
	array__in_bounds(CallSiteStatics, CSSI).

%-----------------------------------------------------------------------------%

lookup_call_site_dynamics(CallSiteDynamics, CSDPtr, CSD) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(CallSiteDynamics, CSDI, CSD).

lookup_call_site_statics(CallSiteStatics, CSSPtr, CSS) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(CallSiteStatics, CSSI, CSS).

lookup_proc_dynamics(ProcDynamics, PDPtr, PD) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(ProcDynamics, PDI, PD).

lookup_proc_statics(ProcStatics, PSPtr, PS) :-
	PSPtr = proc_static_ptr(PSI),
	array__lookup(ProcStatics, PSI, PS).

lookup_clique_index(CliqueIndex, PDPtr, CliquePtr) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(CliqueIndex, PDI, CliquePtr).

lookup_clique_members(CliqueMembers, CliquePtr, PDPtrs) :-
	CliquePtr = clique_ptr(CI),
	array__lookup(CliqueMembers, CI, PDPtrs).

lookup_clique_parents(CliqueParents, CliquePtr, CSDPtr) :-
	CliquePtr = clique_ptr(CI),
	array__lookup(CliqueParents, CI, CSDPtr).

lookup_clique_maybe_child(CliqueMaybeChild, CSDPtr, MaybeCliquePtr) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(CliqueMaybeChild, CSDI, MaybeCliquePtr).

lookup_call_site_static_map(CallSiteStaticMap, CSDPtr, CSSPtr) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(CallSiteStaticMap, CSDI, CSSPtr).

%-----------------------------------------------------------------------------%

deep_lookup_call_site_dynamics(Deep, CSDPtr, CSD) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(Deep ^ call_site_dynamics, CSDI, CSD).

deep_lookup_call_site_statics(Deep, CSSPtr, CSS) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(Deep ^ call_site_statics, CSSI, CSS).

deep_lookup_proc_dynamics(Deep, PDPtr, PD) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(Deep ^ proc_dynamics, PDI, PD).

deep_lookup_proc_statics(Deep, PSPtr, PS) :-
	PSPtr = proc_static_ptr(PSI),
	array__lookup(Deep ^ proc_statics, PSI, PS).

deep_lookup_clique_index(Deep, PDPtr, CliquePtr) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(Deep ^ clique_index, PDI, CliquePtr).

deep_lookup_clique_members(Deep, CliquePtr, PDPtrs) :-
	CliquePtr = clique_ptr(CI),
	array__lookup(Deep ^ clique_members, CI, PDPtrs).

deep_lookup_clique_parents(Deep, CliquePtr, CSDPtr) :-
	CliquePtr = clique_ptr(CI),
	array__lookup(Deep ^ clique_parents, CI, CSDPtr).

deep_lookup_clique_maybe_child(Deep, CSDPtr, MaybeCliquePtr) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(Deep ^ clique_maybe_child, CSDI, MaybeCliquePtr).

deep_lookup_call_site_static_map(Deep, CSDPtr, CSSPtr) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(Deep ^ call_site_static_map, CSDI, CSSPtr).

deep_lookup_call_site_calls(Deep, CSSPtr, Calls) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(Deep ^ call_site_calls, CSSI, Calls).

deep_lookup_proc_dynamic_sites(Deep, PDPtr, PDSites) :-
	deep_lookup_proc_dynamics(Deep, PDPtr, PD),
	PDSites = PD ^ pd_sites.

%-----------------------------------------------------------------------------%

deep_lookup_pd_own(Deep, PDPtr, Own) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(Deep ^ pd_own, PDI, Own).

deep_lookup_pd_desc(Deep, PDPtr, Desc) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(Deep ^ pd_desc, PDI, Desc).

deep_lookup_csd_own(Deep, CSDPtr, Own) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(Deep ^ call_site_dynamics, CSDI, CSD),
	CSD = call_site_dynamic(_, _, Own).

deep_lookup_csd_desc(Deep, CSDPtr, Desc) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(Deep ^ csd_desc, CSDI, Desc).

deep_lookup_ps_own(Deep, PSPtr, Own) :-
	PSPtr = proc_static_ptr(PSI),
	array__lookup(Deep ^ ps_own, PSI, Own).

deep_lookup_ps_desc(Deep, PSPtr, Desc) :-
	PSPtr = proc_static_ptr(PSI),
	array__lookup(Deep ^ ps_desc, PSI, Desc).

deep_lookup_css_own(Deep, CSSPtr, Own) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(Deep ^ css_own, CSSI, Own).

deep_lookup_css_desc(Deep, CSSPtr, Desc) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(Deep ^ css_desc, CSSI, Desc).

%-----------------------------------------------------------------------------%

update_call_site_dynamics(CallSiteDynamics0, CSDPtr, CSD, CallSiteDynamics) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__set(CallSiteDynamics0, CSDI, CSD, CallSiteDynamics).

update_call_site_statics(CallSiteStatics0, CSSPtr, CSS, CallSiteStatics) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__set(CallSiteStatics0, CSSI, CSS, CallSiteStatics).

update_proc_dynamics(ProcDynamics0, PDPtr, PD, ProcDynamics) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__set(ProcDynamics0, PDI, PD, ProcDynamics).

update_proc_statics(ProcStatics0, PSPtr, PS, ProcStatics) :-
	PSPtr = proc_static_ptr(PSI),
	array__set(ProcStatics0, PSI, PS, ProcStatics).

update_call_site_static_map(CallSiteStaticMap0, CSDPtr, CSSPtr,
		CallSiteStaticMap) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__set(CallSiteStaticMap0, CSDI, CSSPtr, CallSiteStaticMap).

%-----------------------------------------------------------------------------%

deep_update_csd_desc(Deep0, CSDPtr, CSDDesc, Deep) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__set(u(Deep0 ^ csd_desc), CSDI, CSDDesc, CSDDescs),
	Deep = Deep0 ^ csd_desc := CSDDescs.

deep_update_pd_desc(Deep0, PDPtr, PDDesc, Deep) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__set(u(Deep0 ^ pd_desc), PDI, PDDesc, PDDescs),
	Deep = Deep0 ^ pd_desc := PDDescs.

deep_update_pd_own(Deep0, PDPtr, PDOwn, Deep) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__set(u(Deep0 ^ pd_own), PDI, PDOwn, PDOwns),
	Deep = Deep0 ^ pd_own := PDOwns.

%-----------------------------------------------------------------------------%
