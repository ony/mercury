%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module deep.

:- interface.

:- import_module io.

:- pred main(io__state, io__state).
:- mode main(di, uo) is det.

:- implementation.

:- import_module measurements.
:- import_module array, bool, char, getopt, int, list, assoc_list.
:- import_module map, require, set, std_util, string.

:- type initial_deep --->
	initial_deep(
		init_root		:: call_site_dynamic_ptr,
			% The main arrays, each indexed by own xxx_ptr int
		init_call_site_dynamics	:: call_site_dynamics,
		init_proc_dynamics	:: proc_dynamics,
		init_call_site_statics	:: call_site_statics,
		init_proc_statics	:: proc_statics
	).

:- type deep --->
	deep(
		root			:: call_site_dynamic_ptr,
			% The main arrays, each indexed by own xxx_ptr int
		call_site_dynamics	:: call_site_dynamics,
		proc_dynamics		:: proc_dynamics,
		call_site_statics	:: call_site_statics,
		proc_statics		:: proc_statics,
			% Clique information
		clique_index		:: array(clique_ptr),
					   % index: proc_dynamic_ptr int
		clique_members		:: array(list(proc_dynamic_ptr)),
					   % index: clique_ptr int
		clique_parents		:: array(call_site_dynamic_ptr),
					   % index: clique_ptr int
		clique_maybe_child	:: array(maybe(clique_ptr)),
					   % index: call_site_dynamic_ptr int
			% Reverse links
		proc_callers		:: array(list(call_site_dynamic_ptr)),
					   % index: proc_static_ptr int
		call_site_static_map	:: call_site_static_map,
					   % index: call_site_dynamic_ptr int
		call_site_calls		:: array(map(proc_static_ptr,
						list(call_site_dynamic_ptr))),
					   % index: call_site_static_ptr int
			% Propagated timing info
		pd_own			:: array(own_prof_info),
		pd_desc			:: array(inherit_prof_info),
		csd_desc		:: array(inherit_prof_info),
		ps_own			:: array(own_prof_info),
		ps_desc			:: array(inherit_prof_info),
		css_own			:: array(own_prof_info),
		css_desc		:: array(inherit_prof_info)
	).

%-----------------------------------------------------------------------------%

:- type proc_dynamics == array(proc_dynamic).
:- type proc_statics == array(proc_static).
:- type call_site_dynamics == array(call_site_dynamic).
:- type call_site_statics == array(call_site_static).
:- type call_site_static_map == array(call_site_static_ptr).

:- type proc_dynamic_ptr
	--->	proc_dynamic_ptr(int).

:- type proc_static_ptr
	--->	proc_static_ptr(int).

:- type call_site_dynamic_ptr
	--->	call_site_dynamic_ptr(int).

:- type call_site_static_ptr
	--->	call_site_static_ptr(int).

:- type clique_ptr
	--->	clique_ptr(int).

%-----------------------------------------------------------------------------%

:- type proc_dynamic
	--->	proc_dynamic(
			proc_static_ptr,
			array(call_site_array_slot)
		).

:- type proc_static
	--->	proc_static(
			proc_id,		% procedure ID
			string, 		% file name
			array(call_site_static_ptr)
		).

:- type call_site_dynamic
	--->	call_site_dynamic(
			proc_dynamic_ptr,
			own_prof_info
		).

:- type call_site_static
	--->	call_site_static(
			proc_static_ptr,	% the containing procedure
			int,			% slot number in the
						% containing procedure
			call_site_kind,
			int,			% line number
			string			% goal path
		).

%-----------------------------------------------------------------------------%

:- type pred_or_func
	--->	predicate
	;	function.

:- type proc_id
	--->	user_defined(
			user_pred_or_func	:: pred_or_func,
			user_decl_module	:: string,
			user_def_module		:: string,
			user_name		:: string,
			user_arity		:: int,
			user_mode		:: int
		)
	;	compiler_generated(
			comp_gen_type_name	:: string,
			comp_gen_type_module	:: string,
			comp_gen_def_module	:: string,
			comp_gen_pred_name	:: string,
			comp_gen_arity		:: int,
			comp_gen_mode		:: int
		).

:- type call_site_array_slot
	--->	normal(call_site_dynamic_ptr)
	;	multi(array(call_site_dynamic_ptr)).

:- type call_site_kind
	--->	normal_call
	;	special_call
	;	higher_order_call
	;	method_call
	;	callback.

:- type call_site_callees
	--->	call_site_callees(
			list(proc_dynamic_ptr)
		).

:- type call_site_caller
	--->	call_site_caller(
			call_site_static_ptr
		).

%-----------------------------------------------------------------------------%

:- type globals == (univ -> univ).
:- typeclass global(T1, T2) where [].

:- type option
	--->	help
		% Input options
	;	data_file
	
		% Output generation options
	;	depth

		% Output formats
	;	flat
	;	gprof
	%;	browse
	;	dot
	;	dump
	;	html

		% XXX
	;	server
	;	input_file
	;	output_file
	;	wait
	.

:- type options ---> options.
:- type option_table ---> options(option_table(option)).
:- instance global(options, option_table) where [].

:- type [A | B] == list(A).
:- type [] ---> [].
:- type (A -> B) == map(A, B).

%:- include_module deep:browse.
:- include_module deep:cliques.
:- include_module deep:io.
:- include_module deep:server.

%:- import_module deep:browse.
:- import_module deep:cliques.
:- import_module deep:io.
:- import_module deep:server.

main -->
%	foldl((pred(_::in, di, uo) is det -->
%		main0
%	), [1,2,3,4,5,6,7,8,9,10]).
%
%:- pred main0(io__state, io__state).
%:- mode main0(di, uo) is det.
%
%main0 -->
	{ init(Globs0) },
	io__command_line_arguments(Args0),
	{ getopt__process_options(option_ops(short, long, defaults),
		Args0, _Args, MOptions) },
	(
		{ MOptions = ok(Options) },
		{ set_global(Globs0, options, options(Options)) = Globs1 },
		main2(Globs1)
	;
		{ MOptions = error(Msg) },
		io__stderr_stream(StdErr),
		format(StdErr, "error parsing options: %s\n", [s(Msg)])
	).

:- pred main2(globals, io__state, io__state).
:- mode main2(in, di, uo) is det.

main2(Globals0) -->
	stderr_stream(StdErr),
	io__report_stats,
	write_string(StdErr, "  Reading graph data...\n"),
	{ get_global(Globals0, options) = options(Options) },
	( { map__lookup(Options, data_file, maybe_string(yes(FileName0))) } ->
		{ FileName = FileName0 }
	;
		{ FileName = "Deep.data" }
	),
	read_call_graph(FileName, Res),
	write_string(StdErr, "  Done.\n"),
	io__report_stats,
	(
		{ Res = ok(InitialDeep) },
		startup(InitialDeep, Deep),
		write_string(StdErr, "Done.\n"),
		{ array_foldl(sum_all_csd_quanta, Deep ^ call_site_dynamics,
			0, Total) },
		format(StdErr, "Total quanta %d\n", [i(Total)]),
		main3(Globals0, Deep)
	;
		{ Res = error(Err) },
		format(StdErr, "%s\n", [s(Err)])
	).

:- pred sum_all_csd_quanta(int::in, call_site_dynamic::in, int::in, int::out)
	is det.

sum_all_csd_quanta(_, call_site_dynamic(_, OwnPI), Sum0, Sum0 + quanta(OwnPI)).

:- pred main3(globals, deep, io__state, io__state).
:- mode main3(in, in, di, uo) is det.

main3(Globals, Deep) -->
	{ get_global(Globals, options) = options(Options) },
	( { search(Options, dump, bool(yes)) } ->
		dump_graph(Deep)
	;
		[]
	),
	%( { search(Options, dot, bool(yes)) } ->
	%	{ getopt__lookup_int_option(Options, depth, Depth) },
	%	deep2dot("Deep.dot", Depth, Deep)
	%;
	%	[]
	%),
	(
		{ search(Options, server, string(MachineName)) },
		{ MachineName \= "" },
		{ map__search(Options, input_file, string(InputFileName)) },
		{ map__search(Options, output_file, string(OutputFileName)) },
		{ map__search(Options, wait, int(Wait)) }
	->
		server(InputFileName, OutputFileName, Wait, MachineName, Deep)
	;
		[]
	),
	%( { search(Options, html, bool(yes)) } ->
	%	stderr_stream(StdErr),
	%	write_string(StdErr, "Generating HTML.\n"),
	%	deep2html("Deep", Deep),
	%	write_string(StdErr, "Done.\n")
	%;
	%	[]
	%),
	%( { search(Options, browse, bool(yes)) } ->
	%	browse(Globals, Deep)
	%;
	%	[]
	%).
	[].

%-----------------------------------------------------------------------------%

:- pred startup(initial_deep::in, deep::out, io__state::di, io__state::uo)
	is det.

startup(InitialDeep, Deep) -->
	stderr_stream(StdErr),

	{ InitialDeep = initial_deep(Root, CallSiteDynamics, ProcDynamics,
		CallSiteStatics0, ProcStatics) },

	format(StdErr, "  Mapping call sites to containing procedures...\n",
		[]),
	{ array_foldl(record_containing_procedures, ProcStatics,
		u(CallSiteStatics0), CallSiteStatics) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Constructing graph...\n", []),
	make_graph(InitialDeep, Graph),
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Constructing cliques...\n", []),
	{ atsort(Graph, CliqueList0) },

		% Turn each of the sets into a list.
		% (We use foldl here because the list may be very
		% long and map runs out of stack space, and we
		% want the final list in reverse order anyway.)
	{ list__foldl((pred(Set::in, L0::in, L::out) is det :-
		set__to_sorted_list(Set, List0),
		map((pred(PDI::in, PDPtr::out) is det :-
			PDPtr = proc_dynamic_ptr(PDI)
		), List0, List),
		L = [List | L0]
	), CliqueList0, [], CliqueList) },
		% It's actually more convenient to have the list in
		% reverse order so that foldl works from the bottom
		% of the tsort to the top, so that we can use it to
		% do the propagation simply.
	{ Cliques = array(CliqueList) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Constructing clique indexes...\n", []),
	flush_output(StdErr),

	{ array__max(ProcDynamics, PDMax) },
	{ NPDs = PDMax + 1 },
	{ array__max(CallSiteDynamics, CSDMax) },
	{ NCSDs = CSDMax + 1 },
	{ array__max(ProcStatics, PSMax) },
	{ NPSs = PSMax + 1 },
	{ array__max(CallSiteStatics, CSSMax) },
	{ NCSSs = CSSMax + 1 },

	{ array__init(NPDs, clique_ptr(-1), CliqueIndex0) },

		% For each clique, add entries in an array
		% that maps from each clique member (ProcDynamic)
		% back to the clique to which it belongs.
	{ array_foldl((pred(CliqueN::in, CliqueMembers::in,
				I0::array_di, I::array_uo) is det :-
		array_list_foldl((pred(X::in, I1::array_di, I2::array_uo)
				is det :-
			X = proc_dynamic_ptr(Y),
			array__set(I1, Y, clique_ptr(CliqueN), I2)
		), CliqueMembers, I0, I)
	), Cliques, CliqueIndex0, CliqueIndex) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Constructing clique parent map...\n", []),

		% For each CallSiteDynamic pointer, if it points to
		% a ProcDynamic which is in a different clique to
		% the one from which the CallSiteDynamic's parent
		% came, then this CallSiteDynamic is the entry to
		% the [lower] clique. We need to compute this information
		% so that we can print clique-based timing summaries in
		% the browser.
	{ array__max(Cliques, CliqueMax) },
	{ NCliques = CliqueMax + 1 },
	{ array__init(NCliques, call_site_dynamic_ptr(-1), CliqueParents0) },
	{ array__init(NCSDs, no, CliqueMaybeChildren0) },
	{ array_foldl2(construct_clique_parents(InitialDeep, CliqueIndex),
		CliqueIndex,
		CliqueParents0, CliqueParents1,
		CliqueMaybeChildren0, CliqueMaybeChildren1) },

	{ Root = call_site_dynamic_ptr(RootI) },
	{ array__lookup(CallSiteDynamics, RootI, RootCSD) },
	{ RootCSD = call_site_dynamic(RootPD, _) },
	{ RootPD = proc_dynamic_ptr(RootPDI) },
	{ array__lookup(CliqueIndex, RootPDI, RootCliquePtr) },
	{ RootCliquePtr = clique_ptr(RootCliqueN) },
	{ array__set(CliqueParents1, RootCliqueN, Root, CliqueParents) },
	{ array__set(CliqueMaybeChildren1, RootI, yes(RootCliquePtr),
		CliqueMaybeChildren) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Finding procedure callers...\n", []),
	{ array__init(NPSs, [], ProcCallers0) },
	{ array_foldl(construct_proc_callers(InitialDeep), CallSiteDynamics,
		ProcCallers0, ProcCallers) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Constructing call site static map...\n", []),
	{ array__init(NCSDs, call_site_static_ptr(-1), CallSiteStaticMap0) },
	{ array_foldl(construct_call_site_caller(InitialDeep), ProcDynamics,
		CallSiteStaticMap0, CallSiteStaticMap) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Finding call site calls...\n", []),
	{ array__init(NCSSs, map__init, CallSiteCalls0) },
	{ array_foldl(construct_call_site_calls(InitialDeep), ProcDynamics,
		CallSiteCalls0, CallSiteCalls) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Propagating time up call graph...\n", []),

	{ array__init(NCSDs, zero_inherit_prof_info, CSDDesc0) },
	{ array__init(NPDs, zero_own_prof_info, PDOwn0) },
	{ array_foldl(sum_call_sites_in_proc_dynamic,
		CallSiteDynamics, PDOwn0, PDOwn) },
	{ array__init(NPDs, zero_inherit_prof_info, PDDesc0) },
	{ array__init(NPSs, zero_own_prof_info, PSOwn0) },
	{ array__init(NPSs, zero_inherit_prof_info, PSDesc0) },
	{ array__init(NCSSs, zero_own_prof_info, CSSOwn0) },
	{ array__init(NCSSs, zero_inherit_prof_info, CSSDesc0) },

	{ Deep0 = deep(Root, CallSiteDynamics, ProcDynamics,
		CallSiteStatics, ProcStatics,
		CliqueIndex, Cliques, CliqueParents, CliqueMaybeChildren,
		ProcCallers, CallSiteStaticMap, CallSiteCalls,
		PDOwn, PDDesc0, CSDDesc0,
		PSOwn0, PSDesc0, CSSOwn0, CSSDesc0) },

	{ array_foldl(propagate_to_clique, Cliques, Deep0, Deep1) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Summarizing information...\n", []),
	{ summarize_proc_dynamics(Deep1, Deep2) },
	{ summarize_call_site_dynamics(Deep2, Deep) },
	format(StdErr, "  Done.\n", []),
	io__report_stats.

:- pred record_containing_procedures(int::in, proc_static::in,
	array(call_site_static)::array_di,
	array(call_site_static)::array_uo) is det.

record_containing_procedures(PSI, PS, CallSiteStatics0, CallSiteStatics) :-
	PS = proc_static(_, _, CSSPtrs),
	PSPtr = proc_static_ptr(PSI),
	array__max(CSSPtrs, MaxCS),
	record_containing_procedures_2(MaxCS, PSPtr, CSSPtrs,
		CallSiteStatics0, CallSiteStatics).

:- pred record_containing_procedures_2(int::in, proc_static_ptr::in,
	array(call_site_static_ptr)::in,
	array(call_site_static)::array_di,
	array(call_site_static)::array_uo) is det.

record_containing_procedures_2(SlotNum, PSPtr, CSSPtrs,
		CallSiteStatics0, CallSiteStatics) :-
	( SlotNum >= 0 ->
		array__lookup(CSSPtrs, SlotNum, CSSPtr),
		lookup_call_site_statics(CallSiteStatics0, CSSPtr, CSS0),
		CSS0 = call_site_static(PSPtr0, SlotNum0,
			Kind, LineNumber, GoalPath),
		require(unify(PSPtr0, proc_static_ptr(-1)),
			"record_containing_procedures_2: real proc_static_ptr"),
		require(unify(SlotNum0, -1),
			"record_containing_procedures_2: real slot_num"),
		CSS = call_site_static(PSPtr, SlotNum,
			Kind, LineNumber, GoalPath),
		update_call_site_statics(CallSiteStatics0, CSSPtr, CSS,
			CallSiteStatics1),
		record_containing_procedures_2(SlotNum - 1, PSPtr, CSSPtrs,
			CallSiteStatics1, CallSiteStatics)
	;
		CallSiteStatics = CallSiteStatics0
	).

%-----------------------------------------------------------------------------%

:- pred construct_clique_parents(initial_deep::in, array(clique_ptr)::in,
	int::in, clique_ptr::in,
	array(call_site_dynamic_ptr)::array_di,
	array(call_site_dynamic_ptr)::array_uo,
	array(maybe(clique_ptr))::array_di,
	array(maybe(clique_ptr))::array_uo) is det.

construct_clique_parents(InitialDeep, CliqueIndex, PDI, CliquePtr,
		CliqueParents0, CliqueParents,
		CliqueMaybeChildren0, CliqueMaybeChildren) :-
	( PDI > 0 ->
		flat_call_sites(InitialDeep ^ init_proc_dynamics,
			proc_dynamic_ptr(PDI), CSDPtrs),
		array_list_foldl2(
			construct_clique_parents_2(InitialDeep,
				CliqueIndex, CliquePtr),
			CSDPtrs, CliqueParents0, CliqueParents,
			CliqueMaybeChildren0, CliqueMaybeChildren)
	;
		error("emit nasal daemons")
	).

:- pred construct_clique_parents_2(initial_deep::in, array(clique_ptr)::in,
	clique_ptr::in, call_site_dynamic_ptr::in,
	array(call_site_dynamic_ptr)::array_di,
	array(call_site_dynamic_ptr)::array_uo,
	array(maybe(clique_ptr))::array_di,
	array(maybe(clique_ptr))::array_uo) is det.

construct_clique_parents_2(InitialDeep, CliqueIndex, ParentCliquePtr, CSDPtr,
		CliqueParents0, CliqueParents,
		CliqueMaybeChildren0, CliqueMaybeChildren) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	( CSDI > 0 ->
		array__lookup(InitialDeep ^ init_call_site_dynamics, CSDI,
			CSD),
		CSD = call_site_dynamic(ChildPDPtr, _),
		ChildPDPtr = proc_dynamic_ptr(ChildPDI),
		( ChildPDI > 0 ->
			array__lookup(CliqueIndex, ChildPDI, ChildCliquePtr),
			( ChildCliquePtr \= ParentCliquePtr ->
				ChildCliquePtr = clique_ptr(ChildCliqueNum),
				array__set(CliqueParents0, ChildCliqueNum,
					CSDPtr, CliqueParents),
				array__set(CliqueMaybeChildren0, CSDI,
					yes(ChildCliquePtr),
					CliqueMaybeChildren)
			;
				CliqueParents = CliqueParents0,
				CliqueMaybeChildren = CliqueMaybeChildren0
			)
		;
			CliqueParents = CliqueParents0,
			CliqueMaybeChildren = CliqueMaybeChildren0
		)
	;
		CliqueParents = CliqueParents0,
		CliqueMaybeChildren = CliqueMaybeChildren0
	).

:- pred construct_proc_callers(initial_deep::in, int::in,
	call_site_dynamic::in,
	array(list(call_site_dynamic_ptr))::array_di,
	array(list(call_site_dynamic_ptr))::array_uo) is det.

construct_proc_callers(InitialDeep, CSDI, CSD, ProcCallers0, ProcCallers) :-
	CSD = call_site_dynamic(PDPtr, _),
	PDPtr = proc_dynamic_ptr(PDI),
	( PDI > 0, array__in_bounds(InitialDeep ^ init_proc_dynamics, PDI) ->
		array__lookup(InitialDeep ^ init_proc_dynamics, PDI, PD),
		PD = proc_dynamic(PSPtr, _),
		PSPtr = proc_static_ptr(PSI),
		array__lookup(ProcCallers0, PSI, Callers0),
		Callers = [call_site_dynamic_ptr(CSDI) | Callers0],
		array__set(ProcCallers0, PSI, Callers, ProcCallers)
	;
		ProcCallers = ProcCallers0
	).

:- pred construct_call_site_caller(initial_deep::in, int::in, proc_dynamic::in,
	array(call_site_static_ptr)::array_di,
	array(call_site_static_ptr)::array_uo) is det.

construct_call_site_caller(InitialDeep, _PDI, PD,
		CallSiteStaticMap0, CallSiteStaticMap) :-
	PD = proc_dynamic(PSPtr, CSDArraySlots),
	PSPtr = proc_static_ptr(PSI),
	array__lookup(InitialDeep ^ init_proc_statics, PSI, PS),
	PS = proc_static(_, _, CSSPtrs),
	array__max(CSDArraySlots, MaxCS),
	construct_call_site_caller_2(MaxCS,
		InitialDeep ^ init_call_site_dynamics, CSSPtrs, CSDArraySlots,
		CallSiteStaticMap0, CallSiteStaticMap).

:- pred construct_call_site_caller_2(int::in, call_site_dynamics::in,
	array(call_site_static_ptr)::in,
	array(call_site_array_slot)::in,
	array(call_site_static_ptr)::array_di,
	array(call_site_static_ptr)::array_uo) is det.

construct_call_site_caller_2(SlotNum, Deep, CSSPtrs, CSDArraySlots,
		CallSiteStaticMap0, CallSiteStaticMap) :-
	( SlotNum >= 0 ->
		array__lookup(CSDArraySlots, SlotNum, CSDArraySlot),
		array__lookup(CSSPtrs, SlotNum, CSSPtr),
		(
			CSDArraySlot = normal(CSDPtr),
			construct_call_site_caller_3(Deep, CSSPtr, -1, CSDPtr,
				CallSiteStaticMap0, CallSiteStaticMap1)

		;
			CSDArraySlot = multi(CSDPtrs),
			array_foldl0(
				construct_call_site_caller_3(Deep, CSSPtr),
				CSDPtrs,
				CallSiteStaticMap0, CallSiteStaticMap1)
		),
		construct_call_site_caller_2(SlotNum - 1, Deep, CSSPtrs,
			CSDArraySlots, CallSiteStaticMap1, CallSiteStaticMap)
	;
		CallSiteStaticMap = CallSiteStaticMap0
	).

:- pred construct_call_site_caller_3(call_site_dynamics::in,
	call_site_static_ptr::in, int::in, call_site_dynamic_ptr::in,
	array(call_site_static_ptr)::array_di,
	array(call_site_static_ptr)::array_uo) is det.

construct_call_site_caller_3(CallSiteDynamics, CSSPtr, _Dummy, CSDPtr,
		CallSiteStaticMap0, CallSiteStaticMap) :-
	( valid_call_site_dynamic_ptr_raw(CallSiteDynamics, CSDPtr) ->
		update_call_site_static_map(CallSiteStaticMap0,
			CSDPtr, CSSPtr, CallSiteStaticMap)
	;
		CallSiteStaticMap = CallSiteStaticMap0
	).

:- pred construct_call_site_calls(initial_deep::in, int::in, proc_dynamic::in,
	array(map(proc_static_ptr, list(call_site_dynamic_ptr)))::array_di,
	array(map(proc_static_ptr, list(call_site_dynamic_ptr)))::array_uo)
	is det.

construct_call_site_calls(InitialDeep, _PDI, PD,
		CallSiteCalls0, CallSiteCalls) :-
	PD = proc_dynamic(PSPtr, CSDArraySlots),
	array__max(CSDArraySlots, MaxCS),
	PSPtr = proc_static_ptr(PSI),
	array__lookup(InitialDeep ^ init_proc_statics, PSI, PS),
	PS = proc_static(_, _, CSSPtrs),
	CallSiteDynamics = InitialDeep ^ init_call_site_dynamics,
	ProcDynamics = InitialDeep ^ init_proc_dynamics,
	construct_call_site_calls_2(CallSiteDynamics, ProcDynamics, MaxCS,
		CSSPtrs, CSDArraySlots, CallSiteCalls0, CallSiteCalls).

:- pred construct_call_site_calls_2(call_site_dynamics::in, proc_dynamics::in,
	int::in, array(call_site_static_ptr)::in,
	array(call_site_array_slot)::in,
	array(map(proc_static_ptr, list(call_site_dynamic_ptr)))::array_di,
	array(map(proc_static_ptr, list(call_site_dynamic_ptr)))::array_uo)
	is det.

construct_call_site_calls_2(CallSiteDynamics, ProcDynamics, SlotNum,
		CSSPtrs, CSDArraySlots, CallSiteCalls0, CallSiteCalls) :-
	( SlotNum >= 0 ->
		array__lookup(CSDArraySlots, SlotNum, CSDArraySlot),
		array__lookup(CSSPtrs, SlotNum, CSSPtr),
		(
			CSDArraySlot = normal(CSDPtr),
			construct_call_site_calls_3(CallSiteDynamics,
				ProcDynamics, CSSPtr, -1,
				CSDPtr, CallSiteCalls0, CallSiteCalls1)
		;
			CSDArraySlot = multi(CSDPtrs),
			array_foldl0(
				construct_call_site_calls_3(CallSiteDynamics,
					ProcDynamics, CSSPtr),
				CSDPtrs, CallSiteCalls0, CallSiteCalls1)
		),
		construct_call_site_calls_2(CallSiteDynamics, ProcDynamics,
			SlotNum - 1, CSSPtrs, CSDArraySlots,
			CallSiteCalls1, CallSiteCalls)
	;
		CallSiteCalls = CallSiteCalls0
	).

:- pred construct_call_site_calls_3(call_site_dynamics::in, proc_dynamics::in,
	call_site_static_ptr::in, int::in, call_site_dynamic_ptr::in,
	array(map(proc_static_ptr, list(call_site_dynamic_ptr)))::array_di,
	array(map(proc_static_ptr, list(call_site_dynamic_ptr)))::array_uo)
	is det.

construct_call_site_calls_3(CallSiteDynamics, ProcDynamics, CSSPtr,
		_Dummy, CSDPtr, CallSiteCalls0, CallSiteCalls) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	( CSDI > 0 ->
		array__lookup(CallSiteDynamics, CSDI, CSD),
		CSD = call_site_dynamic(PDPtr, _),
		PDPtr = proc_dynamic_ptr(PDI),
		array__lookup(ProcDynamics, PDI, PD),
		PD = proc_dynamic(PSPtr, _),

		CSSPtr = call_site_static_ptr(CSSI),
		array__lookup(CallSiteCalls0, CSSI, CallMap0),
		( map__search(CallMap0, PSPtr, CallList0) ->
			CallList = [CSDPtr | CallList0],
			map__det_update(CallMap0, PSPtr, CallList, CallMap)
		;
			CallList = [CSDPtr],
			map__det_insert(CallMap0, PSPtr, CallList, CallMap)
		),
		array__set(CallSiteCalls0, CSSI, CallMap, CallSiteCalls)
	;
		CallSiteCalls = CallSiteCalls0
	).

:- pred sum_call_sites_in_proc_dynamic(int::in, call_site_dynamic::in,
	array(own_prof_info)::array_di, array(own_prof_info)::array_uo) is det.

sum_call_sites_in_proc_dynamic(_, CSD, PDO0, PDO) :-
	CSD = call_site_dynamic(PDPtr, PI),
	PDPtr = proc_dynamic_ptr(PDI),
	( PDI > 0 ->
		array__lookup(PDO0, PDI, OwnPI0),
		OwnPI = add_own_to_own(PI, OwnPI0),
		array__set(PDO0, PDI, OwnPI, PDO)
	;
		PDO = PDO0
	).

:- pred summarize_proc_dynamics(deep::in, deep::out) is det.

summarize_proc_dynamics(Deep0, Deep) :-
	PSOwn0 = Deep0 ^ ps_own,
	PSDesc0 = Deep0 ^ ps_desc,
	array_foldl2(summarize_proc_dynamic(Deep0 ^ pd_own, Deep0 ^ pd_desc),
		Deep0 ^ proc_dynamics,
		copy(PSOwn0), PSOwn, copy(PSDesc0), PSDesc),
	Deep = ((Deep0
		^ ps_own := PSOwn)
		^ ps_desc := PSDesc).

:- pred summarize_proc_dynamic(array(own_prof_info)::in,
	array(inherit_prof_info)::in, int::in, proc_dynamic::in,
	array(own_prof_info)::array_di, array(own_prof_info)::array_uo,
	array(inherit_prof_info)::array_di, array(inherit_prof_info)::array_uo)
	is det.

summarize_proc_dynamic(PDOwn, PDDesc, PDI, PD,
		PSOwn0, PSOwn, PSDesc0, PSDesc) :-
	PD = proc_dynamic(PSPtr, _),
	PSPtr = proc_static_ptr(PSI),
	( PSI > 0 ->
		array__lookup(PDOwn, PDI, PDOwnPI),
		array__lookup(PDDesc, PDI, PDDescPI),

		array__lookup(PSOwn0, PSI, PSOwnPI0),
		array__lookup(PSDesc0, PSI, PSDescPI0),

		add_own_to_own(PDOwnPI, PSOwnPI0) = PSOwnPI,
		add_inherit_to_inherit(PDDescPI, PSDescPI0) = PSDescPI,
		array__set(u(PSOwn0), PSI, PSOwnPI, PSOwn),
		array__set(u(PSDesc0), PSI, PSDescPI, PSDesc)
	;
		error("emit nasal devils")
	).

:- pred summarize_call_site_dynamics(deep::in, deep::out) is det.

summarize_call_site_dynamics(Deep0, Deep) :-
	CSSOwn0 = Deep0 ^ css_own,
	CSSDesc0 = Deep0 ^ css_desc,
	array_foldl2(summarize_call_site_dynamic(Deep0 ^ root,
		Deep0 ^ call_site_static_map, Deep0 ^ csd_desc),
		Deep0 ^ call_site_dynamics,
		copy(CSSOwn0), CSSOwn, copy(CSSDesc0), CSSDesc),
	Deep = ((Deep0
		^ css_own := CSSOwn)
		^ css_desc := CSSDesc).

:- pred summarize_call_site_dynamic(call_site_dynamic_ptr::in,
	call_site_static_map::in, array(inherit_prof_info)::in,
	int::in, call_site_dynamic::in,
	array(own_prof_info)::array_di, array(own_prof_info)::array_uo,
	array(inherit_prof_info)::array_di, array(inherit_prof_info)::array_uo)
	is det.

summarize_call_site_dynamic(Root, CallSiteStaticMap, CSDDescs, CSDI, CSD,
		CSSOwn0, CSSOwn, CSSDesc0, CSSDesc) :-
	( call_site_dynamic_ptr(CSDI) \= Root ->
		CSDPtr = call_site_dynamic_ptr(CSDI),
		lookup_call_site_static_map(CallSiteStaticMap, CSDPtr, CSSPtr),
		CSSPtr = call_site_static_ptr(CSSI),
		( CSSI > 0 ->
			CSD = call_site_dynamic(_, CSDOwnPI),
			array__lookup(CSDDescs, CSDI, CSDDescPI),

			array__lookup(CSSOwn0, CSSI, CSSOwnPI0),
			array__lookup(CSSDesc0, CSSI, CSSDescPI0),

			add_own_to_own(CSDOwnPI, CSSOwnPI0)
				= CSSOwnPI,
			add_inherit_to_inherit(CSDDescPI, CSSDescPI0)
				= CSSDescPI,
			array__set(u(CSSOwn0), CSSI, CSSOwnPI, CSSOwn),
			array__set(u(CSSDesc0), CSSI, CSSDescPI, CSSDesc)
		;
			error("emit nasal gorgons")
		)
    	;
		% There is no CSS for root.
		% XXX There probably should be!
		CSSOwn = CSSOwn0,
		CSSDesc = CSSDesc0
	).

:- pred propagate_to_clique(int::in, list(proc_dynamic_ptr)::in,
	deep::in, deep::out) is det.

propagate_to_clique(CliqueNumber, Members, Deep0, Deep) :-
	array__lookup(Deep0 ^ clique_parents, CliqueNumber, ParentCSDPtr),
	ParentCSDPtr = call_site_dynamic_ptr(ParentCSDI),
	list__foldl(propagate_to_proc_dynamic(CliqueNumber, ParentCSDPtr),
		Members, Deep0, Deep1),
	array__lookup(Deep1 ^ call_site_dynamics, ParentCSDI, ParentCSD),
	ParentCSD = call_site_dynamic(_, ParentOwnPI),
	array__lookup(Deep1 ^ csd_desc, ParentCSDI, CliqueTotal0),
	subtract_own_from_inherit(ParentOwnPI, CliqueTotal0) = CliqueTotal,
	array__set(u(Deep1 ^ csd_desc), ParentCSDI, CliqueTotal, CSDDesc),
	Deep = Deep1 ^ csd_desc := CSDDesc.

:- pred propagate_to_proc_dynamic(int::in, call_site_dynamic_ptr::in,
		proc_dynamic_ptr::in, deep::in, deep::out) is det.

propagate_to_proc_dynamic(CliqueNumber, ParentCSDPtr, PDPtr,
		Deep0, Deep) :-
	flat_call_sites(Deep0 ^ proc_dynamics, PDPtr, CSDPtrs),
	list__foldl(propagate_to_call_site(CliqueNumber, PDPtr),
		CSDPtrs, Deep0, Deep1),
	ParentCSDPtr = call_site_dynamic_ptr(ParentCSDI),
	array__lookup(Deep1 ^ csd_desc, ParentCSDI, CliqueTotal0),
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(Deep1 ^ pd_desc, PDI, DescPI),
	array__lookup(Deep1 ^ pd_own, PDI, OwnPI),
	add_own_to_inherit(OwnPI, CliqueTotal0) = CliqueTotal1,
	add_inherit_to_inherit(DescPI, CliqueTotal1) = CliqueTotal,
	array__set(u(Deep1 ^ csd_desc), ParentCSDI, CliqueTotal, CSDDesc),
	Deep = Deep1 ^ csd_desc := CSDDesc.

:- pred propagate_to_call_site(int::in, proc_dynamic_ptr::in,
		call_site_dynamic_ptr::in, deep::in, deep::out) is det.

propagate_to_call_site(CliqueNumber, PDPtr, CSDPtr, Deep0, Deep) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	( CSDI > 0 ->
		array__lookup(Deep0 ^ call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(CPDPtr, CPI),
		CPDPtr = proc_dynamic_ptr(CPDI),
		( CPDI > 0 ->
			array__lookup(Deep0 ^ clique_index, CPDI,
				clique_ptr(ChildCliqueNumber)),
			( ChildCliqueNumber \= CliqueNumber ->
				PDPtr = proc_dynamic_ptr(PDI),
				array__lookup(Deep0 ^ pd_desc, PDI, PDTotal0),
				array__lookup(Deep0 ^ csd_desc, CSDI, CDesc),
				add_own_to_inherit(CPI, PDTotal0) = PDTotal1,
				add_inherit_to_inherit(CDesc, PDTotal1)
					= PDTotal,
				array__set(u(Deep0 ^ pd_desc), PDI, PDTotal,
					PDDesc),
				Deep = Deep0 ^ pd_desc := PDDesc
			;
				Deep = Deep0
			)
		;
			Deep = Deep0
		)
	;
		Deep = Deep0
	).

:- pred require_isnt(pred, string).
:- mode require_isnt((pred) is semidet, in) is det.

require_isnt(Goal, Message) :-
	( call(Goal) ->
		error(Message)
	;
		true
	).

:- pred is_member(T::in, list(T)::in) is semidet.

is_member(Elem, List) :-
	member(Elem, List).

:- pred mlookup(array(T), int, T, string).
:- mode mlookup(in, in, out, in) is det.
:- mode mlookup(array_ui, in, out, in) is det.

mlookup(A, I, T, S) :-
	array__max(A, M),
	( I >= 0, I =< M ->
		array__lookup(A, I, T)
	;
		format("!(0 <= %d <= %d): %s", [i(I), i(M), s(S)], Msg),
		error(Msg)
	).

:- pred child_call_sites(proc_dynamics::in, proc_statics::in,
	proc_dynamic_ptr::in,
	assoc_list(call_site_static_ptr, call_site_array_slot)::out) is det.

child_call_sites(ProcDynamics, ProcStatics, PDPtr, PairedSlots) :-
	PDPtr = proc_dynamic_ptr(PDI),
	% require(array__in_bounds(ProcDynamics, PDI),
	% 	"child_call_sites: PDI not in range"),
	array__lookup(ProcDynamics, PDI, PD),
	PD = proc_dynamic(PSPtr, CSDArray),
	PSPtr = proc_static_ptr(PSI),
	% require(array__in_bounds(ProcStatics, PSI),
	% 	"child_call_sites: PDI not in range"),
	array__lookup(ProcStatics, PSI, PS),
	PS = proc_static(_, _, CSSArray),
	array__to_list(CSDArray, CSDSlots),
	array__to_list(CSSArray, CSSSlots),
	assoc_list__from_corresponding_lists(CSSSlots, CSDSlots, PairedSlots).

:- pred flat_call_sites(proc_dynamics::in, proc_dynamic_ptr::in,
	list(call_site_dynamic_ptr)::out) is det.

flat_call_sites(ProcDynamics, PDPtr, CSDPtrs) :-
	( PDPtr = proc_dynamic_ptr(PDI), PDI > 0 ->
		array__lookup(ProcDynamics, PDI, PD),
		PD = proc_dynamic(_PSPtr, Refs),
		array__to_list(Refs, RefList),
		list__foldl((pred(Ref::in, CSDPtrs0::in, CSDPtrs1::out)
			is det :-
		    (
		    	Ref = normal(CSDPtr),
		    	CSDPtr = call_site_dynamic_ptr(CSDI),
			( CSDI > 0 ->
				CSDPtrs1 = [[CSDPtr] | CSDPtrs0]
			;
				CSDPtrs1 = CSDPtrs0
			)
		    ;
		    	Ref = multi(PtrArray),
		    	array__to_list(PtrArray, PtrList0),
		    	filter((pred(CSDPtr::in) is semidet :-
				CSDPtr = call_site_dynamic_ptr(CSDI),
				CSDI > 0
			), PtrList0, PtrList1),
			CSDPtrs1 = [PtrList1 | CSDPtrs0]
		    )
		), RefList, [], CSDPtrsList0),
		reverse(CSDPtrsList0, CSDPtrsList),
		condense(CSDPtrsList, CSDPtrs)
	;
		CSDPtrs = []
	).

% :- pred kids(deep::in, array(clique_ptr)::in, proc_dynamic_ptr::in,	
% 	list(clique_ptr)::out) is det.
% 
% kids(Deep, Index, PDPtr, Kids) :-
% 	( PDPtr = proc_dynamic_ptr(PDI), PDI > 0 ->
% 		array__lookup(Deep ^ proc_dynamics, PDI, PD),
% 		PD = proc_dynamic(_PSPtr, Refs),
% 		solutions((pred(Kid::out) is nondet :-
% 		    array__to_list(Refs, RefList),
% 		    member(Ref, RefList),
% 		    (
% 		    	Ref = normal(CSDPtr),
% 		    	CSDPtr = call_site_dynamic_ptr(CSDI),
% 			CSDI > 0,
% 			array__lookup(Deep ^ call_site_dynamics, CSDI, CSD),
% 			CSD = call_site_dynamic(CPDPtr, _Prof),
% 			CPDPtr = proc_dynamic_ptr(CPDI),
% 			CPDI > 0,
% 		    	array__lookup(Index, CPDI, Kid)
% 		    ;
% 		    	Ref = multi(PtrArray),
% 		    	array__to_list(PtrArray, PtrList),
% 		    	member(CSDPtr, PtrList),
% 		    	CSDPtr = call_site_dynamic_ptr(CSDI),
% 			CSDI > 0,
% 			array__lookup(Deep ^ call_site_dynamics, CSDI, CSD),
% 			CSD = call_site_dynamic(CPDPtr, _Prof),
% 			CPDPtr = proc_dynamic_ptr(CPDI),
% 			CPDI > 0,
% 		    	array__lookup(Index, CPDI, Kid)
% 		    )
% 		), Kids)
% 	;
% 		Kids = []
% 	).

:- pred make_graph(initial_deep::in, graph::out,
	io__state::di, io__state::uo) is det.

make_graph(InitialDeep, Graph) -->
	{ init(Graph0) },
	array_foldl2((pred(PDI::in, PD::in, G1::in, G2::out, di, uo) is det -->
		{ From = PDI },
	        { PD = proc_dynamic(_ProcStatic, CallSiteRefArray) },
	        { array__to_list(CallSiteRefArray, CallSiteRefList) },
	        list__foldl2((pred(CSR::in, G5::in, G6::out, di, uo) is det -->
		    (
			{ CSR = normal(call_site_dynamic_ptr(CSDI)) },
			( { CSDI > 0 } ->
				{ array__lookup(
					InitialDeep ^ init_call_site_dynamics,
					CSDI, CSD) },
				{ CSD = call_site_dynamic(CPDPtr, _) },
				{ CPDPtr = proc_dynamic_ptr(To) },
				{ add_arc(G5, From, To, G6) }
			;
				{ G6 = G5 }
			)
		    ;
			{ CSR = multi(CallSiteArray) },
			{ array__to_list(CallSiteArray, CallSites) },
			list__foldl2((pred(CSDPtr1::in, G7::in, G8::out,
					di, uo) is det -->
			    { CSDPtr1 = call_site_dynamic_ptr(CSDI) },
			    ( { CSDI > 0 } ->
			    	{ array__lookup(
					InitialDeep ^ init_call_site_dynamics,
					CSDI, CSD) },
			       	{ CSD = call_site_dynamic(CPDPtr, _) },
			    	{ CPDPtr = proc_dynamic_ptr(To) },
			    	{ add_arc(G7, From, To, G8) }
			    ;
			    	{ G8 = G7 }
			    )
			), CallSites, G5, G6)
		    )
	        ), CallSiteRefList, G1, G2)
	), InitialDeep ^ init_proc_dynamics, Graph0, Graph).

%-----------------------------------------------------------------------------%

:- func dummy_proc_id = proc_id.

dummy_proc_id = user_defined(predicate, "unknown", "unknown", "unknown",
	-1, -1).

:- func main_parent_proc_id = proc_id.

main_parent_proc_id = user_defined(predicate, "mercury_runtime",
	"mercury_runtime", "main_parent", 0, 0).

:- func proc_id_to_string(proc_id) = string.

proc_id_to_string(compiler_generated(TypeName, TypeModule, _DefModule,
		PredName, _Arity, _Mode)) =
	string__append_list([PredName, " for ", TypeModule, ":", TypeName]).
proc_id_to_string(user_defined(PredOrFunc, DeclModule, _DefModule,
		Name, Arity, Mode)) =
	string__append_list([DeclModule, ":", Name,
		"/", string__int_to_string(Arity),
		( PredOrFunc = function -> "+1" ; "" ),
		"-", string__int_to_string(Mode)]).

%-----------------------------------------------------------------------------%

:- pred valid_clique_ptr(deep::in, clique_ptr::in) is semidet.

valid_clique_ptr(Deep, clique_ptr(CliqueNum)) :-
	CliqueNum > 0,
	array__in_bounds(Deep ^ clique_members, CliqueNum).

:- pred valid_proc_dynamic_ptr(deep::in, proc_dynamic_ptr::in) is semidet.

valid_proc_dynamic_ptr(Deep, proc_dynamic_ptr(PDI)) :-
	PDI > 0,
	array__in_bounds(Deep ^ proc_dynamics, PDI).

:- pred valid_proc_static_ptr(deep::in, proc_static_ptr::in) is semidet.

valid_proc_static_ptr(Deep, proc_static_ptr(PSI)) :-
	PSI > 0,
	array__in_bounds(Deep ^ proc_statics, PSI).

:- pred valid_call_site_dynamic_ptr(deep::in, call_site_dynamic_ptr::in)
	is semidet.

valid_call_site_dynamic_ptr(Deep, call_site_dynamic_ptr(CSDI)) :-
	CSDI > 0,
	array__in_bounds(Deep ^ call_site_dynamics, CSDI).

:- pred valid_call_site_static_ptr(deep::in, call_site_static_ptr::in)
	is semidet.

valid_call_site_static_ptr(Deep, call_site_static_ptr(CSSI)) :-
	CSSI > 0,
	array__in_bounds(Deep ^ call_site_statics, CSSI).

%-----------------------------------------------------------------------------%

:- pred valid_proc_dynamic_ptr_raw(proc_dynamics::in, proc_dynamic_ptr::in)
	is semidet.

valid_proc_dynamic_ptr_raw(ProcDynamics, proc_dynamic_ptr(PDI)) :-
	PDI > 0,
	array__in_bounds(ProcDynamics, PDI).

:- pred valid_proc_static_ptr_raw(proc_statics::in, proc_static_ptr::in)
	is semidet.

valid_proc_static_ptr_raw(ProcStatics, proc_static_ptr(PSI)) :-
	PSI > 0,
	array__in_bounds(ProcStatics, PSI).

:- pred valid_call_site_dynamic_ptr_raw(call_site_dynamics::in,
	call_site_dynamic_ptr::in) is semidet.

valid_call_site_dynamic_ptr_raw(CallSiteDynamics, call_site_dynamic_ptr(CSDI)) :-
	CSDI > 0,
	array__in_bounds(CallSiteDynamics, CSDI).

:- pred valid_call_site_static_ptr_raw(call_site_statics::in,
	call_site_static_ptr::in) is semidet.

valid_call_site_static_ptr_raw(CallSiteStatics, call_site_static_ptr(CSSI)) :-
	CSSI > 0,
	array__in_bounds(CallSiteStatics, CSSI).

%-----------------------------------------------------------------------------%

:- pred lookup_call_site_dynamics(call_site_dynamics::in,
	call_site_dynamic_ptr::in, call_site_dynamic::out) is det.

lookup_call_site_dynamics(CallSiteDynamics, CSDPtr, CSD) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(CallSiteDynamics, CSDI, CSD).

:- pred lookup_call_site_statics(call_site_statics::in,
	call_site_static_ptr::in, call_site_static::out) is det.

lookup_call_site_statics(CallSiteStatics, CSSPtr, CSS) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(CallSiteStatics, CSSI, CSS).

:- pred lookup_proc_dynamics(proc_dynamics::in,
	proc_dynamic_ptr::in, proc_dynamic::out) is det.

lookup_proc_dynamics(ProcDynamics, PDPtr, PD) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__lookup(ProcDynamics, PDI, PD).

:- pred lookup_proc_statics(proc_statics::in,
	proc_static_ptr::in, proc_static::out) is det.

lookup_proc_statics(ProcStatics, PSPtr, PS) :-
	PSPtr = proc_static_ptr(PSI),
	array__lookup(ProcStatics, PSI, PS).

:- pred lookup_call_site_static_map(call_site_static_map::in,
	call_site_dynamic_ptr::in, call_site_static_ptr::out) is det.

lookup_call_site_static_map(CallSiteStaticMap, CSDPtr, CSSPtr) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(CallSiteStaticMap, CSDI, CSSPtr).

%-----------------------------------------------------------------------------%

:- pred update_call_site_dynamics(call_site_dynamics::array_di,
	call_site_dynamic_ptr::in, call_site_dynamic::in,
	call_site_dynamics::array_uo) is det.

update_call_site_dynamics(CallSiteDynamics0, CSDPtr, CSD, CallSiteDynamics) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__set(CallSiteDynamics0, CSDI, CSD, CallSiteDynamics).

:- pred update_call_site_statics(call_site_statics::array_di,
	call_site_static_ptr::in, call_site_static::in,
	call_site_statics::array_uo) is det.

update_call_site_statics(CallSiteStatics0, CSSPtr, CSS, CallSiteStatics) :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__set(CallSiteStatics0, CSSI, CSS, CallSiteStatics).

:- pred update_proc_dynamics(proc_dynamics::array_di,
	proc_dynamic_ptr::in, proc_dynamic::in,
	proc_dynamics::array_uo) is det.

update_proc_dynamics(ProcDynamics0, PDPtr, PD, ProcDynamics) :-
	PDPtr = proc_dynamic_ptr(PDI),
	array__set(ProcDynamics0, PDI, PD, ProcDynamics).

:- pred update_proc_statics(proc_statics::array_di,
	proc_static_ptr::in, proc_static::in, proc_statics::array_uo) is det.

update_proc_statics(ProcStatics0, PSPtr, PS, ProcStatics) :-
	PSPtr = proc_static_ptr(PSI),
	array__set(ProcStatics0, PSI, PS, ProcStatics).

:- pred update_call_site_static_map(call_site_static_map::array_di,
	call_site_dynamic_ptr::in, call_site_static_ptr::in,
	call_site_static_map::array_uo) is det.

update_call_site_static_map(CallSiteStaticMap0, CSDPtr, CSSPtr,
		CallSiteStaticMap) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__set(CallSiteStaticMap0, CSDI, CSSPtr, CallSiteStaticMap).

%-----------------------------------------------------------------------------%

:- pred array_foldl(pred(int, T, U, U), array(T), U, U).
:- mode array_foldl(pred(in, in, di, uo) is det, in, di, uo) is det.
:- mode array_foldl(pred(in, in, array_di, array_uo) is det, in,
	array_di, array_uo) is det.
:- mode array_foldl(pred(in, in, in, out) is det, in, in, out) is det.

array_foldl(P, A, U0, U) :-
	array__max(A, Max),
	array_foldl(1, Max, P, A, U0, U).

:- pred array_foldl0(pred(int, T, U, U), array(T), U, U).
:- mode array_foldl0(pred(in, in, di, uo) is det, in, di, uo) is det.
:- mode array_foldl0(pred(in, in, array_di, array_uo) is det, in,
	array_di, array_uo) is det.
:- mode array_foldl0(pred(in, in, in, out) is det, in, in, out) is det.

array_foldl0(P, A, U0, U) :-
	array__max(A, Max),
	array_foldl(0, Max, P, A, U0, U).

:- pred array_foldl(int, int, pred(int, T, U, U), array(T), U, U).
:- mode array_foldl(in, in, pred(in, in, di, uo) is det, in, di, uo) is det.
:- mode array_foldl(in, in, pred(in, in, array_di, array_uo) is det, in,
	array_di, array_uo) is det.
:- mode array_foldl(in, in, pred(in, in, in, out) is det, in, in, out) is det.

array_foldl(N, Max, P, A, U0, U) :-
	( N =< Max ->
		array__lookup(A, N, E),
		call(P, N, E, U0, U1),
		array_foldl(N + 1, Max, P, A, U1, U)
	;
		U = U0
	).

:- pred array_foldl2(pred(int, T, U, U, V, V), array(T), U, U, V, V).
:- mode array_foldl2(pred(in, in, di, uo, di, uo) is det, in, di, uo, di, uo)
	is det.
:- mode array_foldl2(pred(in, in, array_di, array_uo, array_di, array_uo)
	is det, in, array_di, array_uo, array_di, array_uo)
	is det.
:- mode array_foldl2(pred(in, in, in, out, di, uo) is det, in, in, out, di, uo)
	is det.

array_foldl2(P, A, U0, U, V0, V) :-
	array__max(A, Max),
	array_foldl2(1, Max, P, A, U0, U, V0, V).

:- pred array_foldl2(int, int, pred(int, T, U, U, V, V), array(T), U, U, V, V).
:- mode array_foldl2(in, in, pred(in, in, di, uo, di, uo) is det, in,
	di, uo, di, uo) is det.
:- mode array_foldl2(in, in, pred(in, in,
	array_di, array_uo, array_di, array_uo) is det, in,
	array_di, array_uo, array_di, array_uo) is det.
:- mode array_foldl2(in, in, pred(in, in, in, out, di, uo) is det, in,
	in, out, di, uo) is det.

array_foldl2(N, Max, P, A, U0, U, V0, V) :-
	( N =< Max ->
		array__lookup(A, N, E),
		call(P, N, E, U0, U1, V0, V1),
		array_foldl2(N + 1, Max, P, A, U1, U, V1, V)
	;
		U = U0,
		V = V0
	).

:- pred array_list_foldl(pred(T, array(U), array(U)), list(T),
	array(U), array(U)).
:- mode array_list_foldl(pred(in, array_di, array_uo) is det, in,
	array_di, array_uo) is det.

array_list_foldl(_, [], Acc, Acc).
array_list_foldl(P, [X | Xs], Acc0, Acc) :-
	call(P, X, Acc0, Acc1),
	array_list_foldl(P, Xs, Acc1, Acc).

:- pred array_list_foldl2(pred(T, array(U), array(U), array(V), array(V)),
	list(T), array(U), array(U), array(V), array(V)).
:- mode array_list_foldl2(pred(in, array_di, array_uo, array_di, array_uo)
	is det, in, array_di, array_uo, array_di, array_uo) is det.

array_list_foldl2(_, [], AccU, AccU, AccV, AccV).
array_list_foldl2(P, [X | Xs], AccU0, AccU, AccV0, AccV) :-
	call(P, X, AccU0, AccU1, AccV0, AccV1),
	array_list_foldl2(P, Xs, AccU1, AccU, AccV1, AccV).

%-----------------------------------------------------------------------------%

:- pred short(char, option).
:- mode short(in, out) is semidet.

short('h',	help).

short('d',	depth).

short('F',	flat).
short('g',	gprof).
%short('b',	browse).
short('D',	dot).
short('G',	dump).
short('H',	html).
short('f',	data_file).
short('S',	server).
short('I',	input_file).
short('O',	output_file).
short('W',	wait).

:- pred long(string, option).
:- mode long(in, out) is semidet.

long("help",	help).

long("depth",	depth).

long("flat",	flat).
long("gprof",	gprof).
%long("browse",	browse).
long("dot",	dot).
long("dump",	dump).
long("html",	html).
long("server",	server).
long("data-file",	data_file).
long("input-file",	input_file).
long("wait",	wait).

:- pred defaults(option, option_data).
:- mode defaults(out, out) is nondet.

defaults(Option, Data) :-
	semidet_succeed,
	defaults0(Option, Data).

:- pred defaults0(option, option_data).
:- mode defaults0(out, out) is multi.

defaults0(help,		bool(no)).

defaults0(depth,	int(1000)).

defaults0(flat,		bool(no)).
defaults0(gprof,	bool(no)).
%defaults0(browse,	bool(yes)).
defaults0(dot,		bool(no)).
defaults0(dump,		bool(no)).
defaults0(html,		bool(no)).
defaults0(data_file,	maybe_string(no)).
defaults0(server,	string("")).
defaults0(input_file,	string("/var/tmp/toDeep")).
defaults0(output_file,	string("/var/tmp/fromDeep")).
defaults0(wait,		int(0)).

:- func (get_global(globals, Key) = Value) <= global(Key, Value).

get_global(Globs, Key) = Value :-
	( map__search(Globs, univ(Key), ValueUniv) ->
		( ValueUniv = univ(Value0) ->
			Value = Value0
		;
			error("get_global: value did not have expected type")
		)
	;
		error("get_global: global not found")
	).

:- func (set_global(globals, Key, Value) = globals) <= global(Key, Value).

set_global(Globs0, Key, Value) = Globs :-
	map__set(Globs0, univ(Key), univ(Value), Globs).
