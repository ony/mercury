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

:- import_module array, bool, char, getopt, int, list.
:- import_module map, require, set, std_util, string.

:- type deep
	--->	deep(
			root			:: call_site_dynamic_ptr,
			call_site_dynamics	:: call_site_dynamics,
			proc_dynamics		:: proc_dynamics,
			call_site_statics	:: call_site_statics,
			proc_statics		:: proc_statics,
				% Clique information
			clique_index		:: array(clique),
			clique_members		:: clique_members,
			clique_parents		:: array(call_site_dynamic_ptr),
				% Propagated timing info
			pd_own			:: array(own_prof_info),
			pd_desc			:: array(inherit_prof_info),
			csd_desc		:: array(inherit_prof_info),
			ps_own			:: array(own_prof_info),
			ps_desc			:: array(inherit_prof_info)
		).

:- type call_site_dynamics == array(call_site_dynamic).
:- type proc_dynamics == array(proc_dynamic).
:- type proc_statics == array(proc_static).
:- type call_site_statics == array(call_site_static).

:- type call_site_dynamic_ptr
	--->	call_site_dynamic_ptr(int).

:- type call_site_dynamic
	--->	call_site_dynamic(
			proc_dynamic_ptr,
			own_prof_info
		).

:- type proc_dynamic_ptr
	--->	proc_dynamic_ptr(int).

:- type call_site_ref
	--->	normal(call_site_dynamic_ptr)
	;	multi(array(call_site_dynamic_ptr))
	.

:- type proc_dynamic
	--->	proc_dynamic(
			proc_static_ptr,
			array(call_site_ref)
		).

:- type proc_static_ptr
	--->	proc_static_ptr(int).

:- type proc_static
	--->	proc_static(
			string,	% procedure ID
			array(call_site_static_ptr)
		).

:- type call_site_static_ptr
	--->	call_site_static_ptr(int).

:- type call_site_static
	--->	call_site_static(
			call_site_kind,
			string	% goal path
		).

:- type call_site_kind
	--->	normal
	;	higher_order
	;	typeclass_method
	;	callback
	.

:- type own_prof_info
	--->	zdet(int)		% calls == exits, quanta == 0
	;	det(int, int)		% calls == exits, quanta
	;	all(int, int, int, int, int, int)
	.				% calls, exits, fails, redos,
					%	quanta, memory

:- type inherit_prof_info
	--->	inherit_prof_info(
			int, 		% quanta
			int 		% memory
		).

:- type ptr ---> ptr(int).
:- type clique ---> clique(int).
:- type clique_members == array([proc_dynamic_ptr]).

:- type globals == (univ -> univ).
:- typeclass global(T1, T2) where [].

:- type option
	--->	help
		% Input options
	;	file
	
		% Output generation options
	;	depth

		% Output formats
	;	flat
	;	gprof
	%;	browse
	;	dot
	;	dump
	;	html
	;	server
	.

:- type options ---> options.
:- type option_table ---> options(option_table(option)).
:- instance global(options, option_table) where [].

:- type [A|B] == list(A).
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
	write_string(StdErr, "Reading graph data...\n"),
	{ get_global(Globals0, options) = options(Options) },
	( { lookup(Options, file, maybe_string(yes(FileName0))) } ->
		{ FileName = FileName0 }
	;
		{ FileName = "Deep.data" }
	),
	read_call_graph(FileName, Res),
	write_string(StdErr, "Done.\n"),
	io__report_stats,
	(
		{ Res = ok(Deep0) },
		write_string(StdErr, "Merging cycles in the graph.\n"),
		merge_cliques(Deep0, Deep),
		write_string(StdErr, "Done.\n"),
		{ foldl(sum_all_csds, Deep ^ call_site_dynamics, 0, Total) },
		format(StdErr, "Total quanta %d\n", [i(Total)]),
		main3(Globals0, Deep)
	;
		{ Res = error(Err) },
		format(StdErr, "%s\n", [s(Err)])
	).

:- pred sum_all_csds(int::in, call_site_dynamic::in, int::in, int::out) is det.

sum_all_csds(_, call_site_dynamic(_, OwnPI), Sum0, Sum0 + quanta(OwnPI)).

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
	( { search(Options, server, bool(yes)) } ->
		server(Globals, Deep)
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

%------------------------------------------------------------------------------%

:- pred merge_cliques(deep, deep, io__state, io__state).
:- mode merge_cliques(in, out, di, uo) is det.

merge_cliques(Deep0, Deep) -->
	stderr_stream(StdErr),
	io__report_stats,
	format(StdErr, "  Constructing graph...\n", []),
	make_graph(Deep0, Graph),
	format(StdErr, "  Done.\n", []),
	io__report_stats,
	format(StdErr, "  Performing topological sort...\n", []),
	{ atsort(Graph, CliqueList0) },
	format(StdErr, "  Done.\n", []),
	io__report_stats,

		% Turn each of the sets into a list.
		% (We use foldl here because the list may be very
		% long and map runs out of stack space, and we
		% want the final list in reverse order anyway.)
	{ foldl((pred(Set::in, L0::in, L::out) is det :-
		set__to_sorted_list(Set, List0),
		map((pred(PDI::in, PDPtr::out) is det :-
			PDPtr = proc_dynamic_ptr(PDI)
		), List0, List),
		L = [List|L0]
	), CliqueList0, [], CliqueList) },
		% It's actually more convenient to have the list in
		% reverse order so that foldl works from the bottom
		% of the tsort to the top, so that we can use it to
		% do the propagation simply.
	{ Cliques = array(CliqueList) },

	format(StdErr, "  Constructing indexes...\n", []),
	flush_output(StdErr),
	{ array__max(Deep0^proc_dynamics, PDMax) },
	{ NPDs = PDMax + 1 },
	{ init(NPDs, clique(-1), CliqueIndex0) },

		% For each clique, add entries in an array
		% that maps from each clique member (ProcDynamic)
		% back to the clique to which it belongs.
	{ foldl((pred(CliqueN::in, CliqueMembers::in,
				I0::array_di, I::array_uo) is det :-
		lfoldl((pred(X::in, I1::array_di, I2::array_uo) is det :-
			X = proc_dynamic_ptr(Y),
			array__set(I1, Y, clique(CliqueN), I2)
		), CliqueMembers, I0, I)
	), Cliques, CliqueIndex0, CliqueIndex) },

		% For each CallSiteDynamic pointer, if it points to
		% a ProcDynamic which is in a different clique to
		% the one from which the CallSiteDynamic's parent
		% came, then this CallSiteDynamic is the entry to
		% the [lower] clique. We need to compute this information
		% so that we can print clique-based timing summaries in
		% the browser.
	{ array__max(Cliques, CliqueMax) },
	{ NCliques = CliqueMax + 1 },
	{ init(NCliques, call_site_dynamic_ptr(-1), CliqueParents0) },
	{ foldl((pred(PPDI1::in, PClique::in,
			C1::array_di, C2::array_uo) is det :-
	    ( PPDI1 > 0 ->
		call_sites(Deep0, proc_dynamic_ptr(PPDI1), CSDPtrs),
		lfoldl((pred(CCSDPtr::in, C3::array_di, C4::array_uo) is det :-
			CCSDPtr = call_site_dynamic_ptr(CCSDI),
			( CCSDI > 0 ->
				lookup(Deep0^call_site_dynamics, CCSDI, CCSD),
				CCSD = call_site_dynamic(CPDPtr, _),
				CPDPtr = proc_dynamic_ptr(CPDI),
				( CPDI > 0 ->
				    lookup(CliqueIndex, CPDI, CClique),
				    ( CClique \= PClique ->
				    	CClique = clique(CN),
					set(C3, CN, CCSDPtr, C4)
				    ;
					C4 = C3
				    )
				;
				    C4 = C3
				)
			;
				C4 = C3
			)
		), CSDPtrs, C1, C2)
	    ;
	    	error("emit nasal daemons")
	    )
	), CliqueIndex, CliqueParents0, CliqueParents1) },
	{ Deep0^root = call_site_dynamic_ptr(RootI) },
	{ lookup(Deep0^call_site_dynamics, RootI, RootCSD) },
	{ RootCSD = call_site_dynamic(RootPD, _) },
	{ RootPD = proc_dynamic_ptr(RootPDI) },
	{ lookup(CliqueIndex, RootPDI, clique(RootCliqueN)) },
	{ set(CliqueParents1, RootCliqueN, Deep0^root, CliqueParents) },

	format(StdErr, "  Done.\n", []),
	io__report_stats,

	format(StdErr, "  Propagating time up call graph...\n", []),

	{ init(NPDs, zero_own_prof_info, PDOwn0) },
	{ foldl((pred(_::in, CSD::in, PDO0::array_di, PDO::array_uo)
								is det :-
		CSD = call_site_dynamic(PDPtr, PI),
		PDPtr = proc_dynamic_ptr(PDI),
		( PDI > 0 ->
			lookup(PDO0, PDI, OwnPI0),
			Calls = calls(PI) + calls(OwnPI0),
			Exits = exits(PI) + exits(OwnPI0),
			Fails = fails(PI) + fails(OwnPI0),
			Redos = redos(PI) + redos(OwnPI0),
			Quanta = quanta(PI) + quanta(OwnPI0),
			Memory = memory(PI) + memory(OwnPI0),
			OwnPI = cons_profile([Calls, Exits,
					Fails, Redos, Quanta, Memory]),
			set(PDO0, PDI, OwnPI, PDO)
		;
			PDO = PDO0
		)
	), Deep0^call_site_dynamics, PDOwn0, PDOwn) },
	
	{ array__max(Deep0^call_site_dynamics, CSDMax) },
	{ NCSDs = CSDMax + 1 },
	{ init(NPDs, zero_inherit_prof_info, PDDesc0) },
	{ init(NCSDs, zero_inherit_prof_info, CSDDesc0) },

	{ array__max(Deep0^proc_statics, PSMax) },
	{ NPSs = PSMax + 1 },
	{ init(NPSs, zero_own_prof_info, PSOwn0) },
	{ init(NPSs, zero_inherit_prof_info, PSDesc0) },

	{ Deep1 = ((((((((Deep0
		^ clique_index := CliqueIndex)
		^ clique_members := Cliques)
		^ clique_parents := CliqueParents)
		^ pd_own := PDOwn)
		^ pd_desc := PDDesc0)
		^ csd_desc := CSDDesc0)
		^ ps_own := PSOwn0)
		^ ps_desc := PSDesc0) },

	{ foldl(propagate_to_clique, Cliques, Deep1, Deep2) },

	{ foldl(summarize_proc_dynamic, Deep2 ^ proc_dynamics, Deep2, Deep) },

	format(StdErr, "  Done.\n", []),
	io__report_stats.

:- pred summarize_proc_dynamic(int::in, proc_dynamic::in, deep::in, deep::out)
	is det.

summarize_proc_dynamic(PDI, PD, Deep0, Deep) :-
	PD = proc_dynamic(PSPtr, _),
	PSPtr = proc_static_ptr(PSI),
	( PSI > 0 ->
		PDOwn = Deep0 ^ pd_own,
		PDDesc = Deep0 ^ pd_desc,
		lookup(PDOwn, PDI, PDOwnPI),
		lookup(PDDesc, PDI, PDDescPI),

		PSOwn0 = Deep0 ^ ps_own,
		PSDesc0 = Deep0 ^ ps_desc,
		lookup(PSOwn0, PSI, PSOwnPI0),
		lookup(PSDesc0, PSI, PSDescPI0),

		add_own_to_own(PDOwnPI, PSOwnPI0) = PSOwnPI,
		add_inherit_to_inherit(PDDescPI, PSDescPI0) = PSDescPI,
		set(u(PSOwn0), PSI, PSOwnPI, PSOwn),
		set(u(PSDesc0), PSI, PSDescPI, PSDesc),

		Deep = (Deep0 ^ ps_own := PSOwn) ^ ps_desc := PSDesc
	;
		error("emit nasal devils")
	).

:- pred propagate_to_clique(int::in, list(proc_dynamic_ptr)::in,
	deep::in, deep::out) is det.

propagate_to_clique(CliqueNumber, Members, Deep0, Deep) :-
	lookup(Deep0 ^ clique_parents, CliqueNumber, ParentCSDPtr),
	ParentCSDPtr = call_site_dynamic_ptr(ParentCSDI),
	foldl(propagate_to_proc_dynamic(CliqueNumber, Members, ParentCSDPtr),
		Members, Deep0, Deep1),
	lookup(Deep1 ^ call_site_dynamics, ParentCSDI, ParentCSD),
	ParentCSD = call_site_dynamic(_, ParentOwnPI),
	lookup(Deep1 ^ csd_desc, ParentCSDI, CliqueTotal0),
	subtract_own_from_inherit(ParentOwnPI, CliqueTotal0) = CliqueTotal,
	set(u(Deep1 ^ csd_desc), ParentCSDI, CliqueTotal, CSDDesc),
	Deep = Deep1 ^ csd_desc := CSDDesc.

:- pred propagate_to_proc_dynamic(int::in, list(proc_dynamic_ptr)::in,
	call_site_dynamic_ptr::in, proc_dynamic_ptr::in, deep::in, deep::out)
	is det.

propagate_to_proc_dynamic(CliqueNumber, Members, ParentCSDPtr, PDPtr,
		Deep0, Deep) :-
	call_sites(Deep0, PDPtr, CSDPtrs),
	foldl(propagate_to_call_site(CliqueNumber, PDPtr, Members),
		CSDPtrs, Deep0, Deep1),
	ParentCSDPtr = call_site_dynamic_ptr(ParentCSDI),
	lookup(Deep1 ^ csd_desc, ParentCSDI, CliqueTotal0),
	PDPtr = proc_dynamic_ptr(PDI),
	lookup(Deep1 ^ pd_desc, PDI, DescPI),
	lookup(Deep1 ^ pd_own, PDI, OwnPI),
	add_own_to_inherit(OwnPI, CliqueTotal0) = CliqueTotal1,
	add_inherit_to_inherit(DescPI, CliqueTotal1) = CliqueTotal,
	set(u(Deep1 ^ csd_desc), ParentCSDI, CliqueTotal, CSDDesc),
	Deep = Deep1 ^ csd_desc := CSDDesc.

:- pred propagate_to_call_site(int::in, proc_dynamic_ptr::in,
	list(proc_dynamic_ptr)::in, call_site_dynamic_ptr::in,
	deep::in, deep::out) is det.

propagate_to_call_site(CliqueNumber, PDPtr, Members, CSDPtr, Deep0, Deep) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	( CSDI > 0 ->
		lookup(Deep0 ^ call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(CPDPtr, CPI),
		CPDPtr = proc_dynamic_ptr(CPDI),
		( CPDI > 0 ->
			lookup(Deep0 ^ clique_index, CPDI,
				clique(ChildCliqueNumber)),
			( ChildCliqueNumber \= CliqueNumber ->
				require_isnt(is_member(CPDPtr, Members),
					"nasal gremlims"),
				PDPtr = proc_dynamic_ptr(PDI),
				lookup(Deep0 ^ pd_desc, PDI, PDTotal0),
				lookup(Deep0 ^ csd_desc, CSDI, CDesc),
				add_own_to_inherit(CPI, PDTotal0) = PDTotal1,
				add_inherit_to_inherit(CDesc, PDTotal1)
					= PDTotal,
				set(u(Deep0 ^ pd_desc), PDI, PDTotal, PDDesc),
				Deep = Deep0 ^ pd_desc := PDDesc
			;
				require(is_member(CPDPtr, Members),
					"nasal demons"),
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

:- func add_inherit_to_inherit(inherit_prof_info, inherit_prof_info)
	= inherit_prof_info.

add_inherit_to_inherit(PI1, PI2) = SumPI :-
	Quanta = inherit_quanta(PI1) + inherit_quanta(PI2),
	Memory = inherit_memory(PI1) + inherit_memory(PI2),
	SumPI = inherit_prof_info(Quanta, Memory).

:- func add_own_to_inherit(own_prof_info, inherit_prof_info)
	= inherit_prof_info.

add_own_to_inherit(PI1, PI2) = SumPI :-
	Quanta = quanta(PI1) + inherit_quanta(PI2),
	Memory = memory(PI1) + inherit_memory(PI2),
	SumPI = inherit_prof_info(Quanta, Memory).

:- func subtract_own_from_inherit(own_prof_info, inherit_prof_info)
	= inherit_prof_info.

subtract_own_from_inherit(PI1, PI2) = SumPI :-
	Quanta = inherit_quanta(PI2) - quanta(PI1),
	Memory = inherit_memory(PI2) - memory(PI1),
	SumPI = inherit_prof_info(Quanta, Memory).

:- func add_inherit_to_own(inherit_prof_info, own_prof_info) = own_prof_info.

add_inherit_to_own(PI1, PI2) = SumPI :-
	Calls = calls(PI2),
	Exits = exits(PI2),
	Fails = fails(PI2),
	Redos = redos(PI2),
	Quanta = inherit_quanta(PI1) + quanta(PI2),
	Memory = inherit_memory(PI1) + memory(PI2),
	SumPI = cons_profile([Calls, Exits, Fails, Redos, Quanta, Memory]).

:- func add_own_to_own(own_prof_info, own_prof_info) = own_prof_info.

add_own_to_own(PI1, PI2) = SumPI :-
	Calls = calls(PI1) + calls(PI2),
	Exits = exits(PI1) + exits(PI2),
	Fails = fails(PI1) + fails(PI2),
	Redos = redos(PI1) + redos(PI2),
	Quanta = quanta(PI1) + quanta(PI2),
	Memory = memory(PI1) + memory(PI2),
	SumPI = cons_profile([Calls, Exits, Fails, Redos, Quanta, Memory]).

:- pred mlookup(array(T), int, T, string).
:- mode mlookup(in, in, out, in) is det.
:- mode mlookup(array_ui, in, out, in) is det.

mlookup(A, I, T, S) :-
	array__max(A, M),
	( I >= 0, I =< M ->
		lookup(A, I, T)
	;
		format("!(0 <= %d <= %d): %s", [i(I), i(M), s(S)], Msg),
		error(Msg)
	).

:- pred call_sites(deep, proc_dynamic_ptr, [call_site_dynamic_ptr]).
:- mode call_sites(in, in, out) is det.

call_sites(Deep, PDPtr, CSDPtrs) :-
	( PDPtr = proc_dynamic_ptr(PDI), PDI > 0 ->
		lookup(Deep ^ proc_dynamics, PDI, PD),
		PD = proc_dynamic(_PSPtr, Refs),
		array__to_list(Refs, RefList),
		foldl((pred(Ref::in, CSDPtrs0::in, CSDPtrs1::out) is det :-
		    (
		    	Ref = normal(CSDPtr),
		    	CSDPtr = call_site_dynamic_ptr(CSDI),
			( CSDI > 0 ->
				CSDPtrs1 = [CSDPtr|CSDPtrs0]
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
			append(PtrList1, CSDPtrs0, CSDPtrs1)
		    )
		), RefList, [], CSDPtrs)
	;
		CSDPtrs = []
	).

:- pred kids(deep, array(clique), proc_dynamic_ptr, [clique]).
:- mode kids(in, in, in, out) is det.

kids(Deep, Index, PDPtr, Kids) :-
	( PDPtr = proc_dynamic_ptr(PDI), PDI > 0 ->
		lookup(Deep^proc_dynamics, PDI, PD),
		PD = proc_dynamic(_PSPtr, Refs),
		solutions((pred(Kid::out) is nondet :-
		    array__to_list(Refs, RefList),
		    member(Ref, RefList),
		    (
		    	Ref = normal(CSDPtr),
		    	CSDPtr = call_site_dynamic_ptr(CSDI),
			CSDI > 0,
			lookup(Deep^call_site_dynamics, CSDI, CSD),
			CSD = call_site_dynamic(CPDPtr, _Prof),
			CPDPtr = proc_dynamic_ptr(CPDI),
			CPDI > 0,
		    	lookup(Index, CPDI, Kid)
		    ;
		    	Ref = multi(PtrArray),
		    	array__to_list(PtrArray, PtrList),
		    	member(CSDPtr, PtrList),
		    	CSDPtr = call_site_dynamic_ptr(CSDI),
			CSDI > 0,
			lookup(Deep^call_site_dynamics, CSDI, CSD),
			CSD = call_site_dynamic(CPDPtr, _Prof),
			CPDPtr = proc_dynamic_ptr(CPDI),
			CPDI > 0,
		    	lookup(Index, CPDI, Kid)
		    )
		), Kids)
	;
		Kids = []
	).

:- pred make_graph(deep, graph, io__state, io__state).
:- mode make_graph(in, out, di, uo) is det.

make_graph(Deep, Graph) -->
	{ init(Graph0) },
	foldl2((pred(PDI::in, PD::in, G1::in, G2::out, di, uo) is det -->
		{ From = PDI },
	        { PD = proc_dynamic(_ProcStatic, CallSiteRefArray) },
	        { array__to_list(CallSiteRefArray, CallSiteRefList) },
	        foldl2((pred(CSR::in, G5::in, G6::out, di, uo) is det -->
		    (
			{ CSR = normal(call_site_dynamic_ptr(CSDI)) },
			( { CSDI > 0 } ->
				{ lookup(Deep^call_site_dynamics, CSDI, CSD) },
				{ CSD = call_site_dynamic(CPDPtr, _) },
				{ CPDPtr = proc_dynamic_ptr(To) },
				{ add_arc(G5, From, To, G6) }
			;
				{ G6 = G5 }
			)
		    ;
			{ CSR = multi(CallSiteArray) },
			{ array__to_list(CallSiteArray, CallSites) },
			foldl2((pred(CSDPtr1::in, G7::in, G8::out,
					di, uo) is det -->
			    { CSDPtr1 = call_site_dynamic_ptr(CSDI) },
			    ( { CSDI > 0 } ->
			    	{ lookup(Deep^call_site_dynamics, CSDI, CSD) },
			       	{ CSD = call_site_dynamic(CPDPtr, _) },
			    	{ CPDPtr = proc_dynamic_ptr(To) },
			    	{ add_arc(G7, From, To, G8) }
			    ;
			    	{ G8 = G7 }
			    )
			), CallSites, G5, G6)
		    )
	        ), CallSiteRefList, G1, G2)
	), Deep^proc_dynamics, Graph0, Graph).

:- pred foldl(pred(int, T, U, U), array(T), U, U).
:- mode foldl(pred(in, in, in, out) is det, in, in, out) is det.
:- mode foldl(pred(in, in, di, uo) is det, in, di, uo) is det.
:- mode foldl(pred(in, in, array_di, array_uo) is det, in,
		array_di, array_uo) is det.

foldl(P, A, U0, U) :-
	array__max(A, Max),
	foldl(1, Max, P, A, U0, U).

:- pred foldl(int, int, pred(int, T, U, U), array(T), U, U).
:- mode foldl(in, in, pred(in, in, in, out) is det, in, in, out) is det.
:- mode foldl(in, in, pred(in, in, di, uo) is det, in, di, uo) is det.
:- mode foldl(in, in, pred(in, in, array_di, array_uo) is det, in,
		array_di, array_uo) is det.

foldl(N, Max, P, A, U0, U) :-
	( N =< Max ->
		lookup(A, N, E),
		call(P, N, E, U0, U1),
		foldl(N + 1, Max, P, A, U1, U)
	;
		U = U0
	).

:- pred foldl2(pred(int, T, U, U, V, V), array(T), U, U, V, V).
:- mode foldl2(pred(in, in, in, out, di, uo) is det, in, in, out, di, uo)
		is det.

foldl2(P, A, U0, U, V0, V) :-
	array__max(A, Max),
	foldl2(1, Max, P, A, U0, U, V0, V).

:- pred foldl2(int, int, pred(int, T, U, U, V, V), array(T), U, U, V, V).
:- mode foldl2(in, in, pred(in, in, in, out, di, uo) is det, in,
		in, out, di, uo) is det.

foldl2(N, Max, P, A, U0, U, V0, V) :-
	( N =< Max ->
		lookup(A, N, E),
		call(P, N, E, U0, U1, V0, V1),
		foldl2(N + 1, Max, P, A, U1, U, V1, V)
	;
		U = U0,
		V = V0
	).

:- pred lfoldl(pred(T, array(U), array(U)), [T], array(U), array(U)).
:- mode lfoldl(pred(in, array_di, array_uo) is det, in,
		array_di, array_uo) is det.

lfoldl(_, []) --> [].
lfoldl(P, [X|Xs]) -->
	call(P, X),
	lfoldl(P, Xs).

%------------------------------------------------------------------------------%

:- func calls(own_prof_info) = int.
:- func exits(own_prof_info) = int.
:- func fails(own_prof_info) = int.
:- func redos(own_prof_info) = int.
:- func quanta(own_prof_info) = int.
:- func memory(own_prof_info) = int.

calls(zdet(Calls)) = Calls.
exits(zdet(Calls)) = Calls.
fails(zdet(_)) = 0.
redos(zdet(_)) = 0.
quanta(zdet(_)) = 0.
memory(zdet(_)) = 0.

calls(det(Calls, _)) = Calls.
exits(det(Calls, _)) = Calls.
fails(det(_, _)) = 0.
redos(det(_, _)) = 0.
quanta(det(_, Quanta)) = Quanta.
memory(det(_, _)) = 0.

calls(all(Calls, _, _, _, _, _)) = Calls.
exits(all(_, Exits, _, _, _, _)) = Exits.
fails(all(_, _, Fails, _, _, _)) = Fails.
redos(all(_, _, _, Redos, _, _)) = Redos.
quanta(all(_, _, _, _, Quanta, _)) = Quanta.
memory(all(_, _, _, _, _, Memory)) = Memory.

:- func zero_own_prof_info = own_prof_info.

zero_own_prof_info = zdet(0).

:- func inherit_quanta(inherit_prof_info) = int.
:- func inherit_memory(inherit_prof_info) = int.

inherit_quanta(inherit_prof_info(Quanta, _)) = Quanta.
inherit_memory(inherit_prof_info(_, Memory)) = Memory.

:- func zero_inherit_prof_info = inherit_prof_info.

zero_inherit_prof_info = inherit_prof_info(0, 0).

%------------------------------------------------------------------------------%

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
short('f',	file).
short('S',	server).

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
long("file",	file).
long("server",	server).

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
defaults0(file,		maybe_string(no)).
defaults0(server,	bool(no)).

:- func (get_global(globals, Key) = Value) <= global(Key, Value).

get_global(Globs, Key) = Value :-
	( search(Globs, univ(Key), ValueUniv) ->
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
	set(Globs0, univ(Key), univ(Value), Globs).
