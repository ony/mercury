%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_profile
% Main authors: nancy

:- module structure_reuse__sr_profile.

:- interface.

:- import_module hlds__hlds_module.

:- import_module io, int, string. 

:- type profiling_info ---> 
		prof(
			% general counting of procedures
			procs_defined	:: int, 
			reuse_procs	:: int,
			uncond_reuse_procs :: int,
			procs_counted	:: int, 

			% only counting about exported procedures
			exported_procs  :: int,
			exported_reuse_procs :: int, 
			exported_uncond_reuse_procs ::int, 
	
			% info about the aliases	
			aliases		:: int, 
			bottom_procs	:: int,
			top_procs	:: int, 
	
			deconstructs 	:: int, 
			direct_reuses 	:: int,
			direct_conditions :: int, 	% not used 
			

			pred_calls 	:: int, 
			reuse_calls	:: int, 
			no_reuse_calls 	:: int  	
		).

:- pred init(profiling_info::out) is det.

:- pred inc_procs_defined(profiling_info::in, profiling_info::out) is det.
:- pred inc_reuse_procs(profiling_info::in, profiling_info::out) is det.
:- pred inc_uncond_reuse_procs(profiling_info::in, 
			profiling_info::out) is det.
:- pred inc_procs_counted(profiling_info::in, profiling_info::out) is det.
:- pred inc_exported_procs(profiling_info::in, profiling_info::out) is det.
:- pred inc_exported_reuse_procs(profiling_info::in, 
			profiling_info::out) is det.
:- pred inc_exported_uncond_reuse_procs(profiling_info::in, 
			profiling_info::out) is det.

:- pred inc_aliases(int::in, profiling_info::in, profiling_info::out) is det.
:- pred inc_bottom_procs(profiling_info::in, profiling_info::out) is det.
:- pred inc_top_procs(profiling_info::in, profiling_info::out) is det.
:- pred inc_deconstructs(profiling_info::in, profiling_info::out) is det.
:- pred inc_direct_reuses(profiling_info::in, profiling_info::out) is det.
:- pred inc_direct_conditions(profiling_info::in, profiling_info::out) is
det.
:- pred inc_pred_calls(profiling_info::in, profiling_info::out) is det.
:- pred inc_reuse_calls(profiling_info::in, profiling_info::out) is det.
:- pred inc_no_reuse_calls(profiling_info::in, profiling_info::out) is det.


:- pred write_profiling(string::in, profiling_info::in, module_info::in,
			io__state::di, io__state::uo) is det. 

%-----------------------------------------------------------------------------%

:- implementation. 

:- import_module hlds__hlds_out.
:- import_module hlds__hlds_pred.
:- import_module transform_hlds__dependency_graph.

:- import_module bool, relation, require, set, time, list, std_util, map. 

init(P) :- 
	P = prof(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0). 

inc_procs_defined(P0, P0 ^ procs_defined := (P0 ^ procs_defined + 1)).
inc_reuse_procs(P0, P0 ^ reuse_procs := (P0 ^ reuse_procs + 1)).
inc_uncond_reuse_procs(P0, 
		P0 ^ uncond_reuse_procs := (P0 ^ uncond_reuse_procs + 1)).
inc_procs_counted(P0, P0 ^ procs_counted := (P0 ^ procs_counted + 1)).
inc_exported_procs(P0, P0 ^ exported_procs := (P0 ^ exported_procs + 1)).
inc_exported_reuse_procs(P0, 
		P0 ^ exported_reuse_procs := (P0 ^ exported_reuse_procs + 1)).
inc_exported_uncond_reuse_procs(P0, 
	P0 ^ exported_uncond_reuse_procs 
			:= (P0 ^ exported_uncond_reuse_procs + 1)).
inc_aliases(N, P0, P0 ^ aliases := (P0 ^ aliases + N)).
inc_bottom_procs(P0, P0 ^ bottom_procs := (P0 ^ bottom_procs + 1)).
inc_top_procs(P0, P0 ^ top_procs := (P0 ^ top_procs + 1)).
inc_deconstructs(P0, P0 ^ deconstructs := (P0 ^ deconstructs + 1)).
inc_direct_reuses(P0, P0 ^ direct_reuses := (P0 ^ direct_reuses + 1)).
inc_direct_conditions(P0, P0 ^ direct_conditions := (P0 ^ direct_conditions + 1)).
inc_pred_calls(P0, P0 ^ pred_calls := (P0 ^ pred_calls + 1)).
inc_reuse_calls(P0, P0 ^ reuse_calls := (P0 ^ reuse_calls + 1)).
inc_no_reuse_calls(P0, P0 ^ no_reuse_calls := (P0 ^ no_reuse_calls + 1)). 

:- pred procs_defined(profiling_info::in, int::out) is det.
:- pred reuse_procs(profiling_info::in, int::out) is det.
:- pred uncond_reuse_procs(profiling_info::in, int::out) is det.
:- pred procs_counted(profiling_info::in, int::out) is det.
:- pred exported_procs(profiling_info::in, int::out) is det.
:- pred exported_reuse_procs(profiling_info::in, int::out) is det.
:- pred exported_uncond_reuse_procs(profiling_info::in, int::out) is det.
:- pred aliases(profiling_info::in, int::out) is det.
:- pred bottom_procs(profiling_info::in, int::out) is det.
:- pred top_procs(profiling_info::in, int::out) is det.
:- pred deconstructs(profiling_info::in, int::out) is det.
:- pred direct_reuses(profiling_info::in, int::out) is det.
:- pred direct_conditions(profiling_info::in,int::out) is det.
:- pred pred_calls(profiling_info::in, int::out) is det.
:- pred reuse_calls(profiling_info::in, int::out) is det.
:- pred no_reuse_calls(profiling_info::in, int::out) is det.


procs_defined(P0, P0 ^ procs_defined).
reuse_procs(P0, P0 ^ reuse_procs).
uncond_reuse_procs(P0, P0 ^ uncond_reuse_procs).
procs_counted(P0, P0 ^ procs_counted).
exported_procs(P0, P0 ^ exported_procs).
exported_reuse_procs(P0, P0 ^ exported_reuse_procs).
exported_uncond_reuse_procs(P0, P0 ^ exported_uncond_reuse_procs).
aliases(P0, P0 ^ aliases).
bottom_procs(P0, P0 ^ bottom_procs).
top_procs(P0, P0 ^ top_procs).
deconstructs(P0, P0 ^ deconstructs).
direct_reuses(P0, P0 ^ direct_reuses).
direct_conditions(P0, P0 ^ direct_conditions).
pred_calls(P0, P0 ^ pred_calls).
reuse_calls(P0, P0 ^ reuse_calls).
no_reuse_calls(P0, P0 ^ no_reuse_calls).

write_profiling(String, Prof, HLDS) --> 
	{ string__append(String, ".profile", String2) }, 
	io__open_output(String2, IOResult), 
	(
		{ IOResult = ok(Stream) },
		% top
		io__write_string(Stream, "/*\nProfiling output for module: "), 
		io__write_string(Stream, String), 
		io__nl(Stream),
		% date
		time__time(TimeT), 
		{ TimeS = time__ctime(TimeT) }, 
		io__write_string(Stream, "Current time: "), 
		io__write_string(Stream, TimeS), 
		io__nl(Stream), 
		io__nl(Stream), 
		io__write_string(Stream, "General info:\n"),
		write_prof_item(Stream, procs_defined, Prof, 
				"# declared procedures"), 
		write_prof_item(Stream, reuse_procs, Prof, 
				"# reuse-procedures"), 
		write_prof_item(Stream, uncond_reuse_procs, Prof, 
				"# unconditional reuse-procedures"), 
		write_prof_item(Stream, procs_counted, Prof, 
				"# procedures (total)"),
		io__write_string(Stream, "Exported info:\n"),
		write_prof_item(Stream, exported_procs, Prof, 
				"# exported procedures"),
		write_prof_item(Stream, exported_reuse_procs, Prof, 
				"# exported procedures with reuse"), 
		write_prof_item(Stream, exported_uncond_reuse_procs, Prof, 
			"# exported unconditional procedures with reuse"), 
		io__write_string(Stream, "Alias info:\n"),
		write_prof_item(Stream, aliases, Prof, 
				"# aliases over all the procedures"),
		write_prof_item(Stream, bottom_procs, Prof, 
				"# procedures with alias = bottom"), 
		write_prof_item(Stream, top_procs, Prof, 
				"# procedures with alias = top"), 
		io__write_string(Stream, "About direct reuses:\n"), 
		write_prof_item(Stream, deconstructs, Prof, 
				"# deconstructs"), 
		write_prof_item(Stream, direct_reuses, Prof, 
				"# direct reuses"),
		write_prof_item(Stream, direct_conditions, Prof, 
				"# conditions implied by direct reuses"),
		io__write_string(Stream, "About indirect reuses:\n"),
		write_prof_item(Stream, pred_calls, Prof, 
				"# procedure calls"),
		write_prof_item(Stream, reuse_calls, Prof, 
				"# calls to procedures with reuse"),
		write_prof_item(Stream, no_reuse_calls, Prof, 
				"# failed calls to procedures with reuse"),

		io__write_string(Stream, "*/\ndigraph "),
		io__write_string(Stream, String), 
		io__write_string(Stream, " {\nrankdir=LR;\n"),
		{ dependency_graph__build_dependency_graph(HLDS,
				yes, DepInfo) },
		{ hlds_dependency_info_get_dependency_graph(DepInfo,
				DepGraph) },
		{ relation__components(DepGraph, ComponentsSet) },
		{ list__filter_map(
			(pred(ComponentSet::in, Component::out) is semidet :-
				(set__singleton_set(ComponentSet, C0) ->
					relation__lookup_key(DepGraph, C0, C),
					C = proc(PredId, _ProcId),
					module_info_pred_info(HLDS,
							PredId, PredInfo),
					pred_info_import_status(PredInfo,
							ImportStatus),
					status_defined_in_this_module(
							ImportStatus, yes),
					module_info_get_special_pred_map(
							HLDS, SpecialPredMap),
					map__values(SpecialPredMap,
							SpecialPredIds),
					\+ list__member(PredId, 
							SpecialPredIds)
				;
					\+ set__singleton_set(ComponentSet, _)
				),
				Component = set__to_sorted_list(ComponentSet)
			), set__to_sorted_list(ComponentsSet), DomList0) },
		{ list__condense(DomList0, DomList1) },
		{ list__map(relation__lookup_key(DepGraph), DomList1,
				DomList) },
		
		write_graph_nodes(DomList, DepGraph,
				write_procedure_node(HLDS, Stream),
				write_procedure_link(HLDS, Stream)),

		io__write_string(Stream, "\n}\n"),

		io__close_output(Stream)
	;
		{ IOResult = error(IOError) },
		{ io__error_message(IOError, IOErrorString) }, 
		{ require__error(IOErrorString) }
	).

:- pred write_procedure_node(module_info::in, io__output_stream::in,
		pred_proc_id::in, io__state::di, io__state::uo) is det.

write_procedure_node(HLDS, Stream, PredProcId) -->
	{ module_info_structure_reuse_info(HLDS, HLDSReuseInfo) },
	{ HLDSReuseInfo = structure_reuse_info(ReuseMap) }, 
	io__set_output_stream(Stream, OldStream),
	{ PredProcId = proc(PredId, ProcId) },
	{ module_info_pred_proc_info(HLDS, PredProcId, PredInfo, ProcInfo) },
	{ proc_info_reuse_information(ProcInfo, ReuseInfo) },
	{ pred_info_import_status(PredInfo, ImportStatus) }, 

	{ 
	(
		ImportStatus = exported
	->
		Shape = "box", 
		Periferies = "2"
	;
		ImportStatus = local
	->
		Shape = "ellipse",
		Periferies = "1"
	;
		Shape = "ellipse", 
		Periferies = "2"
	), 

	(
		ReuseInfo = yes(Conds)
	->
		(
			Conds = [],
			Color = "style=filled, color=chartreuse2"
		;
			Conds = [_|_],
			Color = "style=filled, color=tomato"
		)
	;
		(
			map__contains(ReuseMap, PredProcId)
		->
			% meaning: the predproc has a reuse version
			% but is not used here. 
			Color = "style=filled, color=mistyrose"
		;
			Color = "color=black"
		)
	) },
	{ string__append_list(["[", Color,
				",shape=",Shape,
				",peripheries=", Periferies, "];\n"], 
				Options) }, 

	write_node_name(HLDS, PredId, ProcId), 

	io__write_string(Options), 

	io__set_output_stream(OldStream, _).

:- pred write_procedure_link(module_info::in, io__output_stream::in,
		pred_proc_id::in, pred_proc_id::in,
		io__state::di, io__state::uo) is det.

write_procedure_link(HLDS, Stream, Parent, Child) -->
	io__set_output_stream(Stream, OldStream),
	{ Parent = proc(ParentPredId, ParentProcId) },
	{ Child = proc(ChildPredId, ChildProcId) },

	write_node_name(HLDS, ParentPredId, ParentProcId), 
	io__write_string(" -> "),

	write_node_name(HLDS, ChildPredId, ChildProcId), 
	io__write_string(";\n"),

	io__set_output_stream(OldStream, _).
	

:- pred write_node_name(module_info::in, pred_id::in, proc_id::in, 
			io__state::di, io__state::uo) is det.
write_node_name(HLDS, PredId, ProcId) --> 
	{ pred_id_to_int(PredId, PredIdInt) }, 
	{ proc_id_to_int(ProcId, ProcIdInt) }, 
	io__write_char('"'), 
	hlds_out__write_pred_proc_id(HLDS, PredId, ProcId), 
	io__write_string("\\n"), 
	io__write_int(PredIdInt), 
	io__write_char('/'), 
	io__write_int(ProcIdInt), 
	io__write_char('"'). 
	
:- pred write_prof_item(io__output_stream, pred(profiling_info, int), 
			profiling_info, 
			string, io__state, io__state).
:- mode write_prof_item(in, pred(in, out) is det, in, in, di, uo) is det.

write_prof_item(Str, Getter, Prof, Text) --> 
	{ Getter(Prof,Count) },
	io__format(Str, "%8d  %s\n", [i(Count),s(Text)]).
		
