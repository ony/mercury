%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% This module applies the deep profiling transformation described in the paper
% ``Engineering a profiler for a logic programming language'' by Thomas Conway
% and Zoltan Somogyi.
%
% Main author: conway.
%
%-----------------------------------------------------------------------------%

:- module deep_profiling.

:- interface.

:- import_module hlds_module, layout.
:- import_module io, list.

:- pred apply_deep_profiling_transformation(module_info::in, module_info::out,
	list(layout_data)::out, io__state::di, io__state::uo) is det.

%------------------------------------------------------------------------------%

:- implementation.

:- import_module (inst), instmap, hlds_data, hlds_pred, hlds_goal, prog_data.
:- import_module code_model, code_util, prog_util, type_util, mode_util.
:- import_module quantification, dependency_graph, rtti, trace.
:- import_module options, globals.
:- import_module bool, int, list, assoc_list, map, require, set.
:- import_module exception, std_util, string, term, varset.

% 
% Doing the work in procedure bodies, not at calls:
% 
% middle's new body, if det:
% middle(...) :-
% 	get_parent_cur_csd(TopCSD, MiddleCSD),
% 	create_proc_dynamic(MiddleCSD, ProcStatic),
% 	increment_activation_count(MiddleCSD),
% 	<middle's original body, with calls transformed as below>,
% 	decrement_activation_count(ProcDyn),
% 	set_cur_csd(TopCSD).
% 
% middle's new body, if semi:
% middle(...) :-
% 	get_parent_cur_csd(TopCSD, MiddleCSD),
% 	create_proc_dynamic(MiddleCSD, ProcStatic),
% 	increment_activation_count(MiddleCSD),
% 	(
% 		<middle's original body, with calls transformed as below>,
% 		decrement_activation_count(MiddleCSD),
% 		set_cur_csd(TopCSD)
% 	;
% 		decrement_activation_count(MiddleCSD),
% 		set_cur_csd(TopCSD),
% 		fail
% 	).
% 
% middle's new body, if non:
% middle(...) :-
% 	get_parent_cur_csd(TopCSD, MiddleCSD),
% 	create_proc_dynamic(MiddleCSD, ProcStatic, NewOutermostProcDyn),
% 	increment_activation_count(MiddleCSD),
% 	(
% 		<middle's original body, with calls transformed as below>,
% 		(
% 			decrement_activation_count(MiddleCSD),
% 			set_cur_csd(TopCSD)
% 		;
% 			increment_activation_count(MiddleCSD,
% 				NewOutermostProcDyn),
% 			set_cur_csd(MiddleCSD),
% 			fail
% 		)
% 	;
% 		decrement_activation_count(MiddleCSD),
% 		set_cur_csd(TopCSD),
% 		fail
% 	).
% 
% For all calls:
% 	make_new_csd_for_normal_call(MiddleCSD, N, BottomCSD),
% 	bottom(...)
% 
% 
% get_parent_cur_csd(TopCSD, MiddleCSD) executes:
% 	TopCSD = parent_call_site_dyn;
% 	MiddleCSD = current_call_site_dyn;
% make_new_csd_for_normal_call(MiddleCSD, N, BottomCSD)
% 	BottomCSD = create_and_link_new_csd(MiddleCSD, N);
% 	current_call_site_dyn = BottomCSD;
% 	parent_call_site_dyn = MiddleCSD;
% set_cur_csd(CSD) executes:
% 	current_call_site_dyn = CSD;
% 
% create_and_link_new_csd(MiddleCSD, N):
% 	creates a new CSD and returns is address
% 	after linking it to the Nth call site
% 	of the procedure called in MiddleCSD
% 

apply_deep_profiling_transformation(ModuleInfo0, ModuleInfo, ProcStatics) -->
	{ module_info_globals(ModuleInfo0, Globals) },
	{ globals__lookup_bool_option(Globals, deep_profile_tail_recursion,
		TailRecursion) },
	(
		{ TailRecursion = yes },
		{ apply_tail_recursion_transformation(ModuleInfo0,
			ModuleInfo1) }
	;
		{ TailRecursion = no },
		{ ModuleInfo1 = ModuleInfo0 }
	),
	{ module_info_predids(ModuleInfo1, PredIds) },
	{ module_info_get_predicate_table(ModuleInfo1, PredTable0) },
	{ predicate_table_get_preds(PredTable0, PredMap0) },
	{ list__foldl2(transform_predicate(ModuleInfo1),
		PredIds, PredMap0, PredMap, [], MProcStatics) },
		% Remove any duplicates that resulted from
		% references in inner tail recursive procedures 
	{ list__filter_map((pred(MProcStatic::in, ProcStatic::out) is semidet :-
		MProcStatic = yes(ProcStatic)
	), MProcStatics, ProcStatics) },
	{ predicate_table_set_preds(PredTable0, PredMap, PredTable) },
	{ module_info_set_predicate_table(ModuleInfo1, PredTable, ModuleInfo) }.

%-----------------------------------------------------------------------------%

:- pred apply_tail_recursion_transformation(module_info::in, module_info::out)
	is det.

apply_tail_recursion_transformation(ModuleInfo0, ModuleInfo) :-
	module_info_ensure_dependency_info(ModuleInfo0, ModuleInfo1),
	module_info_dependency_info(ModuleInfo1, DepInfo),
	hlds_dependency_info_get_dependency_ordering(DepInfo, SCCs),
	list__foldl(apply_tail_recursion_to_scc, SCCs,
		ModuleInfo1, ModuleInfo).

:- pred apply_tail_recursion_to_scc(list(pred_proc_id)::in,
	module_info::in, module_info::out) is det.

apply_tail_recursion_to_scc(SCC, ModuleInfo0, ModuleInfo) :-
	% For the time being, we only look for self-tail-recursive calls.
	list__foldl(apply_tail_recursion_to_proc, SCC,
		ModuleInfo0, ModuleInfo).

:- pred apply_tail_recursion_to_proc(pred_proc_id::in,
	module_info::in, module_info::out) is det.

apply_tail_recursion_to_proc(PredProcId, ModuleInfo0, ModuleInfo) :-
	PredProcId = proc(PredId, ProcId),
	module_info_preds(ModuleInfo0, PredTable0),
	map__lookup(PredTable0, PredId, PredInfo0),
	pred_info_arg_types(PredInfo0, Types),
	pred_info_procedures(PredInfo0, ProcTable0),
	map__lookup(ProcTable0, ProcId, ProcInfo0),
	proc_info_goal(ProcInfo0, Goal0),
	proc_info_interface_determinism(ProcInfo0, Detism),
	(
		determinism_components(Detism, _CanFail, SolnCount),
		SolnCount \= at_most_many,
		proc_info_headvars(ProcInfo0, HeadVars),
		proc_info_argmodes(ProcInfo0, Modes),
		find_list_of_output_args(HeadVars, Modes, Types, ModuleInfo0,
			Outputs),
		clone_proc_id(ProcTable0, ProcId, CloneProcId),
		ClonePredProcId = proc(PredId, CloneProcId),
		ApplyInfo = apply_tail_recursion_info(ModuleInfo0,
			[PredProcId - ClonePredProcId], Detism, Outputs),
		apply_tail_recursion_to_goal(Goal0, ApplyInfo,
			Goal, no, FoundTailCall, _),
		FoundTailCall = yes
	->
		proc_info_set_goal(ProcInfo0, Goal, ProcInfo1),
		figure_out_rec_call_numbers(Goal, 0, _N, [], TailCallSites),
		OrigDeepProfileInfo = deep_profile_proc_info(
			outer_proc(ClonePredProcId),
			[visible_scc_data(PredProcId, ClonePredProcId,
				TailCallSites)]),
		CloneDeepProfileInfo = deep_profile_proc_info(
			inner_proc(PredProcId),
			[visible_scc_data(PredProcId, ClonePredProcId,
				TailCallSites)]),
		proc_info_set_maybe_deep_profile_info(ProcInfo1,
			yes(OrigDeepProfileInfo), ProcInfo),
		proc_info_set_maybe_deep_profile_info(ProcInfo1,
			yes(CloneDeepProfileInfo), CloneProcInfo),
		map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable1),
		map__det_insert(ProcTable1, CloneProcId, CloneProcInfo,
			ProcTable),
		pred_info_set_procedures(PredInfo0, ProcTable, PredInfo),
		map__det_update(PredTable0, PredId, PredInfo, PredTable),
		module_info_set_preds(ModuleInfo0, PredTable, ModuleInfo)
	;
		ModuleInfo = ModuleInfo0
	).

:- pred find_list_of_output_args(list(prog_var)::in, list(mode)::in,
	list(type)::in, module_info::in, list(prog_var)::out) is det.

find_list_of_output_args(Vars, Modes, Types, ModuleInfo, Outputs) :-
	(
		find_list_of_output_args_2(Vars, Modes, Types, ModuleInfo,
			OutputsPrime)
	->
		Outputs = OutputsPrime
	;
		error("find_list_of_output_args: list length mismatch")
	).

:- pred find_list_of_output_args_2(list(prog_var)::in, list(mode)::in,
	list(type)::in, module_info::in, list(prog_var)::out) is semidet.

find_list_of_output_args_2([], [], [], _, []).
find_list_of_output_args_2([Var | Vars], [Mode | Modes], [Type | Types],
		ModuleInfo, Outputs) :-
	find_list_of_output_args_2(Vars, Modes, Types, ModuleInfo, Outputs1),
	mode_to_arg_mode(ModuleInfo, Mode, Type, ArgMode),
	( ArgMode = top_in ->
		Outputs = Outputs1
	;
		Outputs = [Var | Outputs1]
	).

%-----------------------------------------------------------------------------%

:- type apply_tail_recursion_info
	--->	apply_tail_recursion_info(
			moduleinfo	:: module_info,
			scc_ppids	:: assoc_list(pred_proc_id),
			detism		:: determinism,
			outputs		:: list(prog_var)
		).

:- pred apply_tail_recursion_to_goal(hlds_goal::in,
	apply_tail_recursion_info::in, hlds_goal::out, bool::in, bool::out,
	maybe(list(prog_var))::out) is det.

apply_tail_recursion_to_goal(Goal0, ApplyInfo, Goal,
		FoundTailCall0, FoundTailCall, Continue) :-
	Goal0 = GoalExpr0 - GoalInfo0,
	(
		GoalExpr0 = pragma_foreign_code(_, _, _, _, _, _, _),
		Goal = Goal0,
		FoundTailCall = FoundTailCall0,
		Continue = no
	;
		GoalExpr0 = call(PredId, ProcId, Args,
			Builtin, UnifyContext, SymName),
		(
			PredProcId = proc(PredId, ProcId),
			assoc_list__search(ApplyInfo ^ scc_ppids, PredProcId,
				ClonePredProcId),
			module_info_pred_proc_info(ApplyInfo ^ moduleinfo,
				PredId, ProcId, PredInfo, ProcInfo),
			proc_info_interface_determinism(ProcInfo, CallDetism),
			CallDetism = ApplyInfo ^ detism,
			pred_info_arg_types(PredInfo, Types),
			proc_info_argmodes(ProcInfo, Modes),
			find_list_of_output_args(Args, Modes, Types,
				ApplyInfo ^ moduleinfo, CallOutputs),
			CallOutputs = ApplyInfo ^ outputs,
			Builtin = not_builtin
		->
			ClonePredProcId = proc(ClonePredId, CloneProcId),
			GoalExpr = call(ClonePredId, CloneProcId, Args,
				Builtin, UnifyContext, SymName),
			goal_info_add_feature(GoalInfo0, tailcall, GoalInfo),
			Goal = GoalExpr - GoalInfo,
			FoundTailCall = yes
		;
			Goal = Goal0,
			FoundTailCall = FoundTailCall0
		),
		Continue = no
	;
		GoalExpr0 = generic_call(_, _, _, _),
		Goal = Goal0,
		FoundTailCall = FoundTailCall0,
		Continue = no
	;
		GoalExpr0 = unify(_, _, _, Unify0, _),
		Goal = Goal0,
		FoundTailCall = FoundTailCall0,
		(
			Unify0 = assign(ToVar, FromVar)
		->
			apply_tail_recursion_process_assign(
				ApplyInfo ^ outputs, ToVar, FromVar, Outputs),
			Continue = yes(Outputs)
		;
			Continue = no
		)
	;
		GoalExpr0 = conj(Goals0),
		apply_tail_recursion_to_conj(Goals0, ApplyInfo,
			Goals, FoundTailCall0, FoundTailCall, Continue),
		GoalExpr = conj(Goals),
		Goal = GoalExpr - GoalInfo0
	;
		GoalExpr0 = disj(Goals0, SM),
		apply_tail_recursion_to_disj(Goals0, ApplyInfo,
			Goals, FoundTailCall0, FoundTailCall),
		GoalExpr = disj(Goals, SM),
		Goal = GoalExpr - GoalInfo0,
		Continue = no
	;
		GoalExpr0 = switch(Var, CanFail, Cases0, SM),
		apply_tail_recursion_to_cases(Cases0, ApplyInfo,
			Cases, FoundTailCall0, FoundTailCall),
		GoalExpr = switch(Var, CanFail, Cases, SM),
		Goal = GoalExpr - GoalInfo0,
		Continue = no
	;
		GoalExpr0 = if_then_else(Vars, Cond, Then0, Else0, SM),
		apply_tail_recursion_to_goal(Then0, ApplyInfo,
			Then, FoundTailCall0, FoundTailCall1, _),
		apply_tail_recursion_to_goal(Else0, ApplyInfo,
			Else, FoundTailCall1, FoundTailCall, _),
		GoalExpr = if_then_else(Vars, Cond, Then, Else, SM),
		Goal = GoalExpr - GoalInfo0,
		Continue = no
	;
		GoalExpr0 = par_conj(_, _),
		Goal = Goal0,
		FoundTailCall = FoundTailCall0,
		Continue = no
	;
		GoalExpr0 = some(_, _, _),
		Goal = Goal0,
		FoundTailCall = FoundTailCall0,
		Continue = no
	;
		GoalExpr0 = not(_),
		Goal = Goal0,
		FoundTailCall = FoundTailCall0,
		Continue = no
	;
		GoalExpr0 = bi_implication(_, _),
		error("bi_implication in apply_tail_recursion_to_goal")
	).

:- pred apply_tail_recursion_process_assign(list(prog_var)::in,
	prog_var::in, prog_var::in, list(prog_var)::out) is det.

apply_tail_recursion_process_assign([], _, _, []).
apply_tail_recursion_process_assign([Output0 | Outputs0], ToVar, FromVar,
		[Output | Outputs]) :-
	( ToVar = Output0 ->
		Output = FromVar
	;
		Output = Output0
	),
	apply_tail_recursion_process_assign(Outputs0, ToVar, FromVar, Outputs).

:- pred apply_tail_recursion_to_conj(list(hlds_goal)::in,
	apply_tail_recursion_info::in, list(hlds_goal)::out,
	bool::in, bool::out, maybe(list(prog_var))::out) is det.

apply_tail_recursion_to_conj([], ApplyInfo, [],
		FoundTailCall, FoundTailCall, yes(ApplyInfo ^ outputs)).
apply_tail_recursion_to_conj([Goal0 | Goals0], ApplyInfo0, [Goal | Goals],
		FoundTailCall0, FoundTailCall, Continue) :-
	apply_tail_recursion_to_conj(Goals0, ApplyInfo0, Goals,
		FoundTailCall0, FoundTailCall1, Continue1),
	(
		Continue1 = yes(Outputs),
		apply_tail_recursion_to_goal(Goal0,
			ApplyInfo0 ^ outputs := Outputs, Goal,
			FoundTailCall1, FoundTailCall, Continue)
	;
		Continue1 = no,
		Goal = Goal0,
		FoundTailCall = FoundTailCall1,
		Continue = no
	).

:- pred apply_tail_recursion_to_disj(list(hlds_goal)::in,
	apply_tail_recursion_info::in, list(hlds_goal)::out,
	bool::in, bool::out) is det.

apply_tail_recursion_to_disj([], _, [], FoundTailCall, FoundTailCall).
apply_tail_recursion_to_disj([Goal0], ApplyInfo, [Goal],
		FoundTailCall0, FoundTailCall) :-
	apply_tail_recursion_to_goal(Goal0, ApplyInfo, Goal,
		FoundTailCall0, FoundTailCall, _).
apply_tail_recursion_to_disj([Goal0 | Goals0], ApplyInfo, [Goal0 | Goals],
		FoundTailCall0, FoundTailCall) :-
	Goals0 = [_ | _],
	apply_tail_recursion_to_disj(Goals0, ApplyInfo, Goals,
		FoundTailCall0, FoundTailCall).

:- pred apply_tail_recursion_to_cases(list(case)::in,
	apply_tail_recursion_info::in, list(case)::out,
	bool::in, bool::out) is det.

apply_tail_recursion_to_cases([], _,
		[], FoundTailCall, FoundTailCall).
apply_tail_recursion_to_cases([case(ConsId, Goal0) | Cases0], ApplyInfo,
		[case(ConsId, Goal) | Cases], FoundTailCall0, FoundTailCall) :-
	apply_tail_recursion_to_goal(Goal0, ApplyInfo, Goal,
		FoundTailCall0, FoundTailCall1, _),
	apply_tail_recursion_to_cases(Cases0, ApplyInfo, Cases,
		FoundTailCall1, FoundTailCall).

%-----------------------------------------------------------------------------%

:- pred figure_out_rec_call_numbers(hlds_goal, int, int, list(int), list(int)).
:- mode figure_out_rec_call_numbers(in, in, out, in, out) is det.

figure_out_rec_call_numbers(Goal, N0, N, TailCallSites0, TailCallSites) :-
	Goal = GoalExpr - GoalInfo,
	(
		GoalExpr = pragma_foreign_code(Attrs, _, _, _, _, _, _),
		( may_call_mercury(Attrs, may_call_mercury) ->
			N = N0 + 1
		;
			N = N0
		),
		TailCallSites = TailCallSites0
	;
		GoalExpr = call(_, _, _, BuiltinState, _, _),
		goal_info_get_features(GoalInfo, Features),
		( BuiltinState \= inline_builtin ->
			N = N0 + 1
		;
			N = N0
		),
		( member(tailcall, Features) ->
			TailCallSites = [N0|TailCallSites0]
		;
			TailCallSites = TailCallSites0
		)
	;
		GoalExpr = generic_call(_, _, _, _),
		N = N0 + 1,
		TailCallSites = TailCallSites0
	;
		GoalExpr = unify(_, _, _, _, _),
		N = N0,
		TailCallSites = TailCallSites0
	;
		GoalExpr = conj(Goals),
		figure_out_rec_call_numbers_in_goal_list(Goals, N0, N,
			TailCallSites0, TailCallSites)
	;
		GoalExpr = disj(Goals, _),
		figure_out_rec_call_numbers_in_goal_list(Goals, N0, N,
			TailCallSites0, TailCallSites)
	;
		GoalExpr = switch(_, _, Cases, _),
		figure_out_rec_call_numbers_in_case_list(Cases, N0, N,
			TailCallSites0, TailCallSites)
	;
		GoalExpr = if_then_else(_, Cond, Then, Else, _),
		figure_out_rec_call_numbers(Cond, N0, N1,
			TailCallSites0, TailCallSites1),
		figure_out_rec_call_numbers(Then, N1, N2,
			TailCallSites1, TailCallSites2),
		figure_out_rec_call_numbers(Else, N2, N,
			TailCallSites2, TailCallSites)
	;
		GoalExpr = par_conj(Goals, _),
		figure_out_rec_call_numbers_in_goal_list(Goals, N0, N,
			TailCallSites0, TailCallSites)
	;
		GoalExpr = some(_, _, Goal1),
		figure_out_rec_call_numbers(Goal1, N0, N,
			TailCallSites0, TailCallSites)
	;
		GoalExpr = not(Goal1),
		figure_out_rec_call_numbers(Goal1, N0, N,
			TailCallSites0, TailCallSites)
	;
		GoalExpr = bi_implication(_, _),
		error("bi_implication in apply_tail_recursion_to_goal")
	).

:- pred figure_out_rec_call_numbers_in_goal_list(list(hlds_goal), int, int,
		list(int), list(int)).
:- mode figure_out_rec_call_numbers_in_goal_list(in, in, out, in, out) is det.

figure_out_rec_call_numbers_in_goal_list([], N, N,
		TailCallSites, TailCallSites).
figure_out_rec_call_numbers_in_goal_list([Goal|Goals], N0, N,
		TailCallSites0, TailCallSites) :-
	figure_out_rec_call_numbers(Goal, N0, N1,
		TailCallSites0, TailCallSites1),
	figure_out_rec_call_numbers_in_goal_list(Goals, N1, N,
		TailCallSites1, TailCallSites).

:- pred figure_out_rec_call_numbers_in_case_list(list(case), int, int,
		list(int), list(int)).
:- mode figure_out_rec_call_numbers_in_case_list(in, in, out, in, out) is det.

figure_out_rec_call_numbers_in_case_list([], N, N,
		TailCallSites, TailCallSites).
figure_out_rec_call_numbers_in_case_list([Case|Cases], N0, N,
		TailCallSites0, TailCallSites) :-
	Case = case(_, Goal),
	figure_out_rec_call_numbers(Goal, N0, N1,
		TailCallSites0, TailCallSites1),
	figure_out_rec_call_numbers_in_case_list(Cases, N1, N,
		TailCallSites1, TailCallSites).

%-----------------------------------------------------------------------------%

:- pred transform_predicate(module_info::in, pred_id::in,
	pred_table::in, pred_table::out,
	list(maybe(layout_data))::in, list(maybe(layout_data))::out) is det.

transform_predicate(ModuleInfo, PredId, PredMap0, PredMap,
		ProcStatics0, ProcStatics) :-
	map__lookup(PredMap0, PredId, PredInfo0),
	pred_info_non_imported_procids(PredInfo0, ProcIds),
	pred_info_procedures(PredInfo0, ProcTable0),
	list__foldl2(maybe_transform_procedure(ModuleInfo, PredId),
		ProcIds, ProcTable0, ProcTable, ProcStatics0, ProcStatics),
	pred_info_set_procedures(PredInfo0, ProcTable, PredInfo),
	map__det_update(PredMap0, PredId, PredInfo, PredMap).

:- pred maybe_transform_procedure(module_info::in, pred_id::in, proc_id::in,
	proc_table::in, proc_table::out,
	list(maybe(layout_data))::in, list(maybe(layout_data))::out) is det.

maybe_transform_procedure(ModuleInfo, PredId, ProcId, ProcTable0, ProcTable,
		ProcStatics0, ProcStatics) :-
	map__lookup(ProcTable0, ProcId, ProcInfo0),
	proc_info_goal(ProcInfo0, Goal0),
	predicate_module(ModuleInfo, PredId, PredModuleName),
	(
		(
			% XXX We need to eliminate nondet C code...
			Goal0 = pragma_foreign_code(_,_,_,_,_,_, Impl) - _,
			Impl = nondet(_, _, _, _, _, _, _, _, _)
		;
			% We don't want to transform the procedures for
			% managing the deep profiling call graph, or we'd get
			% infinite recursion.
			mercury_profiling_builtin_module(PredModuleName)
		)
	->
		ProcTable = ProcTable0,
		ProcStatics = ProcStatics0
	;
		transform_procedure2(ModuleInfo, proc(PredId, ProcId),
			ProcInfo0, ProcInfo, ProcStatics0, ProcStatics),
		map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable)
	).

:- pred transform_procedure2(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out,
	list(maybe(layout_data))::in, list(maybe(layout_data))::out) is det.

transform_procedure2(ModuleInfo, PredProcId, Proc0, Proc,
		ProcStaticList0, ProcStaticList) :-
	proc_info_get_maybe_deep_profile_info(Proc0, MRecInfo),
	proc_info_interface_code_model(Proc0, CodeModel),
	(
		CodeModel = model_det,
		( MRecInfo = yes(RecInfo), RecInfo ^ role = inner_proc(_) ->
			transform_inner_proc(ModuleInfo, PredProcId, Proc0,
				Proc, MProcStatic)
		;
			transform_det_proc(ModuleInfo, PredProcId, Proc0,
				Proc, MProcStatic)
		)
	;
		CodeModel = model_semi,
		( MRecInfo = yes(RecInfo), RecInfo ^ role = inner_proc(_) ->
			transform_inner_proc(ModuleInfo, PredProcId, Proc0,
				Proc, MProcStatic)
		;
			transform_semi_proc(ModuleInfo, PredProcId, Proc0,
				Proc, MProcStatic)
		)
	;
		CodeModel = model_non,
		transform_non_proc(ModuleInfo, PredProcId, Proc0,
			Proc, MProcStatic)
	),
	ProcStaticList = [MProcStatic | ProcStaticList0].

%-----------------------------------------------------------------------------%

:- type deep_info
	--->	deep_info(
			module_info		:: module_info,
			current_csd		:: prog_var,
			next_site_num		:: int,
			call_sites		:: list(call_site_static_data),
			vars			:: prog_varset,
			var_types		:: vartypes,
			proc_filename		:: string,
			maybe_rec_info		:: maybe(deep_profile_proc_info)
		).

:- pred transform_det_proc(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out, maybe(layout_data)::out) is det.

transform_det_proc(ModuleInfo, PredProcId, Proc0, Proc, yes(ProcStatic)) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = c_pointer_type,
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcStaticVar, Vars3),
	map__set(VarTypes2, ProcStaticVar, CPointerType, VarTypes3),
	module_info_globals(ModuleInfo, Globals),
	globals__lookup_bool_option(Globals, use_activation_counts,
		UseActivationCounts),
	(
		UseActivationCounts = no,
		varset__new_var(Vars3, ActivationPtr0, Vars5),
		map__set(VarTypes3, ActivationPtr0, CPointerType, VarTypes5),
		MActivationPtr = yes(ActivationPtr0)
	;
		UseActivationCounts = yes,
		Vars5 = Vars3,
		VarTypes5 = VarTypes3,
		MActivationPtr = no
	),
	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	proc_info_get_maybe_deep_profile_info(Proc0, MRecInfo),
	
	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0,
			[], Vars5, VarTypes5, FileName, MRecInfo),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,
	CallSites = PInfo ^ call_sites,

	(
		MRecInfo = yes(RecInfo),
		RecInfo ^ role = inner_proc(OuterPredProcId)
	->
		OuterPredProcId = proc(PredId, ProcId)
	;
		PredProcId = proc(PredId, ProcId)
	),

	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStatic = proc_static_data(RttiProcLabel, FileName, CallSites),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	(
		MActivationPtr = yes(ActivationPtr1),
		generate_call(ModuleInfo, "det_call_port_code_sr", 4,
			[ProcStaticVar, TopCSD, MiddleCSD, ActivationPtr1],
			[TopCSD, MiddleCSD, ActivationPtr1], CallPortCode),
		generate_call(ModuleInfo, "det_exit_port_code_ac", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], [], ExitPortCode)
	;
		MActivationPtr = no,
		generate_call(ModuleInfo, "det_call_port_code_ac", 3,
			[ProcStaticVar, TopCSD, MiddleCSD],
			[TopCSD, MiddleCSD], CallPortCode),
		generate_call(ModuleInfo, "det_exit_port_code_ac", 2,
			[TopCSD, MiddleCSD], [], ExitPortCode)
	),

	Goal = conj([
		BindProcStaticVarGoal,
		CallPortCode,
		TransformedGoal,
		ExitPortCode
	]) - GoalInfo0,
	proc_info_set_varset(Proc0, Vars, Proc1),
	proc_info_set_vartypes(Proc1, VarTypes, Proc2),
	proc_info_set_goal(Proc2, Goal, Proc).

:- pred transform_semi_proc(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out, maybe(layout_data)::out) is det.

transform_semi_proc(ModuleInfo, PredProcId, Proc0, Proc, yes(ProcStatic)) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = c_pointer_type,
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcStaticVar, Vars3),
	map__set(VarTypes2, ProcStaticVar, CPointerType, VarTypes3),
	module_info_globals(ModuleInfo, Globals),
	globals__lookup_bool_option(Globals, use_activation_counts,
		UseActivationCounts),
	(
		UseActivationCounts = no,
		varset__new_var(Vars3, ActivationPtr0, Vars5),
		map__set(VarTypes3, ActivationPtr0, CPointerType, VarTypes5),
		MActivationPtr = yes(ActivationPtr0)
	;
		UseActivationCounts = yes,
		Vars5 = Vars3,
		VarTypes5 = VarTypes3,
		MActivationPtr = no
	),
	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	proc_info_get_maybe_deep_profile_info(Proc0, MRecInfo),
	
	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0,
			[], Vars5, VarTypes5, FileName, MRecInfo),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,
	CallSites = PInfo ^ call_sites,

	(
		MRecInfo = yes(RecInfo),
		RecInfo ^ role = inner_proc(OuterPredProcId)
	->
		OuterPredProcId = proc(PredId, ProcId)
	;
		PredProcId = proc(PredId, ProcId)
	),

	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStatic = proc_static_data(RttiProcLabel, FileName, CallSites),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	(
		MActivationPtr = yes(ActivationPtr1),
		generate_call(ModuleInfo, "semi_call_port_code_sr", 4,
			[ProcStaticVar, TopCSD, MiddleCSD, ActivationPtr1],
			[TopCSD, MiddleCSD, ActivationPtr1], CallPortCode),
		generate_call(ModuleInfo, "semi_exit_port_code_sr", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], [], ExitPortCode),
		generate_call(ModuleInfo, "semi_fail_port_code_sr", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], no, failure,
			FailPortCode),
		NewNonlocals = list_to_set([MiddleCSD, ActivationPtr1])
	;
		MActivationPtr = no,
		generate_call(ModuleInfo, "semi_call_port_code_ac", 3,
			[ProcStaticVar, TopCSD, MiddleCSD],
			[TopCSD, MiddleCSD], CallPortCode),
		generate_call(ModuleInfo, "semi_exit_port_code_ac", 2,
			[TopCSD, MiddleCSD], [], ExitPortCode),
		generate_call(ModuleInfo, "semi_fail_port_code_ac", 2,
			[TopCSD, MiddleCSD], no, failure, FailPortCode),
		NewNonlocals = list_to_set([MiddleCSD])
	),

	ExitConjGoalInfo = goal_info_add_nonlocals_make_impure(GoalInfo0,
		NewNonlocals),

	Goal = conj([
		BindProcStaticVarGoal,
		CallPortCode,
		disj([
			conj([
				TransformedGoal,
				ExitPortCode
			]) - ExitConjGoalInfo,
			FailPortCode
		], map__init) - ExitConjGoalInfo
	]) - GoalInfo0,
	proc_info_set_varset(Proc0, Vars, Proc1),
	proc_info_set_vartypes(Proc1, VarTypes, Proc2),
	proc_info_set_goal(Proc2, Goal, Proc).

:- pred transform_non_proc(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out, maybe(layout_data)::out) is det.

transform_non_proc(ModuleInfo, PredProcId, Proc0, Proc, yes(ProcStatic)) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = c_pointer_type,
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcStaticVar, Vars3),
	map__set(VarTypes2, ProcStaticVar, CPointerType, VarTypes3),
	module_info_globals(ModuleInfo, Globals),
	globals__lookup_bool_option(Globals, use_activation_counts,
		UseActivationCounts),
	(
		UseActivationCounts = no,
		varset__new_var(Vars3, OldOutermostProcDyn0, Vars4),
		map__set(VarTypes3, OldOutermostProcDyn0, CPointerType,
			VarTypes4),
		varset__new_var(Vars4, NewOutermostProcDyn, Vars5),
		map__set(VarTypes4, NewOutermostProcDyn, CPointerType,
			VarTypes5),
		MOldActivationPtr = yes(OldOutermostProcDyn0)
	;
		UseActivationCounts = yes,
		varset__new_var(Vars3, NewOutermostProcDyn, Vars5),
		map__set(VarTypes3, NewOutermostProcDyn, CPointerType,
			VarTypes5),
		MOldActivationPtr = no
	),
	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	proc_info_get_maybe_deep_profile_info(Proc0, MRecInfo),
	
	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0,
			[], Vars5, VarTypes5, FileName, MRecInfo),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,
	CallSites = PInfo ^ call_sites,

	PredProcId = proc(PredId, ProcId),
	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStatic = proc_static_data(RttiProcLabel, FileName, CallSites),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	(
		MOldActivationPtr = yes(OldOutermostProcDyn2),
		generate_call(ModuleInfo, "non_call_port_code_sr", 5,
			[ProcStaticVar, TopCSD, MiddleCSD,
			OldOutermostProcDyn2, NewOutermostProcDyn],
			[TopCSD, MiddleCSD,
				OldOutermostProcDyn2, NewOutermostProcDyn],
			CallPortCode),
		generate_call(ModuleInfo, "non_exit_port_code_sr", 3,
			[TopCSD, MiddleCSD, OldOutermostProcDyn2], [],
			ExitPortCode),
		generate_call(ModuleInfo, "non_fail_port_code_sr", 3,
			[TopCSD, MiddleCSD, OldOutermostProcDyn2], no,
			failure, FailPortCode),
		generate_call(ModuleInfo, "non_redo_port_code_sr", 2,
			[MiddleCSD, NewOutermostProcDyn], no,
			failure, RedoPortCode),
		NewNonlocals = list_to_set(
			[TopCSD, MiddleCSD, OldOutermostProcDyn2])
	;
		MOldActivationPtr = no,
		generate_call(ModuleInfo, "non_call_port_code_ac", 4,
			[ProcStaticVar, TopCSD, MiddleCSD, NewOutermostProcDyn],
			[TopCSD, MiddleCSD, NewOutermostProcDyn],
			CallPortCode),
		generate_call(ModuleInfo, "non_exit_port_code_ac", 2,
			[TopCSD, MiddleCSD], [], ExitPortCode),
		generate_call(ModuleInfo, "non_fail_port_code_ac", 2,
			[TopCSD, MiddleCSD], no, failure, FailPortCode),
		generate_call(ModuleInfo, "non_redo_port_code_ac", 2,
			[MiddleCSD, NewOutermostProcDyn], no,
			failure, RedoPortCode),
		NewNonlocals = list_to_set([TopCSD, MiddleCSD])
	),

	ExitRedoNonLocals = set__union(NewNonlocals,
		list_to_set([NewOutermostProcDyn])),
	ExitRedoGoalInfo = impure_reachable_init_goal_info(ExitRedoNonLocals,
		multidet),

	CallExitRedoGoalInfo = goal_info_add_nonlocals_make_impure(GoalInfo0,
		ExitRedoNonLocals),

	Goal = conj([
		BindProcStaticVarGoal,
		CallPortCode,
		disj([
			conj([
				TransformedGoal,
				disj([
					ExitPortCode,
					RedoPortCode
				], map__init) - ExitRedoGoalInfo
			]) - CallExitRedoGoalInfo,
			FailPortCode
		], map__init) - CallExitRedoGoalInfo
	]) - GoalInfo0,
	proc_info_set_varset(Proc0, Vars, Proc1),
	proc_info_set_vartypes(Proc1, VarTypes, Proc2),
	proc_info_set_goal(Proc2, Goal, Proc).

:- pred transform_inner_proc(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out, maybe(layout_data)::out) is det.

transform_inner_proc(ModuleInfo, PredProcId, Proc0, Proc, no) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = c_pointer_type,
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcStaticVar, Vars3),
	map__set(VarTypes2, ProcStaticVar, CPointerType, VarTypes3),

	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	proc_info_get_maybe_deep_profile_info(Proc0, MRecInfo),
	
	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0,
			[], Vars3, VarTypes3, FileName, MRecInfo),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,

	(
		MRecInfo = yes(RecInfo),
		RecInfo ^ role = inner_proc(OuterPredProcId)
	->
		OuterPredProcId = proc(PredId, ProcId)
	;
		PredProcId = proc(PredId, ProcId)
	),

	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	generate_call(ModuleInfo, "inner_call_port_code", 2,
		[ProcStaticVar, MiddleCSD], [MiddleCSD], CallPortCode),

	Goal = conj([
		BindProcStaticVarGoal,
		CallPortCode,
		TransformedGoal
	]) - GoalInfo0,

	proc_info_set_varset(Proc0, Vars, Proc1),
	proc_info_set_vartypes(Proc1, VarTypes, Proc2),
	proc_info_set_goal(Proc2, Goal, Proc).

%-----------------------------------------------------------------------------%

:- pred transform_goal(goal_path::in, hlds_goal::in, hlds_goal::out,
	deep_info::in, deep_info::out) is det.

transform_goal(Path, conj(Goals0) - Info, conj(Goals) - Info)  -->
	transform_conj(0, Path, Goals0, Goals).

transform_goal(Path, par_conj(Goals0, SM) - Info,
		par_conj(Goals, SM) - Info) -->
	transform_conj(0, Path, Goals0, Goals).

transform_goal(Path, switch(Var, CF, Cases0, SM) - Info,
		switch(Var, CF, Cases, SM) - Info) -->
	transform_switch(list__length(Cases0), 0, Path, Cases0, Cases).

transform_goal(Path, disj(Goals0, SM) - Info, disj(Goals, SM) - Info) -->
	transform_disj(0, Path, Goals0, Goals).

transform_goal(Path, not(Goal0) - Info, not(Goal) - Info) -->
	transform_goal([neg | Path], Goal0, Goal).

transform_goal(Path, some(QVars, CR, Goal0) - Info,
		some(QVars, CR, Goal) - Info) -->
	{ Goal0 = _ - InnerInfo },
	{ goal_info_get_determinism(Info, OuterDetism) },
	{ goal_info_get_determinism(InnerInfo, InnerDetism) },
	{ InnerDetism = OuterDetism ->
		MaybeCut = no_cut
	;
		MaybeCut = cut
	},
	transform_goal([exist(MaybeCut) | Path], Goal0, Goal).

transform_goal(Path, if_then_else(IVars, Cond0, Then0, Else0, SM) - Info,
		if_then_else(IVars, Cond, Then, Else, SM) - Info) -->
	transform_goal([ite_cond | Path], Cond0, Cond),
	transform_goal([ite_then | Path], Then0, Then),
	transform_goal([ite_else | Path], Else0, Else).

transform_goal(_, bi_implication(_, _) - _, _) -->
	{ error("transform_goal/5: bi_implications should have gone by now") }.

transform_goal(Path0, Goal0 - Info0, GoalAndInfo) -->
	{ Goal0 = pragma_foreign_code(Attrs, _, _, _, _, _, _) },
	( { may_call_mercury(Attrs, may_call_mercury) } ->
		{ reverse(Path0, Path) },
		wrap_foreign_code(Path, Goal0 - Info0, GoalAndInfo)
	;
		{ GoalAndInfo = Goal0 - Info0 }
	).

transform_goal(_Path, Goal - Info, Goal - Info) -->
	{ Goal = unify(_, _, _, _, _) }.

transform_goal(Path0, Goal0 - Info0, GoalAndInfo) -->
	{ Goal0 = call(_, _, _, BuiltinState, _, _) },
	( { BuiltinState \= inline_builtin } ->
		{ reverse(Path0, Path) },
		wrap_call(Path, Goal0 - Info0, GoalAndInfo)
	;
		{ GoalAndInfo = Goal0 - Info0 }
	).

transform_goal(Path0, Goal0 - Info0, GoalAndInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ reverse(Path0, Path) },
	wrap_call(Path, Goal0 - Info0, GoalAndInfo).

:- pred transform_conj(int::in, goal_path::in,
	list(hlds_goal)::in, list(hlds_goal)::out,
	deep_info::in, deep_info::out) is det.

transform_conj(_, _, [], []) --> [].
transform_conj(N, Path, [Goal0 | Goals0], [Goal | Goals]) -->
	transform_goal([conj(N) | Path], Goal0, Goal),
	transform_conj(N + 1, Path, Goals0, Goals).

:- pred transform_disj(int::in, goal_path::in,
	list(hlds_goal)::in, list(hlds_goal)::out,
	deep_info::in, deep_info::out) is det.

transform_disj(_, _, [], []) --> [].
transform_disj(N, Path, [Goal0 | Goals0], [Goal | Goals]) -->
	transform_goal([disj(N) | Path], Goal0, Goal),
	transform_disj(N + 1, Path, Goals0, Goals).

:- pred transform_switch(int::in, int::in, goal_path::in,
	list(case)::in, list(case)::out,
	deep_info::in, deep_info::out) is det.

transform_switch(_, _, _, [], []) --> [].
transform_switch(NumCases, N, Path, [case(Id, Goal0) | Goals0],
		[case(Id, Goal) | Goals]) -->
	transform_goal([switch(NumCases, N) | Path], Goal0, Goal),
	transform_switch(NumCases, N + 1, Path, Goals0, Goals).

:- pred wrap_call(goal_path::in, hlds_goal::in, hlds_goal::out,
	deep_info::in, deep_info::out) is det.

wrap_call(GoalPath, Goal0, Goal, DeepInfo0, DeepInfo) :-
	Goal0 = GoalExpr - GoalInfo0,
	ModuleInfo = DeepInfo0 ^ module_info,
	MiddleCSD = DeepInfo0 ^ current_csd,

	goal_info_get_nonlocals(GoalInfo0, NonLocals0),
	goal_info_get_features(GoalInfo0, GoalFeatures),
	NewNonlocals = set__make_singleton_set(MiddleCSD),
	NonLocals = union(NonLocals0, NewNonlocals),
	goal_info_set_nonlocals(GoalInfo0, NonLocals, GoalInfo1),
	goal_info_remove_feature(GoalInfo1, tailcall, GoalInfo),

	SiteNum = DeepInfo0 ^ next_site_num,
	varset__new_var(DeepInfo0 ^ vars, SiteNumVar, Vars),
	IntType = int_type,
	map__set(DeepInfo0 ^ var_types, SiteNumVar, IntType, VarTypes),
	generate_unify(int_const(SiteNum), SiteNumVar, SiteNumVarGoal),
	DeepInfo1 = DeepInfo0 ^ vars := Vars,
	DeepInfo2 = DeepInfo1 ^ var_types := VarTypes,

	goal_info_get_context(GoalInfo0, Context),
	FileName0 = term__context_file(Context),
	LineNumber = term__context_line(Context),
	compress_filename(DeepInfo0, FileName0, FileName),
	classify_call(ModuleInfo, GoalExpr, CallKind),
	(
		CallKind = normal(PredProcId),
		generate_call(ModuleInfo, "prepare_for_normal_call", 2,
			[MiddleCSD, SiteNumVar], [], PrepareGoal),
		PredProcId = proc(PredId, ProcId),
		RttiProcLabel = rtti__make_proc_label(ModuleInfo,
			PredId, ProcId),
		TypeSubst = compute_type_subst(GoalExpr, DeepInfo2),
		CallSite = normal_call(RttiProcLabel, TypeSubst,
			FileName, LineNumber, GoalPath),
		Goal1 = Goal0,
		DeepInfo3 = DeepInfo2
	;
		CallKind = special(_PredProcId, TypeInfoVar),
		generate_call(ModuleInfo, "prepare_for_special_call", 3,
			[MiddleCSD, SiteNumVar, TypeInfoVar], [], PrepareGoal),
		CallSite = special_call(FileName, LineNumber, GoalPath),
		Goal1 = Goal0,
		DeepInfo3 = DeepInfo2
	;
		CallKind = generic(Generic),
		generate_call(ModuleInfo, "prepare_for_ho_call", 3,
			[MiddleCSD, SiteNumVar, ClosureVar], [], PrepareGoal),
		(
			Generic = higher_order(ClosureVar, _, _),
			CallSite = higher_order_call(FileName, LineNumber,
				GoalPath)
		;
			Generic = class_method(ClosureVar, _, _, _),
			CallSite = method_call(FileName, LineNumber, GoalPath)
		;
			Generic = aditi_builtin(_, _),
			error("deep profiling and aditi do not mix")
		),
		goal_info_get_code_model(GoalInfo0, GoalCodeModel),
		module_info_globals(ModuleInfo, Globals),
		globals__lookup_bool_option(Globals,
			use_zeroing_for_ho_cycles, UseZeroing),
		( UseZeroing = yes ->
			transform_higher_order_call(GoalCodeModel,
				Goal0, Goal1, DeepInfo2, DeepInfo3)
		;
			Goal1 = Goal0,
			DeepInfo3 = DeepInfo2
		)
	),
	DeepInfo4 = DeepInfo3 ^ next_site_num := SiteNum + 1,
	DeepInfo5 = DeepInfo4 ^ call_sites :=
		DeepInfo4 ^ call_sites ++ [CallSite],
	(
		member(tailcall, GoalFeatures),
		DeepInfo5 ^ maybe_rec_info = yes(RecInfo),
		RecInfo ^ role = outer_proc(_)
	->
		generate_recursion_counter_saves_and_restores(
			MiddleCSD, RecInfo ^ visible_scc,
			BeforeGoals, ExitGoals, FailGoals, ExtraVarList,
			DeepInfo5, DeepInfo),
		generate_call(ModuleInfo, "set_current_csd", 1,
			[MiddleCSD], [], ReturnGoal),
		
		goal_info_get_code_model(GoalInfo, CodeModel),
		( CodeModel = model_det ->
			condense([
				BeforeGoals,
				[SiteNumVarGoal, PrepareGoal, Goal1,
					ReturnGoal],
				ExitGoals
			], Goals),
			Goal = conj(Goals) - GoalInfo
		;
			ExtraVars = list_to_set(ExtraVarList),
			WrappedGoalGoalInfo =
				goal_info_add_nonlocals_make_impure(GoalInfo,
					ExtraVars),

			insert(ExtraVars, MiddleCSD, ReturnFailsNonLocals),
			ReturnFailsGoalInfo =
				impure_unreachable_init_goal_info(
					ReturnFailsNonLocals, failure),

			FailGoalInfo = fail_goal_info,
			FailGoal = disj([], init) - FailGoalInfo,

			append(FailGoals, [FailGoal], FailGoalsAndFail),

			condense([
				BeforeGoals,
				[disj([
					conj([
						SiteNumVarGoal,
						PrepareGoal,
						Goal1,
						ReturnGoal |
						ExitGoals
					]) - WrappedGoalGoalInfo,
					conj([
						ReturnGoal |
						FailGoalsAndFail
					]) - ReturnFailsGoalInfo
				], init) - WrappedGoalGoalInfo]
			], Goals),
			Goal = conj(Goals) - GoalInfo
		)
	;
		Goal = conj([
			SiteNumVarGoal,
			PrepareGoal,
			Goal1
		]) - GoalInfo,
		DeepInfo = DeepInfo5
	).

:- pred transform_higher_order_call(code_model::in,
	hlds_goal::in, hlds_goal::out, deep_info::in, deep_info::out) is det.

transform_higher_order_call(CodeModel, Goal0, Goal, DeepInfo0, DeepInfo) :-
	IntType = int_type,
	CPointerType = c_pointer_type,
	varset__new_var(DeepInfo0 ^ vars, SavedCountVar, Vars1),
	map__set(DeepInfo0 ^ var_types, SavedCountVar, IntType, VarTypes1),
	varset__new_var(Vars1, SavedPtrVar, Vars),
	map__set(VarTypes1, SavedPtrVar, CPointerType, VarTypes),
	DeepInfo1 = DeepInfo0 ^ vars := Vars,
	DeepInfo = DeepInfo1 ^ var_types := VarTypes,
	Goal0 = _ - GoalInfo0,
	MiddleCSD = DeepInfo ^ current_csd,
	generate_call(DeepInfo ^ module_info,
		"save_and_zero_activation_info", 3,
		[MiddleCSD, SavedCountVar, SavedPtrVar],
		[SavedCountVar, SavedPtrVar], SaveStuff),
	generate_call(DeepInfo ^ module_info, "reset_activation_info", 3,
		[MiddleCSD, SavedCountVar, SavedPtrVar], [], RestoreStuff),
	generate_call(DeepInfo ^ module_info, "rezero_activation_info", 1,
		[MiddleCSD], [], ReZeroStuff),

	% XXX We should create goal_exprs and goal_infos only in determinisms
	% that need them.
	ExtGoalInfo = goal_info_add_nonlocals_make_impure(GoalInfo0,
		list_to_set([MiddleCSD, SavedCountVar, SavedPtrVar])),

	% XXX We should build up NoBindExtGoalInfo from scratch.
	instmap_delta_init_reachable(EmptyDelta),
	goal_info_set_instmap_delta(ExtGoalInfo, EmptyDelta,
		NoBindExtGoalInfo),

	FailGoalInfo = fail_goal_info,
	FailGoal = disj([], init) - FailGoalInfo,

	RestoreFailGoalInfo = impure_unreachable_init_goal_info(
		list_to_set([MiddleCSD, SavedCountVar, SavedPtrVar]), failure),

	RezeroFailGoalInfo = impure_unreachable_init_goal_info(
		list_to_set([MiddleCSD]), failure),

	goal_info_add_feature(GoalInfo0, impure, GoalInfo),
	(
		CodeModel = model_det,
		Goal = conj([
			SaveStuff,
			Goal0,
			RestoreStuff
		]) - GoalInfo
	;
		CodeModel = model_semi,
		Goal = conj([
			SaveStuff,
			disj([
				conj([
					Goal0,
					RestoreStuff
				]) - ExtGoalInfo,
				conj([
					RestoreStuff,
					FailGoal
				]) - RestoreFailGoalInfo
			], init) - ExtGoalInfo
		]) - GoalInfo
	;
		CodeModel = model_non,
		Goal = conj([
			SaveStuff,
			disj([
				conj([
					Goal0,
					disj([
						RestoreStuff,
						conj([
							ReZeroStuff,
							FailGoal
						]) - RezeroFailGoalInfo
					], init) - NoBindExtGoalInfo
				]) - ExtGoalInfo,
				conj([
					RestoreStuff,
					FailGoal
				]) - RestoreFailGoalInfo
			], init) - ExtGoalInfo
		]) - GoalInfo
	).

:- pred wrap_foreign_code(goal_path::in, hlds_goal::in, hlds_goal::out,
	deep_info::in, deep_info::out) is det.

wrap_foreign_code(GoalPath, Goal0, Goal, DeepInfo0, DeepInfo) :-
	Goal0 = _ - GoalInfo0,
	ModuleInfo = DeepInfo0 ^ module_info,
	MiddleCSD = DeepInfo0 ^ current_csd,

	goal_info_get_nonlocals(GoalInfo0, NonLocals0),
	NewNonlocals = set__make_singleton_set(MiddleCSD),
	NonLocals = union(NonLocals0, NewNonlocals),
	goal_info_set_nonlocals(GoalInfo0, NonLocals, GoalInfo),

	SiteNum = DeepInfo0 ^ next_site_num,
	varset__new_var(DeepInfo0 ^ vars, SiteNumVar, Vars),
	IntType = int_type,
	map__set(DeepInfo0 ^ var_types, SiteNumVar, IntType, VarTypes),
	generate_unify(int_const(SiteNum), SiteNumVar, SiteNumVarGoal),

	generate_call(ModuleInfo, "prepare_for_callback", 2,
		[MiddleCSD, SiteNumVar], [], PrepareGoal),

	goal_info_get_context(GoalInfo0, Context),
	LineNumber = term__context_line(Context),
	FileName0 = term__context_file(Context),
	compress_filename(DeepInfo0, FileName0, FileName),
	CallSite = callback(FileName, LineNumber, GoalPath),

	Goal = conj([
		SiteNumVarGoal,
		PrepareGoal,
		Goal0
	]) - GoalInfo,
	DeepInfo1 = DeepInfo0 ^ next_site_num := SiteNum + 1,
	DeepInfo2 = DeepInfo1 ^ call_sites
		:= DeepInfo1 ^ call_sites ++ [CallSite],
	DeepInfo3 = DeepInfo2 ^ vars := Vars,
	DeepInfo = DeepInfo3 ^ var_types := VarTypes.

:- pred compress_filename(deep_info::in, string::in, string::out) is det.

compress_filename(Deep, FileName0, FileName) :-
	( FileName0 = Deep ^ proc_filename ->
		FileName = ""
	;
		FileName = FileName0
	).

:- type call_class
			% For normal first order calls
	--->	normal(pred_proc_id)
			% For calls to unify/2 and compare/3
	;	special(pred_proc_id, prog_var)
			% For higher order and typeclass method calls
	;	generic(generic_call)
	.

:- pred classify_call(module_info::in, hlds_goal_expr::in,
	call_class::out) is det.

classify_call(ModuleInfo, Expr, Class) :-
	( Expr = call(PredId, ProcId, Args, _, _, _) ->
		module_info_get_predicate_table(ModuleInfo, PredTable),
		mercury_public_builtin_module(MercuryBuiltin),
		(
			predicate_table_search_pred_m_n_a(PredTable,
				MercuryBuiltin, "unify", 2, [PredId]),
			Args = [TypeInfoVar | _]
		->
			Class = special(proc(PredId, ProcId), TypeInfoVar)
		;
			predicate_table_search_pred_m_n_a(PredTable,
				MercuryBuiltin, "compare", 3, [PredId]),
			Args = [TypeInfoVar | _]
		->
			Class = special(proc(PredId, ProcId), TypeInfoVar)
		;
			Class = normal(proc(PredId, ProcId))
		)
	; Expr = generic_call(Generic, _, _, _) ->
		Class = generic(Generic)
	;
		error("unexpected goal type in classify_call/2")
	).

:- func compute_type_subst(hlds_goal_expr, deep_info) = string.

% XXX we don't compute type substitution strings yet.
compute_type_subst(_, _) = "".

:- pred generate_recursion_counter_saves_and_restores(
		prog_var, list(visible_scc_data), list(hlds_goal),
		list(hlds_goal), list(hlds_goal), list(prog_var),
		deep_info, deep_info).
:- mode generate_recursion_counter_saves_and_restores(in, in, out, out, out,
		out, in, out) is det.

generate_recursion_counter_saves_and_restores(_, [], [], [], [], [],
		DInfo, DInfo).
generate_recursion_counter_saves_and_restores(CSDVar, [Vis|Viss],
		Befores, Exits, Fails, Vars, DeepInfo0, DeepInfo) :-
	generate_recursion_counter_saves_and_restores_2(Vis ^ rec_call_sites,
		CSDVar, Befores0, Exits0, Fails0, Vars0, DeepInfo0, DeepInfo1),
	(
		Viss = [],
		Befores = Befores0,
		Exits = Exits0,
		Fails = Fails0,
		Vars = Vars0,
		DeepInfo = DeepInfo1
	;
		Viss = [_|_],
		error("generate_recursion_counter_saves_and_restores: not implemented")
		% generate a call to get the outermost csd for the next
		% procedure in the clique, then make the recursive call
	).

:- pred generate_recursion_counter_saves_and_restores_2(
		list(int), prog_var, list(hlds_goal), list(hlds_goal),
		list(hlds_goal), list(prog_var), deep_info, deep_info).
:- mode generate_recursion_counter_saves_and_restores_2(in, in, out, out,
		out, out, in, out) is det.

generate_recursion_counter_saves_and_restores_2([], _, [], [], [], [],
		DInfo, DInfo).
generate_recursion_counter_saves_and_restores_2([CSN|CSNs], CSDVar,
		[Unify, Before|Befores], [Exit|Exits], [Fail|Fails],
		[CSNVar, DepthVar|ExtraVars], DeepInfo0, DeepInfo) :-
	varset__new_var(DeepInfo0 ^ vars, CSNVar, Vars1),
	IntType = functor(atom("int"), [], context_init),
	map__set(DeepInfo0 ^ var_types, CSNVar, IntType, VarTypes1),
	varset__new_var(Vars1, DepthVar, Vars),
	map__set(VarTypes1, DepthVar, IntType, VarTypes),
	DeepInfo1 = (DeepInfo0 ^ vars := Vars) ^ var_types := VarTypes,
	generate_unify(int_const(CSN), CSNVar, Unify),
	ModuleInfo = DeepInfo1 ^ module_info,
	generate_call(ModuleInfo, "save_recursion_depth_count", 3,
		[CSDVar, CSNVar, DepthVar], [DepthVar], Before),
	generate_call(ModuleInfo, "restore_recursion_depth_count_exit", 3,
		[CSDVar, CSNVar, DepthVar], [], Exit),
	generate_call(ModuleInfo, "restore_recursion_depth_count_fail", 3,
		[CSDVar, CSNVar, DepthVar], [], Fail),
	generate_recursion_counter_saves_and_restores_2(CSNs, CSDVar,
		Befores, Exits, Fails, ExtraVars, DeepInfo1, DeepInfo).

%:- pred generate_ho_save_goal(ho_call_info, module_info, hlds_goal).
%:- mode generate_ho_save_goal(in, in, out) is det.
%
%generate_ho_save_goal(ho_call_info(MiddleCSD, CountVar, PtrVar), ModuleInfo,
%		Goal) :-
%	generate_call(ModuleInfo, "save_and_zero_activation_info", 3,
%		[MiddleCSD, CountVar, PtrVar], [CountVar, PtrVar], Goal).
%
%generate_ho_save_goal(ho_call_info(MiddleCSD, PtrVar), ModuleInfo, Goal) :-
%	generate_call(ModuleInfo, "save_and_zero_activation_info", 2,
%		[MiddleCSD, PtrVar], [PtrVar], Goal).
%
%:- pred generate_ho_restore_goal(ho_call_info, module_info,
%		set(prog_var), hlds_goal).
%:- mode generate_ho_restore_goal(in, in, out, out) is det.
%
%generate_ho_restore_goal(ho_call_info(MiddleCSD, CountVar, PtrVar), ModuleInfo,
%		RestoreVars, Goal) :-
%	RestoreVars = list_to_set([MiddleCSD, CountVar, PtrVar]),
%	generate_call(ModuleInfo, "reset_activation_info", 3,
%		[MiddleCSD, CountVar, PtrVar], [], Goal).
%
%generate_ho_restore_goal(ho_call_info(MiddleCSD, PtrVar), ModuleInfo,
%		RestoreVars, Goal) :-
%	RestoreVars = list_to_set([MiddleCSD, PtrVar]),
%	generate_call(ModuleInfo, "reset_activation_info", 2,
%		[MiddleCSD, PtrVar], [], Goal).

:- pred generate_call(module_info::in, string::in, int::in,
	list(prog_var)::in, list(prog_var)::in, hlds_goal::out) is det.

generate_call(ModuleInfo, Name, Arity, ArgVars, OutputVars, Goal) :-
	generate_call(ModuleInfo, Name, Arity, ArgVars, yes(OutputVars),
		det, Goal).

:- pred generate_call(module_info::in, string::in, int::in, list(prog_var)::in,
	maybe(list(prog_var))::in, determinism::in, hlds_goal::out) is det.

generate_call(ModuleInfo, Name, Arity, ArgVars, MOutputVars, Detism, Goal) :-
	get_deep_profile_builtin_ppid(ModuleInfo, Name, Arity, PredId, ProcId),
	NonLocals = list_to_set(ArgVars),
	Ground = ground(shared, none),
	(
		MOutputVars = yes(OutputVars),
		map((pred(V::in, P::out) is det :-
			P = V - Ground
		), OutputVars, OutputInsts),
		instmap_delta_from_assoc_list(OutputInsts, InstMapDelta)
	;
		MOutputVars = no,
		instmap_delta_init_unreachable(InstMapDelta)
	),
	GoalInfo = impure_init_goal_info(NonLocals, InstMapDelta, Detism),
	Goal = call(PredId, ProcId, ArgVars, not_builtin, no,
		unqualified(Name)) - GoalInfo.

:- pred generate_unify(cons_id::in, prog_var::in, hlds_goal::out) is det.

generate_unify(ConsId, Var, Goal) :-
	Ground = ground(shared, none),
	NonLocals = set__make_singleton_set(Var),
	instmap_delta_from_assoc_list([Var - ground(shared, none)],
		InstMapDelta),
	Determinism = det,
	goal_info_init(NonLocals, InstMapDelta, Determinism, GoalInfo),
	Goal = unify(Var, functor(ConsId, []),
    		(free -> Ground) - (Ground -> Ground),
		construct(Var, ConsId, [], [], construct_statically([]),
			cell_is_shared, no),
		unify_context(explicit, [])) - GoalInfo.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred get_deep_profile_builtin_ppid(module_info::in, string::in, int::in,
	pred_id::out, proc_id::out) is det.

get_deep_profile_builtin_ppid(ModuleInfo, Name, Arity, PredId, ProcId) :-
	mercury_profiling_builtin_module(ModuleName),
	module_info_get_predicate_table(ModuleInfo, PredTable),
	(
		predicate_table_search_pred_m_n_a(PredTable,
			ModuleName, Name, Arity, PredIds)
	->
		(
			PredIds = [],
			error("get_deep_profile_builtin_ppid: no pred_id")
		;
			PredIds = [PredId],
			predicate_table_get_preds(PredTable, Preds),
			lookup(Preds, PredId, PredInfo),
			pred_info_procids(PredInfo, ProcIds),
			(
				ProcIds = [],
				error("get_deep_profile_builtin_ppid: no proc_id")
			;
				ProcIds = [ProcId]
			;
				ProcIds = [_, _ | _],
				error("get_deep_profile_builtin_ppid: proc_id not unique")
			)
		;
			PredIds = [_, _ | _],
			error("get_deep_profile_builtin_ppid: pred_id not unique")
		)
	;
		format("couldn't find pred_id for `%s'/%d",
			[s(Name), i(Arity)], Msg),
		error(Msg)
	).

%------------------------------------------------------------------------------%

:- func impure_init_goal_info(set(prog_var), instmap_delta, determinism)
	= hlds_goal_info.

impure_init_goal_info(NonLocals, InstMapDelta, Determinism) = GoalInfo :-
	goal_info_init(NonLocals, InstMapDelta, Determinism, GoalInfo0),
	goal_info_add_feature(GoalInfo0, impure, GoalInfo).

:- func impure_reachable_init_goal_info(set(prog_var), determinism)
	= hlds_goal_info.

impure_reachable_init_goal_info(NonLocals, Determinism) = GoalInfo :-
	instmap_delta_init_reachable(InstMapDelta),
	goal_info_init(NonLocals, InstMapDelta, Determinism, GoalInfo0),
	goal_info_add_feature(GoalInfo0, impure, GoalInfo).

:- func impure_unreachable_init_goal_info(set(prog_var), determinism)
	= hlds_goal_info.

impure_unreachable_init_goal_info(NonLocals, Determinism) = GoalInfo :-
	instmap_delta_init_unreachable(InstMapDelta),
	goal_info_init(NonLocals, InstMapDelta, Determinism, GoalInfo0),
	goal_info_add_feature(GoalInfo0, impure, GoalInfo).

:- func goal_info_add_nonlocals_make_impure(hlds_goal_info, set(prog_var))
	= hlds_goal_info.

goal_info_add_nonlocals_make_impure(GoalInfo0, NewNonLocals) = GoalInfo :- 
	goal_info_get_nonlocals(GoalInfo0, NonLocals0),
	NonLocals = set__union(NonLocals0, NewNonLocals),
	goal_info_set_nonlocals(GoalInfo0, NonLocals, GoalInfo1),
	goal_info_add_feature(GoalInfo1, impure, GoalInfo).

:- func fail_goal_info = hlds_goal_info.

fail_goal_info = GoalInfo :-
	instmap_delta_init_unreachable(InstMapDelta),
	goal_info_init(set__init, InstMapDelta, failure, GoalInfo).

%------------------------------------------------------------------------------%
