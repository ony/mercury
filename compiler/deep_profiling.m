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
		PredIds, PredMap0, PredMap, [], ProcStatics) },
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
		OrigDeepProfileInfo = deep_profile_proc_info(
			outer_proc(ClonePredProcId),
			[PredProcId - ClonePredProcId]),
		CloneDeepProfileInfo = deep_profile_proc_info(
			inner_proc(PredProcId),
			[PredProcId - ClonePredProcId]),
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
apply_tail_recursion_to_disj([Goal0 | Goals0], ApplyInfo,
		[Goal | Goals], FoundTailCall0, FoundTailCall) :-
	apply_tail_recursion_to_goal(Goal0, ApplyInfo, Goal,
		FoundTailCall0, FoundTailCall1, _),
	apply_tail_recursion_to_disj(Goals0, ApplyInfo, Goals,
		FoundTailCall1, FoundTailCall).

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

:- pred transform_predicate(module_info::in, pred_id::in,
	pred_table::in, pred_table::out,
	list(layout_data)::in, list(layout_data)::out) is det.

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
	list(layout_data)::in, list(layout_data)::out) is det.

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
			PredModuleName = unqualified("profiling_builtin")
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
	list(layout_data)::in, list(layout_data)::out) is det.

transform_procedure2(ModuleInfo, PredProcId, Proc0, Proc,
		ProcStaticList0, ProcStaticList) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	goal_info_get_code_model(GoalInfo0, CodeModel),		% XXX zs: bug?
	(
		CodeModel = model_det,
		transform_det_proc(ModuleInfo, PredProcId, Proc0,
			Proc, ProcStatic)
	;
		CodeModel = model_semi,
		transform_semi_proc(ModuleInfo, PredProcId, Proc0,
			Proc, ProcStatic)
	;
		CodeModel = model_non,
		transform_non_proc(ModuleInfo, PredProcId, Proc0,
			Proc, ProcStatic)
	),
	ProcStaticList = [ProcStatic | ProcStaticList0].

%-----------------------------------------------------------------------------%

:- type deep_info
	--->	deep_info(
			module_info		:: module_info,
			current_csd		:: prog_var,
			next_site_num		:: int,
			call_sites		:: list(call_site_static_data),
			vars			:: prog_varset,
			var_types		:: vartypes
		).

:- pred transform_det_proc(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out, layout_data::out) is det.

transform_det_proc(ModuleInfo, PredProcId, Proc0, Proc, ProcStatic) :-
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
	globals__lookup_bool_option(Globals,
		use_activation_counts, UseActivationCounts),
	( UseActivationCounts = no ->
		varset__new_var(Vars3, ActivationPtr0, Vars5),
		map__set(VarTypes3, ActivationPtr0, CPointerType, VarTypes5),
		MActivationPtr = yes(ActivationPtr0)
	;
		Vars5 = Vars3,
		VarTypes5 = VarTypes3,
		MActivationPtr = no
	),
	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0, [], Vars5, VarTypes5),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,
	CallSites = PInfo ^ call_sites,

	PredProcId = proc(PredId, ProcId),
	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStatic = proc_static_data(RttiProcLabel, FileName, CallSites),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	( MActivationPtr = yes(ActivationPtr1) ->
		generate_call(ModuleInfo, "det_call_port_code", 4,
			[ProcStaticVar, TopCSD, MiddleCSD, ActivationPtr1],
			[TopCSD, MiddleCSD, ActivationPtr1], CallPortCode)
	;
		generate_call(ModuleInfo, "det_call_port_code", 3,
			[ProcStaticVar, TopCSD, MiddleCSD],
			[TopCSD, MiddleCSD], CallPortCode)
	),


	( MActivationPtr = yes(ActivationPtr2) ->
		generate_call(ModuleInfo, "det_exit_port_code", 3,
			[TopCSD, MiddleCSD, ActivationPtr2], [], ExitPortCode)
	;
		generate_call(ModuleInfo, "det_exit_port_code", 2,
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
	proc_info::in, proc_info::out, layout_data::out) is det.

transform_semi_proc(ModuleInfo, PredProcId, Proc0, Proc, ProcStatic) :-
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
	globals__lookup_bool_option(Globals,
		use_activation_counts, UseActivationCounts),
	( UseActivationCounts = no ->
		varset__new_var(Vars3, ActivationPtr0, Vars5),
		map__set(VarTypes3, ActivationPtr0, CPointerType, VarTypes5),
		MActivationPtr = yes(ActivationPtr0)
	;
		Vars5 = Vars3,
		VarTypes5 = VarTypes3,
		MActivationPtr = no
	),
	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0, [], Vars5, VarTypes5),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,
	CallSites = PInfo ^ call_sites,

	PredProcId = proc(PredId, ProcId),
	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStatic = proc_static_data(RttiProcLabel, FileName, CallSites),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	( MActivationPtr = yes(ActivationPtr1) ->
		generate_call(ModuleInfo, "semi_call_port_code", 4,
			[ProcStaticVar, TopCSD, MiddleCSD, ActivationPtr1],
			[TopCSD, MiddleCSD, ActivationPtr1], CallPortCode),
		generate_call(ModuleInfo, "semi_exit_port_code", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], [], ExitPortCode),
		generate_call(ModuleInfo, "semi_fail_port_code", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], no, failure,
			FailPortCode),
		NewNonlocals = list_to_set([MiddleCSD, ActivationPtr1])
	;
		generate_call(ModuleInfo, "semi_call_port_code", 3,
			[ProcStaticVar, TopCSD, MiddleCSD],
			[TopCSD, MiddleCSD], CallPortCode),
		generate_call(ModuleInfo, "semi_exit_port_code", 2,
			[TopCSD, MiddleCSD], [], ExitPortCode),
		generate_call(ModuleInfo, "semi_fail_port_code", 2,
			[TopCSD, MiddleCSD], no, failure, FailPortCode),
		NewNonlocals = list_to_set([MiddleCSD])
	),

	goal_info_get_nonlocals(GoalInfo0, NonLocals0),
	NonLocals1 = union(NonLocals0, NewNonlocals),
	goal_info_set_nonlocals(GoalInfo0, NonLocals1, GoalInfo1),

	NonLocals2 = union(NewNonlocals, list_to_set([TopCSD])),
	instmap_delta_init_unreachable(InstMapDelta),
	Determinism = failure,
	goal_info_init(NonLocals2, InstMapDelta, Determinism, GoalInfo2),

	Goal = conj([
		BindProcStaticVarGoal,
		CallPortCode,
		disj([
			conj([
				TransformedGoal,
				ExitPortCode
			]) - GoalInfo1,
			conj([
				FailPortCode
			]) - GoalInfo2
		], init) - GoalInfo1
	]) - GoalInfo0,
	proc_info_set_varset(Proc0, Vars, Proc1),
	proc_info_set_vartypes(Proc1, VarTypes, Proc2),
	proc_info_set_goal(Proc2, Goal, Proc).

:- pred transform_non_proc(module_info::in, pred_proc_id::in,
	proc_info::in, proc_info::out, layout_data::out) is det.

transform_non_proc(ModuleInfo, PredProcId, Proc0, Proc, ProcStatic) :-
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
	globals__lookup_bool_option(Globals,
		use_activation_counts, UseActivationCounts),
	( UseActivationCounts = no ->
		varset__new_var(Vars3, OldOutermostProcDyn0, Vars4),
		map__set(VarTypes3, OldOutermostProcDyn0, CPointerType,
			VarTypes4),
		varset__new_var(Vars4, NewOutermostProcDyn, Vars5),
		map__set(VarTypes4, NewOutermostProcDyn, CPointerType,
			VarTypes5),
		MOldActivationPtr = yes(OldOutermostProcDyn0)
	;
		varset__new_var(Vars3, NewOutermostProcDyn, Vars5),
		map__set(VarTypes3, NewOutermostProcDyn, CPointerType,
			VarTypes5),
		MOldActivationPtr = no
	),
	goal_info_get_context(GoalInfo0, Context),
	FileName = term__context_file(Context),

	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0, [], Vars5, VarTypes5),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo ^ vars,
	VarTypes = PInfo ^ var_types,
	CallSites = PInfo ^ call_sites,

	PredProcId = proc(PredId, ProcId),
	RttiProcLabel = rtti__make_proc_label(ModuleInfo, PredId, ProcId),
	ProcStatic = proc_static_data(RttiProcLabel, FileName, CallSites),
	ProcStaticConsId = deep_profiling_proc_static(RttiProcLabel),
	generate_unify(ProcStaticConsId, ProcStaticVar, BindProcStaticVarGoal),

	( MOldActivationPtr = yes(OldOutermostProcDyn2) ->
		generate_call(ModuleInfo, "non_call_port_code", 5,
			[ProcStaticVar, TopCSD, MiddleCSD,
			OldOutermostProcDyn2, NewOutermostProcDyn],
			[TopCSD, MiddleCSD,
				OldOutermostProcDyn2, NewOutermostProcDyn],
			CallPortCode),
		generate_call(ModuleInfo, "non_exit_port_code", 3,
			[TopCSD, MiddleCSD, OldOutermostProcDyn2], [],
			ExitPortCode),
		generate_call(ModuleInfo, "non_fail_port_code", 3,
			[TopCSD, MiddleCSD, OldOutermostProcDyn2], no,
			failure, FailPortCode),
		generate_call(ModuleInfo, "non_redo_port_code2", 2,
			[MiddleCSD, NewOutermostProcDyn], no,
			failure, RedoPortCode),
		NewNonlocals = list_to_set(
			[TopCSD, MiddleCSD, OldOutermostProcDyn2])
	;
		generate_call(ModuleInfo, "non_call_port_code", 4,
			[ProcStaticVar, TopCSD, MiddleCSD, NewOutermostProcDyn],
			[TopCSD, MiddleCSD, NewOutermostProcDyn],
			CallPortCode),
		generate_call(ModuleInfo, "non_exit_port_code", 2,
			[TopCSD, MiddleCSD], [], ExitPortCode),
		generate_call(ModuleInfo, "non_fail_port_code", 2,
			[TopCSD, MiddleCSD], no, failure, FailPortCode),
		generate_call(ModuleInfo, "non_redo_port_code1", 2,
			[MiddleCSD, NewOutermostProcDyn], no,
			failure, RedoPortCode),
		NewNonlocals = list_to_set([TopCSD, MiddleCSD])
	),

	DetMulti = multidet,
	instmap_delta_init_unreachable(Unreachable),
	goal_info_get_nonlocals(GoalInfo0, NonLocals0),

	NonLocals3 = union(NewNonlocals, list_to_set([NewOutermostProcDyn])),
	goal_info_init(NonLocals3, Unreachable, DetMulti, GoalInfo3),

	NonLocals4 = union(NonLocals0, NonLocals3),
	goal_info_set_nonlocals(GoalInfo0, NonLocals4, GoalInfo4),

	Goal = conj([
		BindProcStaticVarGoal,
		CallPortCode,
		disj([
			conj([
				TransformedGoal,
				disj([
					ExitPortCode,
					RedoPortCode
				], init) - GoalInfo3
			]) - GoalInfo4,
			FailPortCode
		], init) - GoalInfo4
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
	LineNumber = term__context_line(Context),
	classify_call(ModuleInfo, GoalExpr, CallKind),
	(
		CallKind = normal(PredProcId),
		generate_call(ModuleInfo, "make_new_csd_for_normal_call", 2,
			[MiddleCSD, SiteNumVar], [], PrepareGoal),
		PredProcId = proc(PredId, ProcId),
		RttiProcLabel = rtti__make_proc_label(ModuleInfo,
			PredId, ProcId),
		CallSite = normal_call(RttiProcLabel, LineNumber, GoalPath),
		Goal1 = Goal0,
		DeepInfo3 = DeepInfo2
	;
		CallKind = special(_PredProcId, TypeInfoVar),
		generate_call(ModuleInfo, "make_new_csd_for_special_call", 3,
			[MiddleCSD, SiteNumVar, TypeInfoVar], [], PrepareGoal),
		CallSite = special_call(LineNumber, GoalPath),
		Goal1 = Goal0,
		DeepInfo3 = DeepInfo2
	;
		CallKind = generic(Generic),
		generate_call(ModuleInfo, "make_new_csd_for_ho_call", 3,
			[MiddleCSD, SiteNumVar, ClosureVar], [], PrepareGoal),
		(
			Generic = higher_order(ClosureVar, _, _),
			CallSite = higher_order_call(LineNumber, GoalPath)
		;
			Generic = class_method(ClosureVar, _, _, _),
			CallSite = method_call(LineNumber, GoalPath)
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
	Goal = conj([
		SiteNumVarGoal,
		PrepareGoal,
		Goal1
	]) - GoalInfo,
	DeepInfo4 = DeepInfo3 ^ next_site_num := SiteNum + 1,
	DeepInfo = DeepInfo4 ^ call_sites
		:= DeepInfo1 ^ call_sites ++ [CallSite].

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
	Goal0 = _ - GoalInfo,
	MiddleCSD = DeepInfo ^ current_csd,
	generate_call(DeepInfo ^ module_info,
		"save_and_zero_activation_info", 3,
		[MiddleCSD, SavedCountVar, SavedPtrVar],
		[SavedCountVar, SavedPtrVar], SaveStuff),
	generate_call(DeepInfo ^ module_info, "reset_activation_info", 3,
		[MiddleCSD, SavedCountVar, SavedPtrVar], [], RestoreStuff),
	generate_call(DeepInfo ^ module_info, "rezero_activation_info", 1,
		[MiddleCSD], [], ReZeroStuff),
	
	goal_info_get_nonlocals(GoalInfo, GoalNonlocals),
	ExtNonlocals = union(
		list_to_set([MiddleCSD, SavedCountVar, SavedPtrVar]),
		GoalNonlocals),
	goal_info_set_nonlocals(GoalInfo, ExtNonlocals, ExtGoalInfo),

	instmap_delta_init_unreachable(Unreachable),

	goal_info_init(init, Unreachable, failure, FailGoalInfo0),
	FailGoal = disj([], init) - FailGoalInfo0,

	FailVars1 = list_to_set([MiddleCSD, SavedCountVar, SavedPtrVar]),
	goal_info_init(FailVars1, Unreachable, failure, FailGoalInfo1),

	FailVars2 = list_to_set([MiddleCSD]),
	goal_info_init(FailVars2, Unreachable, failure, FailGoalInfo2),

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
				]) - FailGoalInfo1
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
						]) - FailGoalInfo2,
						conj([
							RestoreStuff,
							FailGoal
						]) - FailGoalInfo1
					], init) - ExtGoalInfo
				]) - ExtGoalInfo,
				conj([
					RestoreStuff,
					FailGoal
				]) - FailGoalInfo1
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

	generate_call(ModuleInfo, "make_new_csd_for_foreign_call", 2,
		[MiddleCSD, SiteNumVar], [], PrepareGoal),

	goal_info_get_context(GoalInfo0, Context),
	LineNumber = term__context_line(Context),
	CallSite = callback(LineNumber, GoalPath),

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
	goal_info_init(NonLocals, InstMapDelta, Detism, GoalInfo0),
	goal_info_add_feature(GoalInfo0, (impure), GoalInfo),
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
	ModuleName = unqualified("profiling_builtin"),
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
