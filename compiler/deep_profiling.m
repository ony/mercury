:- module deep_profiling.

:- interface.

:- import_module hlds_module, hlds_data, llds.
:- import_module counter, io, list.

:- pred apply_deep_profiling_transformation(module_info, module_info,
		list(cons_id), io__state, io__state).
:- mode apply_deep_profiling_transformation(in, out, out, di, uo) is det.

:- pred generate_llds_proc_descriptions(module_info, list(cons_id),
		list(comp_gen_c_data), counter, counter).
:- mode generate_llds_proc_descriptions(in, in, out, in, out) is det.

%------------------------------------------------------------------------------%
:- implementation.

:- import_module (inst), instmap, hlds_data, hlds_pred, hlds_goal, prog_data.
:- import_module options, code_model, code_util, prog_util, quantification.
:- import_module globals.
:- import_module bool, int, list, map, require, set.
:- import_module exception, std_util, string, term, varset.

% TODO
% fix cruft to do with the cons_id....

% 
% Doing the work in procedure bodies, not at calls:
% 
% middle's new body, if det:
% middle(...) :-
% 	get_parent_cur_csd(TopCSD, MiddleCSD),
% 	create_proc_dynamic(MiddleCSD, ProcDescr),
% 	increment_activation_count(MiddleCSD),
% 	<middle's original body, with calls transformed as below>,
% 	decrement_activation_count(ProcDyn),
% 	set_cur_csd(TopCSD).
% 
% middle's new body, if semi:
% middle(...) :-
% 	get_parent_cur_csd(TopCSD, MiddleCSD),
% 	create_proc_dynamic(MiddleCSD, ProcDescr),
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
% 	create_proc_dynamic(MiddleCSD, ProcDesc, NewOutermostProcDyn),
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

apply_deep_profiling_transformation(Module0, Module, ProcDescs, IO0, IO) :-
    module_info_predids(Module0, PredIds),
    module_info_get_predicate_table(Module0, PredTable0),
    predicate_table_get_preds(PredTable0, Preds0),
    foldl2((pred(PredId::in, Pd0::in, Pd::out, Ds0::in, Ds1::out) is det :-
    	lookup(Pd0, PredId, PredInfo0),
	pred_info_non_imported_procids(PredInfo0, ProcIds),
	pred_info_procedures(PredInfo0, Procs0),
	foldl2((pred(ProcId::in, Ps0::in, Ps::out, Ds2::in, Ds3::out) is det :-
	    lookup(Ps0, ProcId, ProcInfo0),
	    transform_procedure(Module0, proc(PredId, ProcId), ProcInfo0,
	    	ProcInfo, ProcDesc),
	    set(Ps0, ProcId, ProcInfo, Ps),
	    append(ProcDesc, Ds2, Ds3)
	), ProcIds, Procs0, Procs, Ds0, Ds1),
	pred_info_set_procedures(PredInfo0, Procs, PredInfo),
	set(Pd0, PredId, PredInfo, Pd)
    ), PredIds, Preds0, Preds, [], ProcDescs),
    predicate_table_set_preds(PredTable0, Preds, PredTable),
    module_info_set_predicate_table(Module0, PredTable, Module),
    IO = IO0.

:- pred transform_procedure(module_info, pred_proc_id,
		proc_info, proc_info, list(cons_id)).
:- mode transform_procedure(in, in, in, out, out) is det.

transform_procedure(ModuleInfo, PredProcId, Proc0, Proc, ProcDescList) :-
    proc_info_goal(Proc0, Goal0),
    PredProcId = proc(PredId, _),
    predicate_module(ModuleInfo, PredId, PredModuleName),
    (
    	(
		% XXX We need to do something drastic to handle nondet C code...
		Goal0 = pragma_foreign_code(_, _, _, _, _, _, Impl) - _,
		Impl = nondet(_, _, _, _, _, _, _, _, _)
	;
		% We don't want to transform the procedures for managing the
		% deep profiling call graph, or we'd get inifinite recursion.
		PredModuleName = unqualified("profiling_builtin")
	)
    ->
    	Proc = Proc0,
    	ProcDescList = []
    ;
	transform_procedure2(ModuleInfo, PredProcId, Proc0, Proc, ProcDescList)
    ).

:- pred transform_procedure2(module_info, pred_proc_id, proc_info, proc_info,
		list(cons_id)).
:- mode transform_procedure2(in, in, in, out, out) is det.

transform_procedure2(ModuleInfo, PredProcId, Proc0, Proc, ProcDescList) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	goal_info_get_code_model(GoalInfo0, CodeModel),
	(
		CodeModel = model_det,
		transform_det_proc(ModuleInfo, PredProcId, Proc0,
			Proc, ProcDescList)
	;
		CodeModel = model_semi,
		transform_semi_proc(ModuleInfo, PredProcId, Proc0,
			Proc, ProcDescList)
	;
		CodeModel = model_non,
		transform_non_proc(ModuleInfo, PredProcId, Proc0,
			Proc, ProcDescList)
	).

:- pred transform_det_proc(module_info, pred_proc_id, proc_info, proc_info,
		list(cons_id)).
:- mode transform_det_proc(in, in, in, out, out) is det.

transform_det_proc(ModuleInfo, PredProcId, Proc0, Proc, ProcDescList) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = functor(atom("c_pointer"), [], context_init),
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcDescVar, Vars3),
	map__set(VarTypes2, ProcDescVar, CPointerType, VarTypes3),
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

	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0, [], Vars5, VarTypes5),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo^vars,
	VarTypes = PInfo^var_types,
	CallSites = PInfo^call_sites,

	ProcDesc = deep_profiling_procedure_data(PredProcId, CallSites),

	generate_unify(ProcDesc, ProcDescVar, BindProcDescVarGoal),

	( MActivationPtr = yes(ActivationPtr1) ->
		generate_call(ModuleInfo, "det_call_port_code", 4,
			[ProcDescVar, TopCSD, MiddleCSD, ActivationPtr1],
			[TopCSD, MiddleCSD, ActivationPtr1], CallPortCode)
	;
		generate_call(ModuleInfo, "det_call_port_code", 3,
			[ProcDescVar, TopCSD, MiddleCSD],
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
		BindProcDescVarGoal,
		CallPortCode,
		TransformedGoal,
		ExitPortCode
	]) - GoalInfo0,
	proc_info_set_varset(Proc0, Vars, Proc1),
	proc_info_set_vartypes(Proc1, VarTypes, Proc2),
	proc_info_set_goal(Proc2, Goal, Proc),
	ProcDescList = [ProcDesc].

:- pred transform_semi_proc(module_info, pred_proc_id, proc_info, proc_info,
		list(cons_id)).
:- mode transform_semi_proc(in, in, in, out, out) is det.

transform_semi_proc(ModuleInfo, PredProcId, Proc0, Proc, ProcDescList) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = functor(atom("c_pointer"), [], context_init),
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcDescVar, Vars3),
	map__set(VarTypes2, ProcDescVar, CPointerType, VarTypes3),
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

	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0, [], Vars5, VarTypes5),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo^vars,
	VarTypes = PInfo^var_types,
	CallSites = PInfo^call_sites,

	ProcDesc = deep_profiling_procedure_data(PredProcId, CallSites),
	generate_unify(ProcDesc, ProcDescVar, BindProcDescVarGoal),

	( MActivationPtr = yes(ActivationPtr1) ->
		generate_call(ModuleInfo, "semi_call_port_code", 4,
			[ProcDescVar, TopCSD, MiddleCSD, ActivationPtr1],
			[TopCSD, MiddleCSD, ActivationPtr1], CallPortCode),
		generate_call(ModuleInfo, "semi_exit_port_code", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], [], ExitPortCode),
		generate_call(ModuleInfo, "semi_fail_port_code", 3,
			[TopCSD, MiddleCSD, ActivationPtr1], no, failure,
			FailPortCode),
		NewNonlocals = list_to_set([MiddleCSD, ActivationPtr1])
	;
		generate_call(ModuleInfo, "semi_call_port_code", 3,
			[ProcDescVar, TopCSD, MiddleCSD],
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
		BindProcDescVarGoal,
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
	proc_info_set_goal(Proc2, Goal, Proc),
	ProcDescList = [ProcDesc].

:- pred transform_non_proc(module_info, pred_proc_id, proc_info, proc_info,
		list(cons_id)).
:- mode transform_non_proc(in, in, in, out, out) is det.

transform_non_proc(ModuleInfo, PredProcId, Proc0, Proc, ProcDescList) :-
	proc_info_goal(Proc0, Goal0),
	Goal0 = _ - GoalInfo0,
	proc_info_varset(Proc0, Vars0),
	proc_info_vartypes(Proc0, VarTypes0),
	CPointerType = functor(atom("c_pointer"), [], context_init),
	varset__new_var(Vars0, TopCSD, Vars1),
	map__set(VarTypes0, TopCSD, CPointerType, VarTypes1),
	varset__new_var(Vars1, MiddleCSD, Vars2),
	map__set(VarTypes1, MiddleCSD, CPointerType, VarTypes2),
	varset__new_var(Vars2, ProcDescVar, Vars3),
	map__set(VarTypes2, ProcDescVar, CPointerType, VarTypes3),
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

	PInfo0 = deep_info(ModuleInfo, MiddleCSD, 0, [], Vars5, VarTypes5),

	transform_goal([], Goal0, TransformedGoal, PInfo0, PInfo),

	Vars = PInfo^vars,
	VarTypes = PInfo^var_types,
	CallSites = PInfo^call_sites,

	ProcDesc = deep_profiling_procedure_data(PredProcId, CallSites),
	generate_unify(ProcDesc, ProcDescVar, BindProcDescVarGoal),

	( MOldActivationPtr = yes(OldOutermostProcDyn2) ->
		generate_call(ModuleInfo, "non_call_port_code", 5,
			[ProcDescVar, TopCSD, MiddleCSD,
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
			[ProcDescVar, TopCSD, MiddleCSD, NewOutermostProcDyn],
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
		BindProcDescVarGoal,
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
	proc_info_set_goal(Proc2, Goal, Proc),
	ProcDescList = [ProcDesc].

:- type deep_info
	--->	deep_info(
	    module_info		:: module_info,
	    current_csd		:: prog_var,
	    next_site_num	:: int,
	    call_sites		:: list(callsite),
	    vars		:: prog_varset,
	    var_types		:: vartypes
	).

:- pred transform_goal(goalPath, hlds_goal, hlds_goal, deep_info, deep_info).
:- mode transform_goal(in, in, out, in, out) is det.

transform_goal(Path, conj(Goals0) - Info, conj(Goals) - Info)  -->
    transform_conj(0, Path, Goals0, Goals).

transform_goal(Path, par_conj(Goals0, SM) - Info,
	par_conj(Goals, SM) - Info) -->
    transform_conj(0, Path, Goals0, Goals).

transform_goal(Path, switch(Var, CF, Cases0, SM) - Info,
	switch(Var, CF, Cases, SM) - Info) -->
    transform_switch(0, Path, Cases0, Cases).

transform_goal(Path, disj(Goals0, SM) - Info, disj(Goals, SM) - Info) -->
    transform_disj(0, Path, Goals0, Goals).

transform_goal(Path, not(Goal0) - Info, not(Goal) - Info) -->
    transform_goal([(not)|Path], Goal0, Goal).

transform_goal(Path, some(QVars, CR, Goal0) - Info,
	some(QVars, CR, Goal) - Info) -->
    transform_goal([(some)|Path], Goal0, Goal).

transform_goal(Path, if_then_else(IVars, Cond0, Then0, Else0, SM) - Info,
	if_then_else(IVars, Cond, Then, Else, SM) - Info) -->
    transform_goal([if_then_else(0)|Path], Cond0, Cond),
    transform_goal([if_then_else(1)|Path], Then0, Then),
    transform_goal([if_then_else(2)|Path], Else0, Else).

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

:- pred transform_conj(int, goalPath, list(hlds_goal), list(hlds_goal),
		deep_info, deep_info).
:- mode transform_conj(in, in, in, out, in, out) is det.

transform_conj(_, _, [], []) --> [].
transform_conj(N, Path, [Goal0|Goals0], [Goal|Goals]) -->
    transform_goal([conj(N)|Path], Goal0, Goal),
    transform_conj(N + 1, Path, Goals0, Goals).

:- pred transform_disj(int, goalPath, list(hlds_goal), list(hlds_goal),
		deep_info, deep_info).
:- mode transform_disj(in, in, in, out, in, out) is det.

transform_disj(_, _, [], []) --> [].
transform_disj(N, Path, [Goal0|Goals0], [Goal|Goals]) -->
    transform_goal([disj(N)|Path], Goal0, Goal),
    transform_disj(N + 1, Path, Goals0, Goals).

:- pred transform_switch(int, goalPath, list(case), list(case),
		deep_info, deep_info).
:- mode transform_switch(in, in, in, out, in, out) is det.

transform_switch(_, _, [], []) --> [].
transform_switch(N, Path, [case(Id, Goal0)|Goals0], [case(Id, Goal)|Goals]) -->
    transform_goal([switch(N)|Path], Goal0, Goal),
    transform_switch(N + 1, Path, Goals0, Goals).

:- pred wrap_call(goalPath, hlds_goal, hlds_goal, deep_info, deep_info).
:- mode wrap_call(in, in, out, in, out) is det.

wrap_call(Path, Goal0, Goal, DeepInfo0, DeepInfo) :-
	Goal0 = GoalExpr - GoalInfo0,
	ModuleInfo = DeepInfo0^module_info,
	MiddleCSD = DeepInfo0^current_csd,

	goal_info_get_nonlocals(GoalInfo0, NonLocals0),
	NewNonlocals = set__make_singleton_set(MiddleCSD),
	NonLocals = union(NonLocals0, NewNonlocals),
	goal_info_set_nonlocals(GoalInfo0, NonLocals, GoalInfo),

	SiteNum = DeepInfo0^next_site_num,
	varset__new_var(DeepInfo0^vars, SiteNumVar, Vars),
	CPointerType = functor(atom("int"), [], context_init),
	map__set(DeepInfo0^var_types, SiteNumVar, CPointerType, VarTypes),
	generate_unify(int_const(SiteNum), SiteNumVar, SiteNumVarGoal),
	DeepInfo1 = DeepInfo0^vars := Vars,
	DeepInfo2 = DeepInfo1^var_types := VarTypes,

	classifyCall(ModuleInfo, GoalExpr, CallKind),
	(
		CallKind = normal(PredProcId),
		generate_call(ModuleInfo, "make_new_csd_for_normal_call", 2,
			[MiddleCSD, SiteNumVar], [], PrepareGoal),
		CallSite = normal(PredProcId, Path),
		Goal1 = Goal0,
		DeepInfo3 = DeepInfo2
	;
		CallKind = special(_PredProcId, TypeInfoVar),
		generate_call(ModuleInfo, "make_new_csd_for_special_call", 3,
			[MiddleCSD, SiteNumVar, TypeInfoVar], [], PrepareGoal),
		CallSite = call(Path),
		Goal1 = Goal0,
		DeepInfo3 = DeepInfo2
	;
		CallKind = generic(Generic),
		(
			Generic = higher_order(ClosureVar, _, _)
		;
			Generic = class_method(ClosureVar, _, _, _)
		;
			Generic = aditi_builtin(_, _),
			error("deep profiling and aditi do not mix")
		),
		generate_call(ModuleInfo, "make_new_csd_for_ho_call", 3,
			[MiddleCSD, SiteNumVar, ClosureVar], [], PrepareGoal),
		CallSite = call(Path),
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
	DeepInfo4 = DeepInfo3^next_site_num := SiteNum + 1,
	DeepInfo = DeepInfo4^call_sites := DeepInfo1^call_sites ++ [CallSite].

:- pred transform_higher_order_call(code_model, hlds_goal, hlds_goal,
		deep_info, deep_info).
:- mode transform_higher_order_call(in, in, out, in, out) is det.

transform_higher_order_call(CodeModel, Goal0, Goal, DeepInfo0, DeepInfo) :-
	IntType = functor(atom("int"), [], context_init),
	CPointerType = functor(atom("c_pointer"), [], context_init),
	varset__new_var(DeepInfo0^vars, SavedCountVar, Vars1),
	map__set(DeepInfo0^var_types, SavedCountVar, IntType, VarTypes1),
	varset__new_var(Vars1, SavedPtrVar, Vars),
	map__set(VarTypes1, SavedPtrVar, CPointerType, VarTypes),
	DeepInfo1 = DeepInfo0^vars := Vars,
	DeepInfo = DeepInfo1^var_types := VarTypes,
	Goal0 = _ - GoalInfo,
	MiddleCSD = DeepInfo^current_csd,
	generate_call(DeepInfo^module_info, "save_and_zero_activation_info", 3,
		[MiddleCSD, SavedCountVar, SavedPtrVar],
		[SavedCountVar, SavedPtrVar], SaveStuff),
	generate_call(DeepInfo^module_info, "reset_activation_info", 3,
		[MiddleCSD, SavedCountVar, SavedPtrVar], [], RestoreStuff),
	generate_call(DeepInfo^module_info, "rezero_activation_info", 1,
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

:- pred wrap_foreign_code(goalPath, hlds_goal, hlds_goal, deep_info, deep_info).
:- mode wrap_foreign_code(in, in, out, in, out) is det.

wrap_foreign_code(Path, Goal0, Goal, DeepInfo0, DeepInfo) :-
	Goal0 = _ - GoalInfo0,
	ModuleInfo = DeepInfo0^module_info,
	MiddleCSD = DeepInfo0^current_csd,

	goal_info_get_nonlocals(GoalInfo0, NonLocals0),
	NewNonlocals = set__make_singleton_set(MiddleCSD),
	NonLocals = union(NonLocals0, NewNonlocals),
	goal_info_set_nonlocals(GoalInfo0, NonLocals, GoalInfo),

	SiteNum = DeepInfo0^next_site_num,
	varset__new_var(DeepInfo0^vars, SiteNumVar, Vars),
	CPointerType = functor(atom("int"), [], context_init),
	map__set(DeepInfo0^var_types, SiteNumVar, CPointerType, VarTypes),
	generate_unify(int_const(SiteNum), SiteNumVar, SiteNumVarGoal),

	generate_call(ModuleInfo, "make_new_csd_for_foreign_call", 2,
		[MiddleCSD, SiteNumVar], [], PrepareGoal),
	CallSite = call(Path),

	Goal = conj([
		SiteNumVarGoal,
		PrepareGoal,
		Goal0
	]) - GoalInfo,
	DeepInfo1 = DeepInfo0^next_site_num := SiteNum + 1,
	DeepInfo2 = DeepInfo1^call_sites := DeepInfo1^call_sites ++ [CallSite],
	DeepInfo3 = DeepInfo2^vars := Vars,
	DeepInfo = DeepInfo3^var_types := VarTypes.

:- type callClass
			% For normal first order calls
	--->	normal(pred_proc_id)
			% For calls to unify/2 and compare/3
	;	special(pred_proc_id, prog_var)
			% For higher order and typeclass method calls
	;	generic(generic_call)
	.

:- pred classifyCall(module_info, hlds_goal_expr, callClass).
:- mode classifyCall(in, in, out) is det.

classifyCall(ModuleInfo, Expr, Class) :-
    ( Expr = call(PredId, ProcId, Args, _, _, _) ->
	module_info_get_predicate_table(ModuleInfo, PredTable),
	mercury_public_builtin_module(MercuryBuiltin),
	( predicate_table_search_pred_m_n_a(PredTable, MercuryBuiltin,
			"unify", 2, [PredId]),
		Args = [TypeInfoVar|_]
	->
		Class = special(proc(PredId, ProcId), TypeInfoVar)
	; predicate_table_search_pred_m_n_a(PredTable, MercuryBuiltin,
			"compare", 3, [PredId]),
		Args = [TypeInfoVar|_]
	->
		Class = special(proc(PredId, ProcId), TypeInfoVar)
	;
		Class = normal(proc(PredId, ProcId))
	)
    ; Expr = generic_call(Generic, _, _, _) ->
    	Class = generic(Generic)
    ;
    	error("unexpected goal type in classifyCall/2")
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

:- pred generate_call(module_info, string, int, list(prog_var), list(prog_var),
		hlds_goal).
:- mode generate_call(in, in, in, in, in, out) is det.

generate_call(ModuleInfo, Name, Arity, ArgVars, OutputVars, Goal) :-
	generate_call(ModuleInfo, Name, Arity, ArgVars, yes(OutputVars), det, Goal).

:- pred generate_call(module_info, string, int, list(prog_var),
		maybe(list(prog_var)), determinism, hlds_goal).
:- mode generate_call(in, in, in, in, in, in, out) is det.

generate_call(ModuleInfo, Name, Arity, ArgVars, MOutputVars, Detism, Goal) :-
	getPPId(ModuleInfo, Name, Arity, proc(PredId, ProcId)),
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

:- pred generate_unify(cons_id, prog_var, hlds_goal).
:- mode generate_unify(in, in, out) is det.

generate_unify(ConsId, Var, Goal) :-
    Ground = ground(shared, none),
    NonLocals = set__make_singleton_set(Var),
    instmap_delta_from_assoc_list([Var - ground(shared, none)], InstMapDelta),
    Determinism = det,
    goal_info_init(NonLocals, InstMapDelta, Determinism, GoalInfo),
    Goal = unify(Var, functor(ConsId, []),
    		(free -> Ground) - (Ground -> Ground),
		construct(Var, ConsId, [], [], construct_statically([]),
			cell_is_shared, no),
		unify_context(explicit, [])) - GoalInfo.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

generate_llds_proc_descriptions(_ModuleInfo, [], [], CellNum, CellNum).
generate_llds_proc_descriptions(ModuleInfo, [CId|CIds], [Data|Datas],
		CellNum0, CellNum) :-
    generate_llds_proc_description(ModuleInfo, CId, Data, CellNum0, CellNum1),
    generate_llds_proc_descriptions(ModuleInfo, CIds, Datas, CellNum1, CellNum).

:- pred generate_llds_proc_description(module_info, cons_id, comp_gen_c_data,
		counter, counter).
:- mode generate_llds_proc_description(in, in, out, in, out) is det.

generate_llds_proc_description(ModuleInfo, ConsId, Data, CellNum0, CellNum) :-
    ( ConsId = deep_profiling_procedure_data(PPId, CallSites) ->
    	PPId = proc(PredId, ProcId),
    	module_info_name(ModuleInfo, ModuleName),
	code_util__make_proc_label(ModuleInfo, PredId, ProcId, ProcLabel),
	DataName = deep_profiling_procedure_data(ProcLabel),
	make_proc_layout_ref(ModuleInfo, PPId, CallerLayout),
    	length(CallSites, NumCallSites),
    	NumCallSitesTerm = const(int_const(NumCallSites)),
	map_foldl((pred(CallSite::in, yes(CallSiteTerm)::out,
		C0::in, C1::out) is det :-
	    allocate(N, C0, C1),
	    (
	    	CallSite = normal(_CSPPId, Path),
		stringify_path(Path, PathStr),
		Kind = 0
	    ;
	    	CallSite = call(Path),
		stringify_path(Path, PathStr),
		Kind = 1
	    % XXX handle callback and typeclasses
	    ),
	    CallSiteTerm = create(0,
		    [yes(const(int_const(Kind))),
			    yes(const(string_const(PathStr)))],
		    uniform(no), must_be_static, N, "deep profiling", no)
	), CallSites, CallSiteTerms, CellNum0, CellNum1),
	allocate(M, CellNum1, CellNum),
	(
	    CallSiteTerms = [_|_],
	    CallSitesTerm = create(0, CallSiteTerms, uniform(no),
	    	must_be_static, M, "deep profiling", no)
	;
	    CallSiteTerms = [],
	    CallSitesTerm = const(int_const(0))
	),
	module_info_globals(ModuleInfo, Globals),
	globals__lookup_bool_option(Globals,
		use_activation_counts, UseActivationCounts),
	( UseActivationCounts = yes ->
		ActivationCountTerm = yes(const(int_const(0))),
		ActivationPtrTerm = yes(const(int_const(0))),
		ActivationStuff = [ActivationCountTerm, ActivationPtrTerm]
	;
		ActivationPtrTerm = yes(const(int_const(0))),
		ActivationStuff = [ActivationPtrTerm]
	),
    	Data = comp_gen_c_data(ModuleName, DataName, no,
		[yes(CallerLayout), yes(NumCallSitesTerm), yes(CallSitesTerm) |
			ActivationStuff], uniform(no), [])
    ;
    	error("generate_llds_proc_description/3 called with non deep_profiling")
    ).

:- pred make_proc_layout_ref(module_info, pred_proc_id, rval).
:- mode make_proc_layout_ref(in, in, out) is det.

make_proc_layout_ref(ModuleInfo, PPId, RVal) :-
    PPId = proc(PredId, ProcId),
    predicate_module(ModuleInfo, PredId, ModuleName),
    unqualify_name(ModuleName, ModuleStr),
    predicate_name(ModuleInfo, PredId, PredName),
    predicate_arity(ModuleInfo, PredId, PredArity),
    proc_id_to_int(ProcId, ProcNum),
    format("%s:%s/%d-%d",
    		[s(ModuleStr), s(PredName), i(PredArity), i(ProcNum)],
		Str),
    RVal = const(string_const(Str)).

:- pred stringify_path(list(goalPathElem), string).
:- mode stringify_path(in, out) is det.

stringify_path(Elems, Str) :-
    map((pred(Elem::in, Piece::out) is det :-
    	(
	    Elem = conj(I),
	    format("c%d;", [i(I)], Piece)
	;
	    Elem = disj(I),
	    format("d%d;", [i(I)], Piece)
	;
	    Elem = switch(I),
	    format("s%d;", [i(I)], Piece)
	;
	    Elem = if_then_else(I),
	    format("i%d;", [i(I)], Piece)
	;
	    Elem = (not),
	    Piece = "n;"
	;
	    Elem = (some),
	    Piece = "q;"
	)
    ), Elems, Pieces),
    append_list(Pieces, Str).

:- pred getPPId(module_info, string, int, pred_proc_id).
:- mode getPPId(in, in, in, out) is det.

getPPId(ModuleInfo, Name, Arity, proc(PredId, ProcId)) :-
    ModuleName = unqualified("profiling_builtin"),
    module_info_get_predicate_table(ModuleInfo, PredTable),
    (
    	predicate_table_search_pred_m_n_a(PredTable,
		ModuleName, Name, Arity, PredIds)
    ->
    	(
	    PredIds = [PredId|_],
	    predicate_table_get_preds(PredTable, Preds),
	    lookup(Preds, PredId, PredInfo),
	    pred_info_procids(PredInfo, ProcIds),
	    (
	    	ProcIds = [],
		error("Couldn't find proc_ids")
	    ;
	    	ProcIds = [ProcId|_]
	    )
	;
	    PredIds = [],
	    error("Couldn't find unique pred_id")
	)
    ;
    	format("couldn't find pred_id for `%s'/%d", [s(Name), i(Arity)], Msg),
	error(Msg)
    ).

