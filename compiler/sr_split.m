%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_indirect
% Main authors: nancy
% 
% Determine the indirect reuse.  This requires a fixpoint computation.
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_split.
:- interface.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module structure_reuse__sr_data.

:- import_module std_util, io, string.

	% create_multiple_versions(ReuseHLDS, FinalHLDS).
	% Starting from the VirginHLDS, it computes a new HLDS where for
	% each procedure having conditional reuse (ReuseHLDS), a new
	% separate reuse-procedure is added. The calls can then also 
	% be corrected so that they point to the correct reuse-versions.
:- pred sr_split__create_multiple_versions(reuse_condition_table::in,
		reuse_condition_table::out, module_info::in,
		module_info::out, io__state::di, io__state::uo) is det.

:- pred create_reuse_pred(pred_proc_id::in, memo_reuse::in,
		maybe(hlds_goal)::in,
		pred_proc_id::out, 
		reuse_condition_table::in, reuse_condition_table::out, 
		module_info::in, module_info::out) is det.

:- pred reuse_predicate_name(string).
:- mode reuse_predicate_name(in) is semidet.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds__hlds_data.
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__prog_data.
:- import_module parse_tree__prog_util. 
:- import_module structure_reuse__sr_data. 

:- import_module bool, std_util, require, list, set, map.

reuse_predicate_name(PredName) :- 
	string__prefix(PredName, "reuse__").

sr_split__create_multiple_versions(!ReuseTable, !ModuleInfo, !IO) :- 
		% compute the strongly connected components
	create_versions(!ReuseTable, !ModuleInfo, !IO), 
	reprocess_all_goals(!.ReuseTable, !ModuleInfo).

	% reprocess each of the procedures to make sure that all calls
	% to reuse preds are correct. 
:- pred reprocess_all_goals(reuse_condition_table::in, 
		module_info::in, module_info::out) is det.

reprocess_all_goals(ReuseTable, HLDS0, HLDS) :- 
	module_info_predids(HLDS0, PredIds), 
	list__foldl(
		reprocess_all_goals_2(ReuseTable),
		PredIds,
		HLDS0, 
		HLDS).

:- pred reprocess_all_goals_2(reuse_condition_table::in, pred_id::in, 
		module_info::in, module_info::out) is det. 
reprocess_all_goals_2(ReuseTable, PredId, HLDS0, HLDS) :- 
	module_info_pred_info(HLDS0, PredId, PredInfo0), 
	pred_info_procids(PredInfo0, ProcIds), 
	pred_info_procedures(PredInfo0, Procedures0), 
	list__foldl(
		reprocess_all_goals_3(ReuseTable, HLDS0, PredId),
		ProcIds,
		Procedures0, 
		Procedures
		), 
	pred_info_set_procedures(PredInfo0, Procedures, PredInfo), 
	module_info_set_pred_info(HLDS0, PredId, PredInfo, HLDS). 

:- pred reprocess_all_goals_3(reuse_condition_table::in, 
		module_info::in, pred_id::in, proc_id::in, 
		proc_table::in, proc_table::out) is det.
reprocess_all_goals_3(ReuseTable, HLDS, PredId, ProcId, 
		ProcTable0, ProcTable) :- 
	map__lookup(ProcTable0, ProcId, ProcInfo0), 
	(
		Memo = reuse_condition_table_search(proc(PredId, ProcId), 
			ReuseTable), 
		Memo = yes(Conditions)
	->
		proc_info_goal(ProcInfo0, Goal0), 
			% If the conditions on the reuse are empty, then
			% we have unconditional reuse, so make sure when
			% processing the goal we don't do any actions
			% which would introduce a condition.
		( Conditions = [] ->
			LocalReuseOnly = yes
		;
			LocalReuseOnly = no
		),
		process_goal(LocalReuseOnly, Goal0, Goal, HLDS, _), 
		proc_info_set_goal(ProcInfo0, Goal, ProcInfo), 
		map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable)
	;
		ProcTable = ProcTable0
	).


:- pred create_versions(reuse_condition_table::in, 
		reuse_condition_table::out, 
		module_info::in, module_info::out, 
		io__state::di, io__state::uo) is det.

create_versions(!ReuseTable, !ModuleInfo, !IO) :- 
	module_info_predids(!.ModuleInfo, PredIds), 
	list__foldl3(create_versions_2, PredIds, !ReuseTable, 
		!ModuleInfo, !IO). 

:- pred create_versions_2(pred_id::in, 
		reuse_condition_table::in, 
		reuse_condition_table::out, 
		module_info::in, module_info::out, 
		io__state::di, io__state::uo) is det.

create_versions_2(PredId, !ReuseTable, !ModuleInfo, !IO) :- 
	module_info_pred_info(!.ModuleInfo, PredId, PredInfo0), 
	pred_info_procids(PredInfo0, ProcIds), 
	list__foldl3(
		pred(Id::in, RT0::in, RT::out, H0::in, H::out, 
			IOin::di, IOout::uo) is det :- 
		(
			create_versions_3(proc(PredId, Id), RT0, RT, 
				H0, H, IOin, IOout)
		),
		ProcIds, !ReuseTable, !ModuleInfo, !IO).

:- pred create_versions_3(pred_proc_id::in, 
		reuse_condition_table::in, 
		reuse_condition_table::out, 
		module_info::in, module_info::out, 
		io__state::di, io__state::uo) is det.

create_versions_3(PredProcId, !ReuseTable, WorkingHLDS, HLDS, !IO):- 
	module_info_pred_proc_info(WorkingHLDS, PredProcId, 
				PredInfo0, ProcInfo0),
	proc_info_goal(ProcInfo0, ReuseGoal), 

	(
		Memo = reuse_condition_table_search(PredProcId, !.ReuseTable), 
		Memo = yes(_)
	-> 
		(
			memo_reuse_is_conditional(Memo) 
		->
			% fetch the reuse goal

			create_reuse_pred_info(PredProcId, yes(ReuseGoal), 
					PredInfo0, ProcInfo0,
					ReusePredInfo, 
					ReuseProcId, ReuseName),
			module_info_get_predicate_table(WorkingHLDS,
					PredTable0),
			module_info_structure_reuse_info(WorkingHLDS,
					StrReuseInfo0),
			StrReuseInfo0 = structure_reuse_info(ReuseMap0),
			predicate_table_insert(PredTable0, ReusePredInfo,
					ReusePredId, PredTable),

			memo_reuse_simplify(Memo, SimplifiedMemo),
			reuse_condition_table_set(
				proc(ReusePredId, ReuseProcId), 
					SimplifiedMemo, !ReuseTable), 

			(
				map__search(ReuseMap0, PredProcId, _)
			->
				PredProcId = proc(PredId, ProcId), 
				Msg1 = "% Adding already existing procedure: ", 
				write_proc_progress_message(Msg1, 
					PredId, ProcId, WorkingHLDS, !IO),
				HLDS = WorkingHLDS

			%	pred_id_to_int(PredId, PredIdInt), 
			%	proc_id_to_int(ProcId, ProcIdInt), 
			%	string__append_list([
			%		"(sr_split) ", 
			%		"Reuse map already ", 
			%		"contains id: proc(", 
			%		string__int_to_string(PredIdInt),
			%		", ", 
			%		string__int_to_string(ProcIdInt), 
			%		").\n"], Msg),
				% error(Msg)
			; 
			 	map__det_insert(ReuseMap0, PredProcId,
					proc(ReusePredId, 
						ReuseProcId) - ReuseName,
					ReuseMap),
				StrReuseInfo = structure_reuse_info(ReuseMap),
				module_info_set_structure_reuse_info(
					WorkingHLDS, StrReuseInfo, 
					WorkingHLDS1),
				module_info_set_predicate_table(WorkingHLDS1, 
					PredTable, WorkingHLDS2),
				module_info_set_pred_proc_info(WorkingHLDS2,
					PredProcId, PredInfo0, ProcInfo0, HLDS)
			),

				% Change the conditions on this version
				% to be unconditional.  This ensures
				% that when process_goal is run on this
				% procedure only the reuse which is
				% unconditional is kept.
			reuse_condition_table_set(PredProcId, 
					yes([]), !ReuseTable)

		;
			% memo_reuse is unconditional -- perfect -- 
			% nothing to be done! (processing the goal is
			% done separately). 
			% HLDS = WorkingHLDS
			% instead of keeping as is, the potential reuses
			% have to be converted to real reuses. 
			convert_potential_reuse_to_reuse(ReuseGoal, 
					ReuseGoal1),
			proc_info_set_goal(ProcInfo0, ReuseGoal1, 
					ProcInfo2), 
			module_info_set_pred_proc_info(WorkingHLDS, 
				PredProcId, PredInfo0, ProcInfo2, HLDS)
			
		)
	;
		% restore the old status of the procedure
		% module_info_set_pred_proc_info(WorkingHLDS, PredProcId,
	       	% 		PredInfo0, CleanProcInfo, HLDS)
		HLDS = WorkingHLDS
	).

	
create_reuse_pred(PredProcId, TransOptReuse, MaybeHLDS_GOAL, 
		proc(ReusePredId, ReuseProcId), 
		!ReuseTable, !ModuleInfo) :- 
	module_info_pred_proc_info(!.ModuleInfo, PredProcId, PredInfo0, 
					ProcInfo0),
	(
		memo_reuse_is_conditional(TransOptReuse) 
	->
		create_reuse_pred_info(PredProcId,
			MaybeHLDS_GOAL, PredInfo0, ProcInfo0,
			ReusePredInfo, 
			ReuseProcId, ReuseName),

		module_info_get_predicate_table(!.ModuleInfo, PredTable0),
		predicate_table_insert(PredTable0, ReusePredInfo,
			ReusePredId, PredTable),

		memo_reuse_simplify(TransOptReuse, SimplifiedTabledReuse),
		reuse_condition_table_set(proc(ReusePredId, ReuseProcId), 
			SimplifiedTabledReuse, !ReuseTable),

		module_info_structure_reuse_info(!.ModuleInfo, StrReuseInfo0),
		StrReuseInfo0 = structure_reuse_info(ReuseMap0),
		map__det_insert(ReuseMap0, PredProcId,
			proc(ReusePredId, ReuseProcId) - ReuseName,
			ReuseMap),
		StrReuseInfo = structure_reuse_info(ReuseMap),
		module_info_set_structure_reuse_info(!.ModuleInfo,
			StrReuseInfo, !:ModuleInfo),
		module_info_set_predicate_table(!.ModuleInfo, 
			PredTable, !:ModuleInfo)
	% ; contains_unconditional_reuse(TREUSE) ->
	;
		PredProcId = proc(PredId, ProcId), 
		ReuseProcId = ProcId, 
		ReusePredId = PredId, 
		% is unconditional, or has no reuse, so no simplify required: 
		reuse_condition_table_set(PredProcId, TransOptReuse,
			!ReuseTable), 
		(
			MaybeHLDS_GOAL = yes(HLDS_GOAL),
			proc_info_set_goal(ProcInfo0, HLDS_GOAL, ProcInfo)
		;
			MaybeHLDS_GOAL = no,
			ProcInfo = ProcInfo0
		),
		module_info_set_pred_proc_info(!.ModuleInfo, PredProcId, 
				PredInfo0, ProcInfo, !:ModuleInfo)
	).

:- pred create_reuse_pred_info(pred_proc_id::in,
		maybe(hlds_goal)::in, pred_info::in, proc_info::in,
		pred_info::out,
		proc_id::out, sym_name::out) is det.

create_reuse_pred_info(PredProcId, MaybeReuseGoal, PredInfo, ProcInfo0,
		ReusePredInfo, 
		ReuseProcId, SymName) :-
	(
		MaybeReuseGoal = yes(PotReuseGoal),
		convert_potential_reuse_to_reuse(PotReuseGoal, ReuseGoal),
		proc_info_set_goal(ProcInfo0, ReuseGoal, ReuseProcInfo)
	;
		MaybeReuseGoal = no,
		ReuseProcInfo = ProcInfo0
	),
	pred_info_module(PredInfo, ModuleName),
	pred_info_name(PredInfo, Name),
	pred_info_arg_types(PredInfo, TypeVarSet, ExistQVars, Types),
	Cond = true,
	pred_info_context(PredInfo, PredContext),
	pred_info_import_status(PredInfo, Status),
	pred_info_get_markers(PredInfo, Markers),
	pred_info_get_is_pred_or_func(PredInfo, PredOrFunc),
	pred_info_get_class_context(PredInfo, ClassContext),
	pred_info_get_aditi_owner(PredInfo, Owner),

	set__init(Assertions),

	PredProcId = proc(_PredId, ProcId),
	proc_id_to_int(ProcId, ProcIdInt),

	Line = 0,
	Counter = ProcIdInt,

	make_pred_name_with_context(ModuleName, "reuse", PredOrFunc, Name,
		Line, Counter, SymName),

	pred_info_create(ModuleName, SymName, TypeVarSet, ExistQVars, Types,
			Cond, PredContext, Status, Markers, PredOrFunc,
			ClassContext, Owner, Assertions, ReuseProcInfo, 
			ReuseProcId, ReusePredInfo).

%-----------------------------------------------------------------------------%

:- pred convert_potential_reuse_to_reuse(hlds_goal::in, 
						hlds_goal::out) is det.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = conj(Goals0),
	list__map(convert_potential_reuse_to_reuse, Goals0, Goals), 
	Goal = conj(Goals), 
	GoalInfo = GoalInfo0.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = call(_,_,_,_,_,_),
	Goal = Goal0, 
	goal_info_get_reuse(GoalInfo0, Reuse0), 
	convert_reuse(Reuse0, Reuse), 
	goal_info_set_reuse(Reuse, GoalInfo0, GoalInfo).
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = generic_call(_,_,_,_),
	Goal = Goal0, 
	GoalInfo = GoalInfo0.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = switch(X, Y, Cases0),
	list__map(
		pred(C0::in, C::out) is det:-
			( C0 = case(Id, G0), 
			convert_potential_reuse_to_reuse(G0, G), 
			C = case(Id, G)),
		Cases0,
		Cases),
	Goal = switch(X, Y, Cases),
	GoalInfo = GoalInfo0.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = unify(_,_,_,_,_),
	Goal = Goal0, 
	goal_info_get_reuse(GoalInfo0, Reuse0), 
	convert_reuse(Reuse0,Reuse), 
	goal_info_set_reuse(Reuse, GoalInfo0, GoalInfo).
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = disj(Goals0),
	list__map(convert_potential_reuse_to_reuse, Goals0, Goals), 
	Goal = disj(Goals), 
	GoalInfo = GoalInfo0.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = not(NegGoal0),
	convert_potential_reuse_to_reuse(NegGoal0, NegGoal), 
	Goal = not(NegGoal), 
	GoalInfo = GoalInfo0. 
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = some(A, B, SG0), 
	convert_potential_reuse_to_reuse(SG0, SG), 
	Goal = some(A, B, SG),
	GoalInfo = GoalInfo0. 
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = if_then_else(A, If0, Then0, Else0),
	convert_potential_reuse_to_reuse(If0, If), 
	convert_potential_reuse_to_reuse(Then0, Then), 
	convert_potential_reuse_to_reuse(Else0, Else), 
	Goal = if_then_else(A, If, Then, Else),
	GoalInfo0 = GoalInfo. 
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = foreign_proc(_,_,_,_,_,_,_),
	Goal = Goal0, 
	GoalInfo = GoalInfo0.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = par_conj(_),
	Goal = Goal0, 
	GoalInfo = GoalInfo0.
convert_potential_reuse_to_reuse(Goal0 - GoalInfo0, Goal - GoalInfo) :- 
	Goal0 = shorthand(_),
	Goal = Goal0, 
	GoalInfo = GoalInfo0.

:- pred convert_reuse(reuse_goal_info::in, reuse_goal_info::out) is det.
convert_reuse(R0, R):- R0 = empty, R = R0.
convert_reuse(R0, R):- R0 = potential_reuse(S), R = reuse(S).
convert_reuse(R0, R):- R0 = reuse(_), R = R0.

%-----------------------------------------------------------------------------%
:- pred process_goal(bool::in, hlds_goal::in, hlds_goal::out,
		module_info::in, module_info::out) is det.

process_goal(LocalReuseOnly, Goal0 - GoalInfo0, Goal - GoalInfo) -->
	{ Goal0 = call(PredId0, ProcId0, Args, Builtin, MaybeContext, Name0) },
	=(ModuleInfo),
	{ module_info_structure_reuse_info(ModuleInfo, ReuseInfo) },
	{ ReuseInfo = structure_reuse_info(ReuseMap) },
	{
		goal_info_get_reuse(GoalInfo0, Reuse),
		Reuse = reuse(SR),
		SR = reuse_call(ConditionalReuse),
		map__search(ReuseMap, proc(PredId0, ProcId0), Result)
	->
		( ConditionalReuse = yes, LocalReuseOnly = yes ->
			PredId = PredId0,
			ProcId = ProcId0,
			Name = Name0,
			%goal_info_set_reuse(GoalInfo0, reuse(no_reuse),
					%GoalInfo)
			goal_info_set_reuse(
				potential_reuse(SR),
			% reuse(missed_reuse_call(["Conditional call."])),
				GoalInfo0,
				GoalInfo)
		;
			Result = proc(PredId, ProcId) - Name,
			GoalInfo = GoalInfo0
		)
	;
		PredId = PredId0,
		ProcId = ProcId0,
		Name = Name0,
		GoalInfo = GoalInfo0
	},
	{ Goal = call(PredId, ProcId, Args, Builtin, MaybeContext, Name) }.

process_goal(LocalReuseOnly, Goal0 - GoalInfo0, Goal - GoalInfo) -->
	{ Goal0 = unify(UVar, Rhs, Mode, Unification0, Ctxt) },
	{
		goal_info_get_reuse(GoalInfo0, Reuse),
		Reuse = reuse(SR),
		SR = cell_reused(ReuseVar,
				ConditionalReuse, ConsIds, ReuseFields)
	->
		( ConditionalReuse = yes, LocalReuseOnly = yes ->
			Unification = Unification0,
			goal_info_set_reuse(
				potential_reuse(SR),
				GoalInfo0, 
				GoalInfo)
		;
			(
				Unification0 = construct(Var, ConsId, Vars,
						Modes, _HTC, IsUnique, MaybeRL)
			->
				HTC = reuse_cell(cell_to_reuse(ReuseVar,
						ConsIds, ReuseFields)),
				Unification = construct(Var, ConsId, Vars,
						Modes, HTC, IsUnique, MaybeRL)
			;
				error("sr_split__process_goal: not a construction unification")
			),
			GoalInfo = GoalInfo0
		)
	;
		Unification = Unification0,
		GoalInfo = GoalInfo0
	},
	{ Goal = unify(UVar, Rhs, Mode, Unification, Ctxt) }.
process_goal(_, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
process_goal(_, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = foreign_proc(_, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
process_goal(_, Goal0 - _GoalInfo, _) -->
	{ Goal0 = shorthand(_) },
	{ error("structure_reuse: shorthand.\n") }.

process_goal(LocalReuseOnly, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0) },
	process_goal(LocalReuseOnly, If0, If),
	process_goal(LocalReuseOnly, Then0, Then),
	process_goal(LocalReuseOnly, Else0, Else),
	{ Goal = if_then_else(Vars, If, Then, Else) }.

process_goal(LocalReuseOnly, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0) },
	process_goal_cases(LocalReuseOnly, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases) }.

process_goal(LocalReuseOnly, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	process_goal(LocalReuseOnly, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

process_goal(LocalReuseOnly, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	process_goal(LocalReuseOnly, Goal0, Goal).
process_goal(LocalReuseOnly, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	process_goal_list(LocalReuseOnly, Goal0s, Goals).
process_goal(LocalReuseOnly, disj(Goal0s) - GoalInfo,
		disj(Goals) - GoalInfo) -->
	process_goal_list(LocalReuseOnly, Goal0s, Goals).
process_goal(LocalReuseOnly, par_conj(Goal0s) - GoalInfo,
		par_conj(Goals) - GoalInfo) -->
	process_goal_list(LocalReuseOnly, Goal0s, Goals).

:- pred process_goal_cases(bool::in, list(case)::in, list(case)::out,
		module_info::in, module_info::out) is det.

process_goal_cases(_, [], []) --> [].
process_goal_cases(LocalReuseOnly, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	process_goal(LocalReuseOnly, Goal0, Goal),
	{ Case = case(ConsId, Goal) },
	process_goal_cases(LocalReuseOnly, Case0s, Cases).

:- pred process_goal_list(bool::in, hlds_goals::in, hlds_goals::out,
		module_info::in, module_info::out) is det.

process_goal_list(_, [], []) --> [].
process_goal_list(LocalReuseOnly, [Goal0 | Goal0s], [Goal | Goals]) -->
	process_goal(LocalReuseOnly, Goal0, Goal),
	process_goal_list(LocalReuseOnly, Goal0s, Goals).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
