%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_dead
% Main authors: nancy
% 
% Determine the deconstructions at which the deconstructed data structure
% may potentially die. Record these dead data structures with the conditions
% for reusing them (i.e. the conditions in which they die). For each dead
% data structure we also keep track of the constructions which might be
% interested in reusing that structure. 
% It is up to the choice analysis to make a choice between these possible
% candidates for reuse. 
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_dead.
:- interface.

:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module possible_alias__pa_alias_as.
:- import_module structure_reuse__sr_data.

:- pred sr_dead__process_goal(pred_id::in, proc_info::in, module_info::in, 
		alias_as_table::in, dead_cell_table::out) is det. 

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds__hlds_data.
:- import_module hlds__hlds_goal.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_alias_as.
:- import_module possible_alias__pa_datastruct.
:- import_module possible_alias__pa_run.
:- import_module structure_reuse__sr_live.

:- import_module assoc_list, int, require. 
:- import_module set, list, map, std_util.

process_goal(_PredId, ProcInfo, ModuleInfo, AliasTable, DeadCellTable) :- 
	pa_alias_as__init(Alias0), 
	proc_info_goal(ProcInfo, Goal), 
	collect_dead_cells(ProcInfo, ModuleInfo, AliasTable, Goal, 
		Alias0, _Alias,
		dead_cell_table_init, DeadCellTable).
	
%-----------------------------------------------------------------------------%

:- pred collect_dead_cells(proc_info::in, module_info::in, alias_as_table::in,
		hlds_goal::in, 
		alias_as::in, alias_as::out,
		dead_cell_table::in, dead_cell_table::out) is det.

collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - _Info, !Alias, !DC) :-
	Expr = conj(Goals),
	list__foldl2(collect_dead_cells(ProcInfo, HLDS, AliasTable),
		Goals, !Alias, !DC).
	
collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = call(PredId, ProcId, ActualVars, _, _, _),
	proc_info_vartypes(ProcInfo, VarTypes), 
	list__map(map__lookup(VarTypes), ActualVars, ActualTypes), 
	pa_run__extend_with_call_alias(HLDS, ProcInfo, AliasTable, 
		PredId, ProcId, ActualVars, ActualTypes, !Alias).
	
collect_dead_cells(_ProcInfo, _HLDS, _AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = generic_call(_, _, _, _), 
	pa_alias_as__top("generic_call unhandled", !Alias).
	
collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = switch(_A, _B, Cases),
	Goals = list__map((func(C) = G :- C = case(_, G)), Cases),
	annotate_disj(ProcInfo, HLDS, AliasTable, Goals, !Alias, !DC).

:- pred annotate_disj(proc_info::in, module_info::in, alias_as_table::in, 
		hlds_goals::in, alias_as::in, alias_as::out, 
		dead_cell_table::in, dead_cell_table::out) is det.
annotate_disj(ProcInfo, ModuleInfo, AliasTable, Goals, Alias0, Alias, !DC) :-
	list__map_foldl(
		(pred(G::in, A::out, DCin::in, DCout::out) is det :- 
			collect_dead_cells(ProcInfo, ModuleInfo, AliasTable, 
				G, Alias0, A, DCin, DCout)),
		Goals, ListAliases, !DC),
	pa_alias_as__least_upper_bound_list(ModuleInfo, ProcInfo, 
			ListAliases, Alias).
	
collect_dead_cells(ProcInfo, HLDS, _AliasTable, Expr - Info, !Alias, !DC) :-
	Expr = unify(_Var, _Rhs, _Mode, Unification, _Context),
	program_point_init(Info, ProgramPoint), 
	unification_verify_reuse(HLDS, ProcInfo, Info, Unification, 
		ProgramPoint, !.Alias, !DC),
		% XXX candidate for future optimization: if
		% you annotate the deconstruct first, you might avoid
		% creating the aliases altogether, thus reducing the
		% number of aliases you cary along, and eventually
		% having an impact on the analysis-time.
	pa_alias_as__extend_unification(HLDS, ProcInfo, Unification,
			Info, !Alias).
	
collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = disj(Goals),
	annotate_disj(ProcInfo, HLDS, AliasTable, Goals, !Alias, !DC). 

collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = not(NegatedGoal),
	collect_dead_cells(ProcInfo, HLDS, AliasTable, NegatedGoal, !Alias, !DC). 
	
collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = some(_A, _B, SomeGoal),
	collect_dead_cells(ProcInfo, HLDS, AliasTable, 
			SomeGoal, !Alias, !DC). 
	
collect_dead_cells(ProcInfo, HLDS, AliasTable, Expr - Info, !Alias, !DC) :- 
	Expr = if_then_else(_Vars, Cond, Then, Else),
	Alias0 = !.Alias, 
	collect_dead_cells(ProcInfo, HLDS, AliasTable, Cond, !Alias, !DC), 
	collect_dead_cells(ProcInfo, HLDS, AliasTable, Then, !Alias, !DC), 
	collect_dead_cells(ProcInfo, HLDS, AliasTable, Else, Alias0, AliasElse, 
			!DC), 
	pa_alias_as__least_upper_bound_list(HLDS, ProcInfo, Info, 
			[ !.Alias, AliasElse ], !:Alias).
	
collect_dead_cells(ProcInfo, HLDS, _AliasTable, Expr - Info, !Alias, !DC) :- 
	Expr = foreign_proc(Attrs, PredId, ProcId, 
			Vars, MaybeModes, Types, _), 
	extend_foreign_code(HLDS, ProcInfo, Attrs, PredId, ProcId, 
		Vars, MaybeModes, Types, Info, !Alias).
	
collect_dead_cells(_ProcInfo, _HLDS, _AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = par_conj(_),
	pa_alias_as__top("par_conj unhandled", !Alias).
		
collect_dead_cells(_ProcInfo, _HLDS, _AliasTable, Expr - _Info, !Alias, !DC) :- 
	Expr = shorthand(_),
	error("(sr_dead) shorthand unhandled(sr_dead).\n").

:- pred unification_verify_reuse(module_info::in, proc_info::in, 
		hlds_goal_info::in, 
		hlds_goal__unification::in, 
		program_point::in, alias_as::in, 
		dead_cell_table::in, dead_cell_table::out) is det.

unification_verify_reuse(ModuleInfo, ProcInfo, Info, 
		Unification, PP, Alias0, !DC) :- 
	Unification = deconstruct(Var, ConsId, Vars, _, _, _),
	goal_info_get_lfu(Info, LFU), 
	goal_info_get_lbu(Info, LBU),
	(
		(
			% XXX things suchs as pred_const's cannot
			% die. 
			cons_id_maybe_arity(ConsId, no)
		;
			% Cells of arity 0 can not be reused. 
			cons_id_arity(ConsId, 0), 
			% Arity zero should imply that the size of the
			% cell is zero, just to be sure. 
			list__length(Vars) = 0
		; 
			list__length(Vars) = 0
		;
			set__union(LFU, LBU, LU), 
			LU_data = set__map(pa_datastruct__init, LU),
			sr_live__init(Live0),
			pa_alias_as__live(ModuleInfo, ProcInfo, LU_data, 
				Live0, Alias0, Live), 
			sr_live__is_live(Var, Live) 
		;
			pa_alias_as__is_top(Alias0)
		)
	->
		% No dead cell generated
		true 	
	;
		reuse_condition_init(ModuleInfo, ProcInfo, 
			Var, LFU, LBU, Alias0, ReuseCondition),
		dead_cell_table_set(PP, ReuseCondition, !DC)
	).

unification_verify_reuse(_, _, _, Unification, _, _, !DC) :- 
	Unification = construct(_, _, _, _, _, _, _).
unification_verify_reuse(_, _, _, Unification, _, _, !DC) :- 
	Unification = assign(_, _).
unification_verify_reuse(_, _, _, Unification, _, _, !DC) :- 
	Unification = simple_test(_,_). 
unification_verify_reuse(_, _, _, Unification, _, _, !DC) :- 
	Unification = complicated_unify(_, _, _).

