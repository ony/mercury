%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_choice
% Main authors: petdr
% 
% Given a goal annotated with information about which cells are
% canditates for reuse and a strategy determine which cells will
% actually be reused and the conditions that reuse implies on the head
% variables.
%
%-----------------------------------------------------------------------------%

:- module sr_choice.
:- interface.

:- import_module hlds_goal, sr_data.
:- import_module list, std_util.

:- type strategy
	--->	strategy(
			constraint,
			selection
		).

	% The constraint on the cells that we consider available for
	% reuse.
:- type constraint
	--->	same_cons_id
	.

	% After the constraint has been applied to the set of cells
	% which are available for reuse, determine which of that set we
	% select.
:- type selection
	--->	lifo
	;	random
	.

:- pred sr_choice__apply_constraint_goal(strategy::in, hlds_goal::in, hlds_goal::out,
		maybe(list(reuse_condition))::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds_data, prog_data.
:- import_module multi_map, require, set.

apply_constraint_goal(Strategy, Goal0, Goal, MaybeReuseConditions) :-
	Strategy = strategy(Constraint, SelectionRule),
	apply_constraint(Constraint, Goal0, Goal1),
	select_reuses(SelectionRule, Goal1, Goal, ReuseConditions),
	( ReuseConditions = [] ->
		MaybeReuseConditions = no
	;
		MaybeReuseConditions = yes(ReuseConditions)
	).
	
%-----------------------------------------------------------------------------%

:- type constraint_info
	--->	constraint_info(
			map	:: multi_map(prog_var, cons_id)
		).

:- pred constraint_info_init(constraint_info::out) is det.

constraint_info_init(constraint_info(Map)) :-
	multi_map__init(Map).

:- pred apply_constraint(constraint::in, hlds_goal::in, hlds_goal::out) is det.

apply_constraint(Constraint, Goal0, Goal) :-
	constraint_info_init(ConstraintInfo),
	apply_constraint(Constraint, Goal0, Goal, ConstraintInfo, _).

:- pred apply_constraint(constraint::in, hlds_goal::in, hlds_goal::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint(_Constraint, Goal - GoalInfo, Goal - GoalInfo) -->
	{ Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name) }.

apply_constraint(Constraint, Goal - GoalInfo0, Goal - GoalInfo) -->
	{ Goal = unify(_Var, _Rhs, _Mode, Unification, _Ctxt) },
	apply_constraint_unification(Constraint, Unification, GoalInfo0, GoalInfo).

apply_constraint(_Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
apply_constraint(_Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = pragma_foreign_code(_, _, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
apply_constraint(_Constraint, Goal0 - _GoalInfo, _) -->
	{ Goal0 = bi_implication(_, _) },
	{ error("structure_reuse: bi_implication.\n") }.

apply_constraint(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0, SM) },
	apply_constraint(Constraint, If0, If),
	=(IfInfo),
	{ apply_constraint(Constraint, Then0, Then, IfInfo, ThenInfo) },
	{ apply_constraint(Constraint, Else0, Else, IfInfo, ElseInfo) },
	merge(ThenInfo),
	merge(ElseInfo),
	{ Goal = if_then_else(Vars, If, Then, Else, SM) }.

apply_constraint(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0, StoreMap) },
	=(InitSwitchInfo),
	apply_constraint_cases(Constraint, InitSwitchInfo, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases, StoreMap) }.

apply_constraint(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	apply_constraint(Constraint, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

apply_constraint(Constraint, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	apply_constraint(Constraint, Goal0, Goal).

apply_constraint(Constraint, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	apply_constraint_list(Constraint, Goal0s, Goals).

apply_constraint(Constraint, disj(Goal0s, SM) - GoalInfo,
		disj(Goals, SM) - GoalInfo) -->
	=(InitDisjInfo),
	apply_constraint_disj(Constraint, InitDisjInfo, Goal0s, Goals).

apply_constraint(Constraint, par_conj(Goal0s, SM) - GoalInfo,
		par_conj(Goals, SM) - GoalInfo) -->
	apply_constraint_list(Constraint, Goal0s, Goals).

:- pred apply_constraint_cases(constraint::in, constraint_info::in,
		list(case)::in, list(case)::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_cases(_Constraint, _Info0, [], []) --> [].
apply_constraint_cases(Constraint, Info0, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	{ apply_constraint(Constraint, Goal0, Goal, Info0, Info) },
	merge(Info),
	{ Case = case(ConsId, Goal) },
	apply_constraint_cases(Constraint, Info0, Case0s, Cases).

:- pred apply_constraint_list(constraint::in, hlds_goals::in, hlds_goals::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_list(_Constraint, [], []) --> [].
apply_constraint_list(Constraint, [Goal0 | Goal0s], [Goal | Goals]) -->
	apply_constraint(Constraint, Goal0, Goal),
	apply_constraint_list(Constraint, Goal0s, Goals).

:- pred apply_constraint_disj(constraint::in,
		constraint_info::in, hlds_goals::in, hlds_goals::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_disj(_Constraint, _Info0, [], []) --> [].
apply_constraint_disj(Constraint, Info0, [Goal0 | Goal0s], [Goal | Goals]) -->
	{ apply_constraint(Constraint, Goal0, Goal, Info0, Info) },
	merge(Info),
	apply_constraint_disj(Constraint, Info0, Goal0s, Goals).

:- pred merge(constraint_info::in, constraint_info::in,
		constraint_info::out) is det.

merge(InfoA, Info0, Info) :-
	multi_map__merge(InfoA ^ map, Info0 ^ map, Map),
	Info = Info0 ^ map := Map.

:- pred apply_constraint_unification(constraint::in, unification::in,
		hlds_goal_info::in, hlds_goal_info::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_unification(Constraint, Unif, GoalInfo0, GoalInfo) -->
	{ Unif = construct(_Var, ConsId, _Vars, _Ms, _HTC, _IsUniq, _Aditi) },
	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(construct(Pairs)) ->
		PossibleCanditates = set__to_sorted_list(Pairs)
	;
		error("sr_choice__apply_constraint_unification")
	},
	(
		{ Constraint = same_cons_id },
		Map =^ map,

			% XXX recode this more efficiently at some stage.
		{ P = (pred(Canditate::out) is nondet :- 
			list__member(Canditate, PossibleCanditates),
			CanditateVar = fst(Canditate),
			multi_map__search(Map, CanditateVar, [ConsId])
		)},
		{ solutions(P, Canditates) }
	),
	{ goal_info_set_reuse(GoalInfo0,
			choice(construct(set__list_to_set(Canditates))),
			GoalInfo) }.

apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = deconstruct(Var, ConsId, _Vars, _Modes, _CanFail, _CanCGC) },
	Map0 =^ map,
	{ multi_map__set(Map0, Var, ConsId, Map) },
	^ map := Map.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = assign(_, _) }.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = simple_test(_, _) }.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = complicated_unify(_, _, _) }.


%-----------------------------------------------------------------------------%

:- import_module queue.

:- type selection_info
	--->	selection_info(
			local_used	:: set(prog_var),
			global_used	:: set(prog_var),
			reuse_conds	:: list(reuse_condition)
		).

:- pred select_reuses(selection::in, hlds_goal::in, hlds_goal::out,
		list(reuse_condition)::out) is det.

select_reuses(_SelectionRule, Goal0, Goal, ReuseConditions) :-
	Goal = Goal0,
	ReuseConditions = [].

:- pred select_reuses(selection::in, hlds_goal::in, hlds_goal::out,
		selection_info::in, selection_info::out) is det.

select_reuses(_Selection, Goal - GoalInfo, Goal - GoalInfo) -->
	{ Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name) }.

select_reuses(Selection, Goal - GoalInfo0, Goal - GoalInfo) -->
	{ Goal = unify(_Var, _Rhs, _Mode, Unification, _Ctxt) },
	select_reuses_unification(Selection, Unification, GoalInfo0, GoalInfo).

select_reuses(_Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
select_reuses(_Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = pragma_foreign_code(_, _, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
select_reuses(_Selection, Goal0 - _GoalInfo, _) -->
	{ Goal0 = bi_implication(_, _) },
	{ error("structure_reuse: bi_implication.\n") }.

select_reuses(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0, SM) },
	select_reuses(Selection, If0, If),
	=(IfInfo),
	{ select_reuses(Selection, Then0, Then, IfInfo, ThenInfo) },
	{ select_reuses(Selection, Else0, Else, IfInfo, ElseInfo) },
	selection_merge(ThenInfo),
	selection_merge(ElseInfo),
	{ Goal = if_then_else(Vars, If, Then, Else, SM) }.

select_reuses(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0, StoreMap) },
	=(InitSwitchInfo),
	select_reuses_cases(Selection, InitSwitchInfo, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases, StoreMap) }.

select_reuses(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	select_reuses(Selection, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

select_reuses(Selection, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	select_reuses(Selection, Goal0, Goal).

select_reuses(Selection, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	select_reuses_list(Selection, Goal0s, Goals).

select_reuses(Selection, disj(Goal0s, SM) - GoalInfo,
		disj(Goals, SM) - GoalInfo) -->
	=(InitDisjInfo),
	select_reuses_disj(Selection, InitDisjInfo, Goal0s, Goals).

select_reuses(Selection, par_conj(Goal0s, SM) - GoalInfo,
		par_conj(Goals, SM) - GoalInfo) -->
	select_reuses_list(Selection, Goal0s, Goals).

:- pred select_reuses_cases(selection::in, selection_info::in,
		list(case)::in, list(case)::out,
		selection_info::in, selection_info::out) is det.

select_reuses_cases(_Selection, _Info0, [], []) --> [].
select_reuses_cases(Selection, Info0, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	{ select_reuses(Selection, Goal0, Goal, Info0, Info) },
	selection_merge(Info),
	{ Case = case(ConsId, Goal) },
	select_reuses_cases(Selection, Info0, Case0s, Cases).

:- pred select_reuses_list(selection::in, hlds_goals::in, hlds_goals::out,
		selection_info::in, selection_info::out) is det.

select_reuses_list(_Selection, [], []) --> [].
select_reuses_list(Selection, [Goal0 | Goal0s], [Goal | Goals]) -->
	select_reuses(Selection, Goal0, Goal),
	select_reuses_list(Selection, Goal0s, Goals).

:- pred select_reuses_disj(selection::in,
		selection_info::in, hlds_goals::in, hlds_goals::out,
		selection_info::in, selection_info::out) is det.

select_reuses_disj(_Selection, _Info0, [], []) --> [].
select_reuses_disj(Selection, Info0, [Goal0 | Goal0s], [Goal | Goals]) -->
	{ select_reuses(Selection, Goal0, Goal, Info0, Info) },
	selection_merge(Info),
	select_reuses_disj(Selection, Info0, Goal0s, Goals).

:- pred selection_merge(selection_info::in, selection_info::in,
		selection_info::out) is det.

selection_merge(selection_info(LocalA, GlobalA, CondsA),
		selection_info(LocalB, GlobalB, CondsB),
		selection_info(Local, Global, Conds)) :-
	Local = set__init,
	Global = LocalA `set__union` LocalB `set__union`
			GlobalA `set__union` GlobalB,
	Conds = CondsA ++ CondsB.

:- pred select_reuses_unification(selection::in, unification::in,
		hlds_goal_info::in, hlds_goal_info::out,
		selection_info::in, selection_info::out) is det.

select_reuses_unification(Selection, Unif, GoalInfo0, GoalInfo) -->
	{ Unif = construct(_Var, _ConsId, _Vars, _Ms, _HTC, _IsUniq, _Aditi) },
	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(construct(Pairs)) ->
		PossibleCanditates = set__to_sorted_list(Pairs)
	;
		error("sr_choice__apply_selection_unification")
	},
	(
		{ Selection = lifo },
		{ error("select_reuses_unification: lifo NYI.") }
	;
		{ Selection = random },
		LocalReused0 =^ local_used,
		GlobalReused =^ global_used,

		{ P = (pred(Choice::out) is nondet :- 
			list__member(Choice, PossibleCanditates),
			ChoiceVar = fst(Choice),
			\+ set__member(ChoiceVar, LocalReused0),
			\+ set__member(ChoiceVar, GlobalReused)
		)},

		{ solutions(P, Canditates) },
		( { Canditates = [ReuseVar - ReuseCond | _] } ->
			{ set__insert(LocalReused0, ReuseVar, LocalReused) },
			{ goal_info_set_reuse(GoalInfo0,
					reuse(cell_reused(ReuseVar)),
					GoalInfo) },
			ReuseConditions =^ reuse_conds,
			^ reuse_conds := [ReuseCond | ReuseConditions]
		;
			{ LocalReused = LocalReused0 },
			{ goal_info_set_reuse(GoalInfo0,
					reuse(no_reuse),
					GoalInfo) }
		),
		^ local_used := LocalReused
	).
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = deconstruct(_Var, _ConsId, _Vars, _Modes, _CanFail, _CanCGC) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = assign(_, _) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = simple_test(_, _) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = complicated_unify(_, _, _) }.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
