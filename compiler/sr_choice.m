%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
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

:- module structure_reuse__sr_choice.
:- interface.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_pred.
:- import_module hlds__hlds_module.
:- import_module structure_reuse__sr_data.
:- import_module structure_reuse__sr_choice_util.

:- import_module list, std_util.

:- pred sr_choice__process_goal(strategy::in, vartypes::in, module_info::in,
	proc_info::in, hlds_goal::in, hlds_goal::out,
	maybe(list(reuse_condition))::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module check_hlds__type_util.
:- import_module hlds__hlds_data.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__prog_data.

:- import_module assoc_list, bool, int. 
:- import_module map, multi_map, require, set.
:- import_module string. 
:- import_module queue.

process_goal(Strategy, VarTypes, ModuleInfo, ProcInfo, 
		Goal0, Goal, MaybeReuseConditions) :-
	Strategy = strategy(Constraint, SelectionRule),
	apply_constraint(Constraint, VarTypes, ModuleInfo, ProcInfo, 
			Goal0, Goal1),
	select_reuses(SelectionRule, Goal1, Goal2, ReusedVars, ReuseConditions),
	determine_cgc(ReusedVars, Goal2, Goal),
	( ReuseConditions = [] ->
		MaybeReuseConditions = no
	;
		MaybeReuseConditions = yes(ReuseConditions)
	).
	
%-----------------------------------------------------------------------------%

:- type constraint_info
	--->	constraint_info(
			map		:: multi_map(prog_var,
							reuse_cell_data),
			module_info	:: module_info,
			proc_info	:: proc_info, 
			vartypes	:: vartypes
		).

:- type reuse_cell_data
	--->	data(
			cons_id		:: cons_id,
			vars		:: prog_vars,
			secondary_tag	:: bool
		).

:- pred constraint_info_init(vartypes::in, module_info::in,
		proc_info::in, constraint_info::out) is det.

constraint_info_init(VarTypes, ModuleInfo, ProcInfo, 
		constraint_info(Map, ModuleInfo, ProcInfo, VarTypes)) :-
	multi_map__init(Map).

:- pred apply_constraint(constraint::in, vartypes::in, module_info::in,
		proc_info::in, hlds_goal::in, hlds_goal::out) is det.

apply_constraint(Constraint, VarTypes, ModuleInfo, ProcInfo, Goal0, Goal) :-
	constraint_info_init(VarTypes, ModuleInfo, ProcInfo, ConstraintInfo),
	apply_constraint_2(Constraint, Goal0, Goal, ConstraintInfo, _).

:- pred apply_constraint_2(constraint::in, hlds_goal::in, hlds_goal::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_2(_Constraint, Goal - GoalInfo, Goal - GoalInfo) -->
	{ Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name) }.

apply_constraint_2(Constraint, Goal - GoalInfo0, Goal - GoalInfo) -->
	{ Goal = unify(_Var, _Rhs, _Mode, Unification, _Ctxt) },
	apply_constraint_unification(Constraint, Unification,
			GoalInfo0, GoalInfo).

apply_constraint_2(_Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
apply_constraint_2(_Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = foreign_proc(_, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
apply_constraint_2(_Constraint, Goal0 - _GoalInfo, _) -->
	{ Goal0 = shorthand(_) },
	{ error("structure_reuse: shorthand.\n") }.

apply_constraint_2(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0) },
	=(BeforeIfInfo),
	apply_constraint_2(Constraint, If0, If),
	=(IfInfo),
	{ apply_constraint_2(Constraint, Then0, Then, IfInfo, ThenInfo) },
	{ apply_constraint_2(Constraint, Else0, Else, BeforeIfInfo, ElseInfo) },
	merge(ThenInfo),
	merge(ElseInfo),
	{ Goal = if_then_else(Vars, If, Then, Else) }.

apply_constraint_2(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0) },
	=(InitSwitchInfo),
	apply_constraint_cases(Constraint, InitSwitchInfo, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases) }.

apply_constraint_2(Constraint, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	apply_constraint_2(Constraint, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

apply_constraint_2(Constraint, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	=(InitNotInfo),
	% A negated goal cannot introduce new dead cells to the map of
	% available dead cells, as those dead cells are not allowed to 
	% be reused outside of the negated goal. 
	{ apply_constraint_2(Constraint, Goal0, Goal, InitNotInfo, _) }.

apply_constraint_2(Constraint, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	apply_constraint_list(Constraint, Goal0s, Goals).

apply_constraint_2(Constraint, disj(Goal0s) - GoalInfo,
		disj(Goals) - GoalInfo) -->
	=(InitDisjInfo),
	apply_constraint_disj(Constraint, InitDisjInfo, Goal0s, Goals).

apply_constraint_2(Constraint, par_conj(Goal0s) - GoalInfo,
		par_conj(Goals) - GoalInfo) -->
	apply_constraint_list(Constraint, Goal0s, Goals).

:- pred apply_constraint_cases(constraint::in, constraint_info::in,
		list(case)::in, list(case)::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_cases(_Constraint, _Info0, [], []) --> [].
apply_constraint_cases(Constraint, Info0, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	{ apply_constraint_2(Constraint, Goal0, Goal, Info0, Info) },
	merge(Info),
	{ Case = case(ConsId, Goal) },
	apply_constraint_cases(Constraint, Info0, Case0s, Cases).

:- pred apply_constraint_list(constraint::in, hlds_goals::in, hlds_goals::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_list(_Constraint, [], []) --> [].
apply_constraint_list(Constraint, [Goal0 | Goal0s], [Goal | Goals]) -->
	apply_constraint_2(Constraint, Goal0, Goal),
	apply_constraint_list(Constraint, Goal0s, Goals).

:- pred apply_constraint_disj(constraint::in,
		constraint_info::in, hlds_goals::in, hlds_goals::out,
		constraint_info::in, constraint_info::out) is det.

apply_constraint_disj(_Constraint, _Info0, [], []) --> [].
apply_constraint_disj(Constraint, Info0, [Goal0 | Goal0s], [Goal | Goals]) -->
	{ apply_constraint_2(Constraint, Goal0, Goal, Info0, Info) },
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
	{ Unif = construct(Var, ConsId, Vars, _Ms, _HTC, _IsUniq, _Aditi) },
	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(construct(Pairs)) ->
		PossibleCandidates = set__to_sorted_list(Pairs)
	;
		error("sr_choice__apply_constraint_unification")
	},
	ModuleInfo =^ module_info, 
	VarTypes =^ vartypes, 
	{ has_secondary_tag(ModuleInfo, VarTypes, Var, 
			ConsId, HasSecondaryTag) },
	Map =^ map,
	(
		{ Constraint = same_cons_id },

			% XXX recode this more efficiently at some stage.
		{ P = (pred(Candidate::out) is nondet :- 
			list__member(Candidate0, PossibleCandidates),
			CandidateVar = Candidate0 ^ var,
			multi_map__search(Map, CandidateVar, CandidateData),
			ConsIds = list__map((func(D) = D ^ cons_id),
					CandidateData),
			list__remove_dups(ConsIds, [ConsId]),
			ReuseFields = reuse_fields(HasSecondaryTag, Vars,
					CandidateData),
			Candidate = (Candidate0
					^ cons_ids := yes([ConsId]))
					^ reuse_fields := yes(ReuseFields)
		)}
	;
		{ Constraint = within_n_cells_difference(Difference) },
			% XXX recode this more efficiently at some stage.
		{ P = (pred(Candidate::out) is nondet :- 
			list__member(Candidate0, PossibleCandidates),
			CandidateVar = Candidate0 ^ var,
			
			\+ no_tag_type(ModuleInfo, VarTypes, CandidateVar),

			multi_map__search(Map, CandidateVar, CandidateData),
			ConsIds = list__remove_dups(
					list__map((func(D) = D ^ cons_id),
						CandidateData)),
			% XXX There is something wrong going on here. Removing
			% the list__remove_dups causes stack overflow in some
			% cases. Later some further investigation wouldn't be a
			% bad investment. 
			ReuseSizes = list__remove_dups(list__map(
					(func(Data) = list__length(Data^vars)), 
					CandidateData)),
			
			Size = list__length(Vars),
			all [ReuseSize] (
				list__member(ReuseSize, ReuseSizes)
			=>
				(
					ReuseSize - Size =< Difference
				)
			),
			ReuseFields = reuse_fields(HasSecondaryTag, Vars,
					CandidateData),
			Candidate = (Candidate0
					^ cons_ids := yes(ConsIds))
					^ reuse_fields := yes(ReuseFields)

		)}
	),
	{ solutions(P, Candidates) },
	{ goal_info_set_reuse(
			choice(construct(set__list_to_set(Candidates))),
			GoalInfo0,
			GoalInfo) }.


apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = deconstruct(Var, ConsId, Vars, _Modes, _CanFail, _CanCGC) },
	Map0 =^ map,
	ModuleInfo =^ module_info, 
	VarTypes =^ vartypes, 
	{ has_secondary_tag(ModuleInfo, VarTypes, Var, ConsId, SecondaryTag) },
	{ NewData = data(ConsId, Vars, SecondaryTag) },
	{ 
		(
			multi_map__search(Map0, Var, ListData),
			cons_id_in_reuse_cell_data(ConsId, ListData)
		)
	->
		Map = Map0
	;
		multi_map__set(Map0, Var, NewData, Map) 
	},
	^ map := Map.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = assign(_, _) }.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = simple_test(_, _) }.
apply_constraint_unification(_Constraint, Unif, GoalInfo, GoalInfo) -->
	{ Unif = complicated_unify(_, _, _) }.

:- pred cons_id_in_reuse_cell_data(cons_id, list(reuse_cell_data)). 
:- mode cons_id_in_reuse_cell_data(in, in) is semidet.
cons_id_in_reuse_cell_data(ConsId, Data):- 
	list__filter(
		(pred(ReuseData::in) is semidet :- 
			ReuseData = data(ConsId, _, _)), 
		Data, [_|_]).

	%
	% Determine which of the fields already contain references to
	% the correct variable, and hence don't need to be updated.  To
	% do this requires knowledge of whether or not the current field
	% has a secondary tag or not.
	%
:- func reuse_fields(bool, prog_vars, list(reuse_cell_data)) = list(bool).

reuse_fields(HasSecTag, Vars, CandidateData)
	= list__foldl(and_list, Tail, Head) :-
		Pairs = list__map((func(Data) = 
					Data ^ secondary_tag - Data ^ vars),
				CandidateData),
		BoolsList = list__map(
				already_correct_fields(HasSecTag, Vars), Pairs),
		( BoolsList = [H | T] ->
			Head = H,
			Tail = T
		;
			error("reuse_fields: empty list")
		).


:- func and_list(list(bool), list(bool)) = list(bool).

and_list(ListA, ListB)
	= list__map((func(A - B) = A `and` B),
			from_corresponding_lists(ListA, ListB)).

%-----------------------------------------------------------------------------%


:- type selection_info
	--->	selection_info(
			local_used	:: set(prog_var),
			global_used	:: set(prog_var),
			reuse_conds	:: list(reuse_condition),
		
			lifo		:: lifo
		).

:- type lifo
	--->	lifo(
			all_locals	:: list(list(prog_var)),
			local		:: list(prog_var),
			global		:: list(list(prog_var))
		).

:- func selection_info_init = selection_info.

selection_info_init = selection_info(set__init, set__init, [], lifo([],[],[])).

:- pred select_reuses(selection::in, hlds_goal::in, hlds_goal::out,
		set(prog_var)::out, list(reuse_condition)::out) is det.

select_reuses(SelectionRule, Goal0, Goal, ReusedVars, ReuseConditions) :-
	select_reuses_2(SelectionRule, Goal0, Goal, selection_info_init, Info),
	ReusedVars = Info ^ local_used `union` Info ^ global_used,
	ReuseConditions = Info ^ reuse_conds.

:- pred select_reuses_2(selection::in, hlds_goal::in, hlds_goal::out,
		selection_info::in, selection_info::out) is det.

select_reuses_2(_Selection, Goal - GoalInfo, Goal - GoalInfo) -->
	{ Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name) }.

select_reuses_2(Selection, Goal - GoalInfo0, Goal - GoalInfo) -->
	{ Goal = unify(_Var, _Rhs, _Mode, Unification, _Ctxt) },
	select_reuses_unification(Selection, Unification, GoalInfo0, GoalInfo).

select_reuses_2(_Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = generic_call(_, _, _, _) },
	{ Goal = Goal0 }.
select_reuses_2(_Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = foreign_proc(_, _, _, _, _, _, _) },
	{ Goal = Goal0 }.
select_reuses_2(_Selection, Goal0 - _GoalInfo, _) -->
	{ Goal0 = shorthand(_) },
	{ error("structure_reuse: shorthand.\n") }.

select_reuses_2(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = if_then_else(Vars, If0, Then0, Else0) },
	selection_start_branch,
	=(BeforeIfInfo),
	{ select_reuses_2(Selection, If0, If, BeforeIfInfo, IfInfo) },
	{ select_reuses_2(Selection, Then0, Then, IfInfo, ThenInfo) },
	selection_merge(ThenInfo),
	{ select_reuses_2(Selection, Else0, Else, BeforeIfInfo, ElseInfo) },
	selection_merge(ElseInfo),
	selection_end_branch,
	{ Goal = if_then_else(Vars, If, Then, Else) }.

select_reuses_2(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = switch(Var, CanFail, Cases0) },
	selection_start_branch,
	=(InitSwitchInfo),
	select_reuses_cases(Selection, InitSwitchInfo, Cases0, Cases),
	{ Goal = switch(Var, CanFail, Cases) }.

select_reuses_2(Selection, Goal0 - GoalInfo, Goal - GoalInfo) -->
	{ Goal0 = some(Vars, CanRemove, SomeGoal0) },
	select_reuses_2(Selection, SomeGoal0, SomeGoal),
	{ Goal = some(Vars, CanRemove, SomeGoal) }.

select_reuses_2(Selection, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) -->
	select_reuses_2(Selection, Goal0, Goal).

select_reuses_2(Selection, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) -->
	select_reuses_list(Selection, Goal0s, Goals).

select_reuses_2(Selection, disj(Goal0s) - GoalInfo,
		disj(Goals) - GoalInfo) -->
	selection_start_branch,
	=(InitDisjInfo),
	select_reuses_disj(Selection, InitDisjInfo, Goal0s, Goals).

select_reuses_2(Selection, par_conj(Goal0s) - GoalInfo,
		par_conj(Goals) - GoalInfo) -->
	select_reuses_list(Selection, Goal0s, Goals).

:- pred select_reuses_cases(selection::in, selection_info::in,
		list(case)::in, list(case)::out,
		selection_info::in, selection_info::out) is det.

select_reuses_cases(_Selection, _Info0, [], []) --> selection_end_branch.
select_reuses_cases(Selection, Info0, [Case0 | Case0s], [Case | Cases]) -->
	{ Case0 = case(ConsId, Goal0) },
	{ select_reuses_2(Selection, Goal0, Goal, Info0, Info) },
	selection_merge(Info),
	{ Case = case(ConsId, Goal) },
	select_reuses_cases(Selection, Info0, Case0s, Cases).

:- pred select_reuses_list(selection::in, hlds_goals::in, hlds_goals::out,
		selection_info::in, selection_info::out) is det.

select_reuses_list(_Selection, [], []) --> [].
select_reuses_list(Selection, [Goal0 | Goal0s], [Goal | Goals]) -->
	select_reuses_2(Selection, Goal0, Goal),
	select_reuses_list(Selection, Goal0s, Goals).

:- pred select_reuses_disj(selection::in,
		selection_info::in, hlds_goals::in, hlds_goals::out,
		selection_info::in, selection_info::out) is det.

select_reuses_disj(_Selection, _Info0, [], []) --> selection_end_branch.
select_reuses_disj(Selection, Info0, [Goal0 | Goal0s], [Goal | Goals]) -->
	{ select_reuses_2(Selection, Goal0, Goal, Info0, Info) },
	selection_merge(Info),
	select_reuses_disj(Selection, Info0, Goal0s, Goals).

	%
	% This merges in the select_info left after the end of each
	% branch with the global one.
	%
:- pred selection_merge(selection_info::in, selection_info::in,
		selection_info::out) is det.

selection_merge(selection_info(LocalA, GlobalA, CondsA, LifoA),
		selection_info(LocalB, GlobalB, CondsB, LifoB),
		selection_info(Local, Global, Conds, Lifo)) :-
	Local = LocalA `set__union` LocalB,
	Global = GlobalA `set__union` GlobalB,
	Conds = CondsA ++ CondsB,

	LifoA = lifo(AllLocalsA, LocalsA, GlobalsA),
	LifoB = lifo(AllLocalsB, LocalsB, GlobalsB),
	Lifo  = lifo([LocalsA | AllLocalsB], [], GlobalsB),

	require(unify(LocalsB, []),
			"selection_merge: LocalsB not empty"),
	require(unify(AllLocalsA, []),
			"selection_merge: AllLocalsA not equal"),
	require(unify(GlobalsA, GlobalsB),
			"selection_merge: Globals not equal").
	 

	%
	% At the start of processing all branches of a 
	% disj/switch/if_then_else this predicate should be called.
	%
:- pred selection_start_branch(selection_info::in, selection_info::out) is det.

selection_start_branch(selection_info(Local0, Global0, Conds0, Lifo0),
		selection_info(Local, Global, Conds, Lifo)) :-
	Local = set__init,
	Global = Local0 `set__union` Global0,
	Conds = Conds0,

	Lifo0 = lifo(AllLocals, Locals, Globals),
	Lifo  = lifo(AllLocals, [], [Locals | Globals]).

	%
	% At the end of processing all branches of a
	% disj/switch/if_then_else this predicate should be called.
	%
:- pred selection_end_branch(selection_info::in, selection_info::out) is det.

selection_end_branch(selection_info(Local0, Global0, Conds0, Lifo0),
		selection_info(Local, Global, Conds, Lifo)) :-
	Local = set__init,
	Global = Local0 `set__union` Global0,
	Conds = Conds0,

	Lifo0 = lifo(AllLocals0, Locals0, Globals0),
	( Globals0 = [G | Gs] ->
		Locals = list_merge([Locals0 | AllLocals0]) ++ G,
		Globals = Gs
	;
		Locals = list_merge([Locals0 | AllLocals0]),
		Globals = []
	),
	Lifo  = lifo([], Locals, Globals).

	% [ [1a,2a], [2b,1b], [2c,3c,1c] ] -> [1a, 2b, 2c, 2a, 1b, 3c, 1c]
:- func list_merge(list(list(T))) = list(T).

list_merge(List) = Result :-
	list_merge(List, Tail, Head),
	(  Tail = [] ->
		Result = list__reverse(Head)
	;
		Result = Head ++ list_merge(Tail)
	).


:- pred list_merge(list(list(T))::in, list(list(T))::out, list(T)::out) is det.

list_merge([], [], []).
list_merge([H | T], Tail, Head) :-
	(
		H = [],
		list_merge(T, Tail, Head)
	;
		H = [X | Xs],
		list_merge(T, Tail0, Head0),
		Tail = [Xs | Tail0],
		Head = [X | Head0]
	).

:- pred select_reuses_unification(selection::in, unification::in,
		hlds_goal_info::in, hlds_goal_info::out,
		selection_info::in, selection_info::out) is det.

select_reuses_unification(Selection, Unif, GoalInfo0, GoalInfo) -->
	{ Unif = construct(_Var, _ConsId, _Vars, _Ms, _HTC, _IsUniq, _Aditi) },
	{ goal_info_get_reuse(GoalInfo0, ReuseInfo) },
	{ ReuseInfo = choice(construct(Pairs)) ->
		PossibleCandidates = set__to_sorted_list(Pairs)
	;
		error("sr_choice__apply_selection_unification")
	},

	LocalReused0 =^ local_used,
	GlobalReused =^ global_used,

	(
		{ Selection = lifo },
		Locals =^ lifo ^ local,
		Globals =^ lifo ^ global,
		{ F = (pred(Var::in, LocalReuseVar::out) is semidet :-
				list__filter((pred(RV::in) is semidet :-
						Var = RV ^ var
					), PossibleCandidates,
					[LocalReuseVar]),
				\+ set__member(Var, LocalReused0),
				\+ set__member(Var, GlobalReused)
			)},
		{ list__filter_map(F,
				Locals ++ list__condense(Globals), Candidates) }
	;
		{ Selection = random },
		% XXX If you ask me, I don't see much randomness around here. 
		{ P = (pred(Choice::out) is nondet :- 
			list__member(Choice, PossibleCandidates),
			ChoiceVar = Choice ^ var,
			\+ set__member(ChoiceVar, LocalReused0),
			\+ set__member(ChoiceVar, GlobalReused)
		)},

		{ solutions(P, Candidates) }
	;
		{ Selection = graph },
		{ require__error("(sr_choice) select_reuses_unification: selection graph is not an option at this place.") }
	),
	( { Candidates = [Candidate | _] } ->
		{ Candidate = reuse_var(ReuseVar, ReuseCond,
				MaybeConsIds, MaybeReuseFields) },
		{ 
			MaybeConsIds = yes(ConsIds0),
			MaybeReuseFields = yes(ReuseFields0)
		->
			ConsIds = ConsIds0,
			ReuseFields = ReuseFields0
		;
			error("select_reuses_unification: no cons_ids.")
		},
		{ set__insert(LocalReused0, ReuseVar, LocalReused) },
		{
			ReuseCond = always,
			ConditionalReuse = no
		;
			ReuseCond = condition(_, _, _),
			ConditionalReuse = yes
		},
		{ goal_info_set_reuse(
				potential_reuse(cell_reused(ReuseVar, 
						ConditionalReuse,
						ConsIds, ReuseFields)),
				GoalInfo0,
				GoalInfo) },
		ReuseConditions =^ reuse_conds,
		^ reuse_conds := [ReuseCond | ReuseConditions]
	;
		{ LocalReused = LocalReused0 },
		{ goal_info_set_reuse(
				potential_reuse(no_reuse),
				GoalInfo0,
				GoalInfo) }
	),
	^ local_used := LocalReused.

select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = deconstruct(Var, _ConsId, _Vars, _Modes, _CanFail, _CanCGC) },
	Locals0 =^ lifo ^ local,
	^ lifo ^ local := [Var | Locals0].

select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = assign(_, _) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = simple_test(_, _) }.
select_reuses_unification(_Selection, Unif, GoalInfo, GoalInfo) -->
	{ Unif = complicated_unify(_, _, _) }.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred determine_cgc(set(prog_var)::in, hlds_goal::in, hlds_goal::out) is det.

determine_cgc(_ReusedVars, Goal - GoalInfo, Goal - GoalInfo) :- 
	Goal = call(_PredId, _ProcId, _Args, _Builtin, _MaybeCtxt, _Name).

determine_cgc(ReusedVars, Goal0 - GoalInfo0, Goal - GoalInfo) :-
	Goal0 = unify(Var, Rhs, Mode, Unif0, Ctxt),
	determine_cgc_unification(ReusedVars, Unif0, Unif, GoalInfo0, GoalInfo),
	Goal = unify(Var, Rhs, Mode, Unif, Ctxt).

determine_cgc(_ReusedVars, Goal0 - GoalInfo, Goal - GoalInfo) :- 
	Goal0 = generic_call(_, _, _, _),
	Goal = Goal0.
determine_cgc(_ReusedVars, Goal0 - GoalInfo, Goal - GoalInfo) :- 
	Goal0 = foreign_proc(_, _, _, _, _, _, _),
	Goal = Goal0.
determine_cgc(_ReusedVars, Goal0 - _GoalInfo, _) :- 
	Goal0 = shorthand(_),
	error("structure_reuse: shorthand.\n").

determine_cgc(ReusedVars, Goal0 - GoalInfo, Goal - GoalInfo) :- 
	Goal0 = if_then_else(Vars, If0, Then0, Else0),
	determine_cgc(ReusedVars, If0, If),
	determine_cgc(ReusedVars, Then0, Then),
	determine_cgc(ReusedVars, Else0, Else),
	Goal = if_then_else(Vars, If, Then, Else).

determine_cgc(ReusedVars, Goal0 - GoalInfo, Goal - GoalInfo) :-
	Goal0 = switch(Var, CanFail, Cases0),
	determine_cgc_cases(ReusedVars, Cases0, Cases),
	Goal = switch(Var, CanFail, Cases).

determine_cgc(ReusedVars, Goal0 - GoalInfo, Goal - GoalInfo) :- 
	Goal0 = some(Vars, CanRemove, SomeGoal0),
	determine_cgc(ReusedVars, SomeGoal0, SomeGoal),
	Goal = some(Vars, CanRemove, SomeGoal).

determine_cgc(ReusedVars, not(Goal0) - GoalInfo, not(Goal) - GoalInfo) :- 
	determine_cgc(ReusedVars, Goal0, Goal).

determine_cgc(ReusedVars, conj(Goal0s) - GoalInfo,
		conj(Goals) - GoalInfo) :- 
	determine_cgc_list(ReusedVars, Goal0s, Goals).

determine_cgc(ReusedVars, disj(Goal0s) - GoalInfo,
		disj(Goals) - GoalInfo) :- 
	determine_cgc_list(ReusedVars, Goal0s, Goals).

determine_cgc(ReusedVars, par_conj(Goal0s) - GoalInfo,
		par_conj(Goals) - GoalInfo) :- 
	determine_cgc_list(ReusedVars, Goal0s, Goals).

:- pred determine_cgc_cases(set(prog_var)::in, list(case)::in, 
		list(case)::out) is det.

determine_cgc_cases(_ReusedVars, [], []).
determine_cgc_cases(ReusedVars, [Case0 | Case0s], [Case | Cases]) :- 
	Case0 = case(ConsId, Goal0),
	determine_cgc(ReusedVars, Goal0, Goal),
	Case = case(ConsId, Goal),
	determine_cgc_cases(ReusedVars, Case0s, Cases).

:- pred determine_cgc_list(set(prog_var)::in, hlds_goals::in, 
		hlds_goals::out) is det.

determine_cgc_list(_ReusedVars, [], []).
determine_cgc_list(ReusedVars, [Goal0 | Goal0s], [Goal | Goals]) :-
	determine_cgc(ReusedVars, Goal0, Goal),
	determine_cgc_list(ReusedVars, Goal0s, Goals).

:- pred determine_cgc_unification(set(prog_var)::in,
		unification::in, unification::out,
		hlds_goal_info::in, hlds_goal_info::out) is det.

determine_cgc_unification(_ReusedVars, Unif, Unif, GoalInfo, GoalInfo) :- 
	Unif = construct(_Var, _ConsId, _Vars, _Ms, _HTC, _IsUniq, _Aditi).

determine_cgc_unification(ReusedVars, Unif0, Unif, GoalInfo0, GoalInfo) :- 
	Unif0 = deconstruct(Var, ConsId, Vars, Modes, CanFail, _CanCGC),

	goal_info_get_reuse(GoalInfo0, ReuseInfo),
	( ReuseInfo = choice(deconstruct(MaybeDies)) ->
		(
			MaybeDies = yes(Condition),
			goal_info_set_reuse(
					potential_reuse(cell_died),
					GoalInfo0, 
					GoalInfo),
			( set__member(Var, ReusedVars) ->
				CanCGC = no
			;
				% XXX Currently we only compile time gc
				% cells which don't introduce a reuse
				% condition on the predicate.
				(
					Condition = always,
					CanCGC = yes
				;
					Condition = condition(_, _, _),
					CanCGC = no
				)
			)

		;
			MaybeDies = no,
			CanCGC = no,
			goal_info_set_reuse(
					potential_reuse(no_reuse),
					GoalInfo0, 
					GoalInfo)
		)
	;
		error("determine_cgc_unification")
	),
	Unif = deconstruct(Var, ConsId, Vars, Modes, CanFail, CanCGC).


determine_cgc_unification(_ReusedVars, Unif, Unif, GoalInfo, GoalInfo) :- 
	Unif = assign(_, _).
determine_cgc_unification(_ReusedVars, Unif, Unif, GoalInfo, GoalInfo) :- 
	Unif = simple_test(_, _).
determine_cgc_unification(_ReusedVars, Unif, Unif, GoalInfo, GoalInfo) :- 
	Unif = complicated_unify(_, _, _).


%-----------------------------------------------------------------------------%

