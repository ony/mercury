%-----------------------------------------------------------------------------%
% Copyright (C) 2001-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_choice_graphing
% Main authors: nancy
% 
% Just as in module sr_choice, given a goal annotated with preliminary
% possible reuse information, this pass computes the concrete assignements
% of which constructions can profit of dead cells coming from deconstructions. 
% This module is presented as an alternative to sr_choice. The difference
% lies in the way the assignements are computed: instead of using lifo/random
% the assignment problem is translated into a mapping problem (inspired
% from Debray's paper: "On copy avoidance in single assignment languages", 
% and restricted to reuse of dead cells by at most one new cell).
%
% When assigning constructions to dead deconstructions, a table is first
% computed. For each dead cell, a value is computed which reflects the gain
% a reuse might bring, and the list of constructions involved with reusing it.
% The cell with highest value is selected first, the according constructions
% are annotated, and the table is recomputed. This process is repeated until
% no reusable dead deconstructions are left. 
%
% The value of a dead cell (a specific deconstruction) is computed taking 
% into account the call graph which simplified only takes into account
% construction-unifications, conjunctions, and disjunctions. 
% The source of the graph is the deconstruction, the leaves are
% either constructions, or empty. The branches are either conjunctions
% or disjunctions. 
% The value of the dead cell is then computed as follows: 
% 	- value of a conjunction = maximum of the values of each of the 
%		conjunct branches. 
% 		Intuitively: if a dead deconstruction is followed by
%		two constructions which might reuse the dead cell: pick
%		the one which allows the most potential gain. 
%	- value of a disjunction = average of the value of each of the
%		disjunct branches. 
%		Intuitively: if a dead deconstruction is followed by
% 		a disjunction with 2 disjuncts. If reuse is only possible
% 		in one of the branches, allowing this reuse means that 
% 		a priori reuse will occur in only 50% of the cases. 
%		The value of the disjunct should take this into account. 
%		Without precise notion of which branches are executed
%		more often, taking the simple average of the values is 
%		a good approximation. 
%	- value of a construction = a value that takes into account
%	 	the cost of constructing a new cell and compares it
%		to the cost of updating a dead cell. If the arities
%		between the dead and new cell differ, a penalty cost
%		is added (approximated as the gain one would have had if
%		the unusable words would have been reused too). 
%		Weights are used to estimate all of these costs and are
%		hard-coded. I don't think there is any need in making
%		these an option. 
%
% Once the table is computed, usually the cell with highest value is selected.
% To cut the decision between different dead cells with the same
% value, we select the dead cell which has the least number of
% opportunities to be reused. 
% E.g. 
%	X can be reused by 5 different constructions, 
%		but reaches its highest value for a construction C1
%		(value 10).
%	Y can be reused by only one construction, also C1 (value 10). 
%
% First selecting X (and reusing it with construction C1) would 
% jeopardize the reuse of Y and leaves us with only one cell reused. 
% If, on the contrary, one would select Y first, chances are that
% after recomputing the table, X can still be reused by other
% constructions, hence possibly 2 cells reused. 
% Even if Y would be of smaller value, selecting Y first would still 
% be more interesting. Hence, instead of selecting the cell 
% with highest value, we select the cell with highest
% value/degree ratio, degree being the number of constructions at which
% the cell could potentially be reused. 
%	
% Obtained results: 
% - as the matchings are now decided based on a little more information, the
% obtained results wrt reuse are better, especially when allowing 
% differing arities.
% - yet, sometimes the results might be a little worse than lifo. Both
% strategies might decide different reuse-matchings, hence induce different
% reuse-constraints (e.g. while one strategy decides to reuse the first
% headvariable of a procedure, the other reuses the second headvariable),
% which might make that in one case, the constraints can be satisfied, 
% but the other conditions can not. 
%
% XXX Current shortcoming compared to sr_choice: cells being deconstructed
% in the different branches of a disjunction will not be reused after the
% the disjunction. In sr_choice, this is made possible. 
% e.g.:
%	( 
%		..., X => f(... ), ... 		% X dies
%	; 
%		..., X => g(... ), ... 		% X dies
%	), 
%	Y <= f(... ), ... 			% Y can reuse X
% While sr_choice allows Y to reuse X (which is perfectly legal as
% it dies in each of the branches of the disjunction), this will not
% be discovered at this moment. 
%

%-----------------------------------------------------------------------------%

:- module sr_choice_graphing.
:- interface. 

% library modules. 
:- import_module io, std_util, list. 

% XXX parent modules.
:- import_module hlds.
% compiler_modules.
:- import_module hlds__hlds_goal, hlds__hlds_module, hlds__hlds_pred.
:- import_module sr_data.

:- import_module sr_choice_util.

:- type background_info. 
:- pred set_background_info(sr_choice_util__constraint::in, module_info::in, 
		vartypes::in, background_info::out) is det.

	% Annotate each deconstruction/construction unification with
	% whether they die, can potentially reuse a dead cell or are
	% not possible for reuse. 
:- pred sr_choice_graphing__process_goal(
		background_info::in, 
		hlds_goal::in, hlds_goal::out,
		maybe(list(reuse_condition))::out, 
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
:- implementation. 

% XXX parent modules.
:- import_module parse_tree, check_hlds, libs. 

:- import_module term, map, float, bool, set, require, int. 
:- import_module check_hlds__type_util, libs__globals, libs__options.
:- import_module parse_tree__prog_data.
:- import_module hlds__hlds_data.

%-----------------------------------------------------------------------------%
:- type background_info 
	---> 	background(
			constraint	:: sr_choice_util__constraint,
			module_info	:: module_info, 
			vartypes	:: vartypes
		).

set_background_info(Constraint, ModuleInfo, VarTypes, BG):-
	BG = background(Constraint, ModuleInfo, VarTypes). 

%-----------------------------------------------------------------------------%

	% Type meant to keep a table of the dead cells and their
	% possible reuses. 
:- type values  == map(contextvar, value). 
	
	% Given a construction for which reuse of a dead cell would
	% be possible, record the cons-ids the dead cell which it is 
	% reusing might have, as well as the fields which don't need 
	% explicit update. 
	% XXX the cons-ids will always be at most one cons-id. There can 
	% only be more in the case a cell dies in each of the branches
	% of a disjunction. This is not yet supported. 
:- type context_reuse_var
	---> 	context_reuse_var(
			var		:: contextvar,
			cons_ids	:: maybe(list(cons_id)),
			reuse_fields	:: maybe(list(bool)),
			reuse_type	:: reuse_type
		).

	% Track extra documentation of the reuse. 
:- type reuse_type 
	---> 	no_reuse
	; 	reuse_type(
			same_cons	:: bool, 
			arity_old	:: int, 	% arity of dead cell
			arity_new	:: int		% arity of new cell
				% arity_diff = arity_old - arity_new
		). 

:- type value 
	---> 	entry( 
			conds		:: reuse_condition, 
			weight		:: maybe(float),   % computed value.
			vars		:: list(context_reuse_var),
						% variables involved 
						% with reusing
						% the dead var)
			degree 		:: int
						% keep track of how much
						% constructions could be
						% interested in reusing
						% the dead var. 
		).

	% Each construction/deconstruction has to be identified 
	% uniquely. This is done using the goal_path of the unification. 
	% (the goal_path is filled by sr_direct__process_proc/7).
:- type contextvar 
	---> 	context(
			pvar		:: prog_var, 
			context		:: term__context,
			path		:: goal_path
		).
			

%-----------------------------------------------------------------------------%

process_goal(Background, Goal0, Goal, MaybeConditions) --> 
	{ Values0 = map__init },
	process_goal_2(Background, Goal0, Goal1, no, MaybeConditions, Values0),
	{ clean_all_left_overs(Goal1, Goal) }.

:- pred process_goal_2(background_info::in, hlds_goal::in, hlds_goal::out, 
		maybe(list(reuse_condition))::in, 
		maybe(list(reuse_condition))::out, values::in, 
		io__state::di, io__state::uo) is det.
process_goal_2(Background, Goal0, Goal, MaybeCond0, MaybeCond, Values0) --> 
	{ compute_values_single_goal(Background, Goal0, Values0, Values1) },  
	(
		{ map__is_empty(Values1) }
	-> 
		{ Goal = Goal0 },
		{ MaybeCond = MaybeCond0 }
	; 
		{ highest_degree_value(Values1, ContextVar, HighestValue) },
		dump_table(Values1, ContextVar, HighestValue), 
		{ annotate_reuses(ContextVar, HighestValue, Goal0, Goal1) },
		{ merge_conditions(HighestValue ^ conds, 
					MaybeCond0, MaybeCond1) },
		process_goal_2(Background, Goal1, Goal, 
				MaybeCond1, MaybeCond, Values0)
	). 

%-----------------------------------------------------------------------------%
% dumping the reuse-selections to output
%-----------------------------------------------------------------------------%

:- pred dump_table(values::in, contextvar::in, value::in, 
		io__state::di, io__state::uo) is det.
dump_table(Values, ContextVar, HighestValue) -->
	globals__io_lookup_bool_option(very_verbose, VeryVerbose),
	(
		{ VeryVerbose = yes }
	->
		io__write_string( "\n%---reuse table---------------------------------------------------------------%\n"),
		io__write_string( "%\t|\tvar\t|\tvalue\t|\tdegree\n"),
		io__write_string("%-sel- "),
		dump_selected_var(ContextVar, HighestValue), 
		io__write_string( "%---full table----------------------------------------------------------------%\n"),
		dump_full_table(Values),
		io__write_string( "%-----------------------------------------------------------------------------%\n")
	;
		[]
	).

:- import_module string. 
:- pred dump_selected_var(contextvar::in, value::in, 
		io__state::di, io__state::uo) is det.
dump_selected_var(context(Var, _Context, _GoalPath), Value) -->
	io__write_string("\t|\t"),
	io__write_int(term__var_to_int(Var)),
	io__write_string("\t|\t"),
	{ Val = Value ^ weight }, 
	(
		{ Val = yes(Float) }
	-> 	
		io__format("%.2f", [f(Float)])
	; 
		io__write_string("no reuse")
	),
	{ Degree = Value ^ degree }, 
	io__write_string("\t|\t"),
	io__write_int(Degree),
	io__write_string("\t"), 
	dump_value(Value),
	io__nl.

:- pred dump_value(value::in, io__state::di, io__state::uo) is det.
dump_value(Value) --> 
	io__write_string("("), 
	io__write_list(Value ^ vars, ",\n%----- \t|\t\t|\t\t|\t\t ", 
			dump_context_reuse_var),
	io__write_string(")").	

:- pred dump_context_reuse_var(context_reuse_var::in, 
		io__state::di, io__state::uo) is det.
dump_context_reuse_var(ContextReuseVar) -->
	{ ReuseType = ContextReuseVar ^ reuse_type },
	(
		{ReuseType = reuse_type(SameCons, Aold, Anew)}
	->
		{ ( SameCons = yes  -> S1 = "y" ; S1 = "n") },  
		{ string__int_to_string(arity_diff(ReuseType), S2) }, 
		{ string__int_to_string(Aold, S3) }, 
		{ string__int_to_string(Anew, S4) }, 
		{ string__append_list([S1,"-",S2,"-",S3,"-",S4], String) }
	;
 		{ String = "no" }
	),
	io__write_string(String).
	

:- pred dump_full_table(values::in, io__state::di, io__state::uo) is det.
dump_full_table(Values) --> 
	{ map__to_assoc_list(Values, AssocList) },
	list__foldl(
		pred(Entry::in, IO0::di, IO::uo) is det :-
		    (
			Entry = ContextVar - Value, 
			io__write_string("%----- ", IO0, IO1), 
			dump_selected_var(ContextVar, Value, IO1, IO)
		    ), 
		AssocList).
		

%-----------------------------------------------------------------------------%
:- pred merge_conditions(reuse_condition::in, 
		maybe(list(reuse_condition))::in,
		maybe(list(reuse_condition))::out) is det.

merge_conditions(C, no, yes([C])).
merge_conditions(C, yes(Conds), yes([C | Conds])).

%-----------------------------------------------------------------------------%

% The table is computed by traversing the whole procedure, for each
% dead deconstruction encountered, the value is computed based on
% the code that follows that deconstruction. 

:- pred compute_values_single_goal(background_info::in, 
		hlds_goal::in, values::in, values::out) is det. 

compute_values_single_goal(Background, Goal, Values0, Values):- 
	compute_values(Background, Goal, [], Values0, Values). 

:- pred compute_values(background_info::in, 
		list(hlds_goal)::in, values::in, values::out) is det.

compute_values(_Background, []) --> [].
compute_values(Background, [Goal | Goals]) --> 
	compute_values(Background, Goal, Goals).

	% compute_values(BG, CurrentGoal, Continuation, Values0, Values).
:- pred compute_values(background_info::in, hlds_goal::in, list(hlds_goal)::in, 
			values::in, values::out) is det.

compute_values(Background, Expr - _Info, Cont) --> 
	{ Expr = conj(Goals) },
	% continuation Cont might be non-empty. This can occur in the case
	% of if-then-elses, where the if- en then- parts are taken together. 
	{ list__append(Goals, Cont, NewGoals) },
	compute_values(Background, NewGoals).
compute_values(Background, Expr - _Info, Cont) --> 
	{ Expr = call(_, _, _, _, _, _) },
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) --> 
	{ Expr = generic_call(_, _, _, _) },
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) --> 
	{ Expr = switch(_, _, Cases) },
	{ list__map(
		pred(C::in, G::out) is det:- 
		    ( C = case(_, G) ),
		Cases, Goals) },
	list__foldl(
		pred(Goal::in, V0::in, V::out) is det:- 
		    ( compute_values(Background, Goal, [], V0, V) ),
		Goals),
	compute_values(Background, Cont).
compute_values(Background, Expr - Info, Cont, Values0, Values):- 
	Expr = unify(_Var, _Rhs, _Mode, Unification, _Context),
	goal_info_get_reuse(Info, ReuseInfo), 
	(
		ReuseInfo = choice(deconstruct(yes(Condition))), 
		Unification = deconstruct(Var, _, _, _, _, _)
	->
		value_init(Condition, Val0), 
		conjunction_value_of_dead_cel(Background, Unification, 
					Cont, Val0, Val), 
		(
			value_allows_reuse(Val)
		->
			goal_info_get_context(Info, Context),
			goal_info_get_goal_path(Info, Path), 
			ContextVar = context(Var, Context, Path),
			map__det_insert(Values0, ContextVar, Val, Values1)
		;
			Values1 = Values0
		)
	;
		Values1 = Values0
	), 
	compute_values(Background, Cont, Values1, Values). 

compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = disj(Goals) },
	list__foldl(
		pred(G::in, V0::in, V::out) is det:- 
		    ( compute_values(Background, G, [], V0, V) ),
		Goals),
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = not(Goal) },
		% if Goal contains deconstructions, they should not 
		% be reused within Cont. 
	compute_values(Background, Goal, []),
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = some(_, _, Goal) },
	compute_values(Background, Goal, Cont).
compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = if_then_else(_, If, Then, Else) },
	compute_values(Background, If, [Then]),
	compute_values(Background, Else, []),
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = foreign_proc(_, _, _, _, _, _, _) },
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = par_conj(_) },
	compute_values(Background, Cont).
compute_values(Background, Expr - _Info, Cont) -->
	{ Expr = shorthand(_) },
	compute_values(Background, Cont).

%-----------------------------------------------------------------------------%

	% compute the value of a dead cel with respect to its possible
	% reuses. If reuse is possible, collect the context_reuse_var 
	% information of the constructions involved. 
	% In every conjunction, the dead cell can only be reused once: 
	% this means that for each branch of the conjunction, a separate
	% value must be computed, and only the one with the highest value
	% is kept. 
:- pred conjunction_value_of_dead_cel(background_info::in, 
		unification::in, list(hlds_goal)::in, 
		value::in, value::out) is det. 

conjunction_value_of_dead_cel(Background, Deconstruction, 
		Cont, Val0, Val):- 
	list__map(
		pred(G::in, V::out) is det:- 
		    ( value_of_dead_cel_in_goal(Background, 
			Deconstruction, G, Val0, V)), 
		Cont, DisjunctiveVals), 
	count_candidates(DisjunctiveVals, Degree), 
	highest_value_in_list(DisjunctiveVals, Val0, Val1), 
	Val = Val1 ^ degree := Degree. 

	% compute the value of a dead cell with respect to a 
	% disjunction. If reuse is possible within the branches, the value
	% of the disjunction is set to the average of the values of the
	% branches. Branches not allowing any reuse have value 0. 
	% The context_reuse_vars are the union of all the
	% context_reuse_vars of the branches. 
:- pred disjunction_value_of_dead_cel(background_info::in,
		unification::in, list(hlds_goal)::in, 
		value::in, value::out) is det.
disjunction_value_of_dead_cel(Background, Deconstruction, 
		Branches, Val0, Val):- 
	(
		Branches = []
	-> 	
		Val = Val0
	; 
		list__map(
			pred(G::in, V::out) is det:- 
			    ( value_of_dead_cel_in_goal(Background, 
				Deconstruction, G, Val0, V)), 
			Branches, BranchVals), 
		count_candidates(BranchVals, Degree), 
		average_value(BranchVals, Val1),
		Val = Val1 ^ degree := Degree
	).

:- pred count_candidates(list(value)::in, int::out) is det.
count_candidates(Values, Degree):- 
	list__foldl(
		pred(Val::in, D0::in, D::out) is det:- 
		    (
			D = D0 + Val ^ degree
		    ), 
		Values, 
		0, Degree). 

	% Compute the value of a dead cell for a specific goal. 
:- pred value_of_dead_cel_in_goal(background_info::in, 
				unification::in, hlds_goal::in, 
				value::in, value::out) is det.
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - _Info) --> 
	{ Goal = conj(Goals) },
	conjunction_value_of_dead_cel(Background,
		Deconstruct, Goals).
value_of_dead_cel_in_goal(_Background, 
		_Deconstruct, Goal - _Info) -->
	{ Goal = call(_, _, _, _, _, _) }.
value_of_dead_cel_in_goal(_Background, 
		_Deconstruct, Goal - _Info) -->
	{ Goal = generic_call(_, _, _, _) }.
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - _Info) -->
	{ Goal = switch(_, _, Cases) },
	{ list__map(
		pred(C::in, G::out) is det:- 
		    ( C = case(_, G) ), 
		Cases, Branches) }, 
	disjunction_value_of_dead_cel(Background, 
		Deconstruct, Branches).
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - Info, Val0, Value):- 
	Goal = unify(_, _, _, Unification, _Context),
	ModuleInfo = Background ^ module_info, 
	Vartypes = Background ^ vartypes, 
	(
		Unification = construct(Var, Cons, Args, _, _, _, _),
		Deconstruct = deconstruct(DeadVar, DeadCons, 
					DeadArgs, _, _, _),
		goal_info_get_reuse(Info, choice(construct(ReuseVars))), 
		PureReuseVars = set__map(
					func(RV) = V :-
					    ( V = RV ^ var ),
					ReuseVars),
		set__contains(PureReuseVars, DeadVar),
		% XXX this should be moved to the place where the
		% ReuseVars are computed. 
		\+ no_tag_type(ModuleInfo, Vartypes, DeadVar)
	-> 
		% if all the conditions above are met, reuse is possible
		% here. What is the gain/value of the reuse? 
		has_secondary_tag(ModuleInfo, Vartypes, Var, Cons, SecTag), 
		has_secondary_tag(ModuleInfo, Vartypes, DeadVar, DeadCons, 
				DeadSecTag), 
		ReuseFields = already_correct_fields(SecTag, Args, 
				DeadSecTag - DeadArgs),
		make_contextvar(Var, Info, ContextVar), 
		compute_new_value(Background ^ constraint, 
			Cons, DeadCons, 
			list__length(Args), 
			list__length(DeadArgs), 
			list__length(list__delete_all(ReuseFields, no)),
			MaybeResult, ReuseType), 

		ContextReuseVar = context_reuse_var(
					ContextVar, 
					yes([DeadCons]),
					yes(ReuseFields), 
					ReuseType), 
	
		(
			MaybeResult = yes(Int)
		-> 
			Value = entry(Val0 ^ conds, yes(float(Int)),
					[ContextReuseVar], 1)
		; 
			Value = Val0
		)
	; 
		Value = Val0
	). 

		
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - _Info) -->
	{ Goal = disj(Branches) },
	disjunction_value_of_dead_cel(Background, 
		Deconstruct, Branches).
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - _Info) -->
	{ Goal = not(NegatedGoal) },
	value_of_dead_cel_in_goal(Background, 
		Deconstruct, NegatedGoal).
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - _Info) -->
	{ Goal = some(_, _, SGoal) },
	value_of_dead_cel_in_goal(Background, 
		Deconstruct, SGoal).
value_of_dead_cel_in_goal(Background, 
		Deconstruct, Goal - _Info, Val0, Value):- 
	Goal = if_then_else(_, If, Then, Else),
	conjunction_value_of_dead_cel(Background, 
		Deconstruct, [If, Then], Val0, Val1), 
	value_of_dead_cel_in_goal(Background,
		Deconstruct, Else, Val0, Val2), 
	average_value([Val1, Val2], Value).
value_of_dead_cel_in_goal(_Background, 
		_Deconstruct, Goal - _Info) -->
	{ Goal = foreign_proc(_, _, _, _, _, _, _) }.
value_of_dead_cel_in_goal(_Background, 
		_Deconstruct, Goal - _Info) -->
	{ Goal = par_conj(_) }.
value_of_dead_cel_in_goal(_Background, 
		_Deconstruct, Goal - _Info) -->
	{ Goal = shorthand(_) }.
	

	
%-----------------------------------------------------------------------------%
	% Gain = (Alfa + Gamma) * ArityNewCell + Beta
	%		- Gamma * (ArityNewCell - UptoDateFields)
	%		- ( SameCons? Beta; 0)
	%		- Alfa * (ArityOldCell - ArityNewCell)
	% Alfa represents the number of instructions to create a
	% new cell (relative to the size of the cell)
	% Gamma represents the number of instructions to update a field
	% within a cell. 
	% Beta represents the cost of updating/setting the cons_id field. 

	% compute_new_value(Constraint, ArityNewCell, ArityDeadCell, 
	%	UptoDateFields, MaybeFloat).
:- pred compute_new_value(sr_choice_util__constraint::in, 
		cons_id::in, cons_id::in, int::in, 
		int::in, int::in, maybe(int)::out, 
		reuse_type::out) is det.

compute_new_value(Constraint, NewCons, DeadCons, ArityNewCell, ArityDeadCell, 
		UpToDateFields, MaybeResult, ReuseType):- 
	DiffArity = ArityDeadCell - ArityNewCell, 
	(
		NewCons = DeadCons
	-> 
		SameCons = yes		
	; 
		SameCons = no	
	), 
	(
		( (
			Constraint = within_n_cells_difference(N),
			DiffArity =< N
		)
		; 
		(
			Constraint = same_cons_id, 
			SameCons = yes
		) )
	->
		Alfa = 5, Gamma = 1, Beta = 1, 
		( SameCons = yes -> SameConsV = 0; SameConsV = 1),
	 	Int = ( (Alfa + Gamma) * ArityNewCell + Beta
	 		- Gamma * (ArityNewCell - UpToDateFields)
			- Beta * SameConsV
			- Alfa * DiffArity ),
	% 	Int1 = 2 * Alfa * ArityNewCell + Gamma * UpToDateFields, 
	%	Int = Int1 - Alfa * ArityDeadCell, 
		(
			Int > 0
		->
			MaybeResult = yes(Int), 
			ReuseType = reuse_type(SameCons, 
				ArityDeadCell, ArityNewCell)
			
		; 
			MaybeResult = no,
			ReuseType = no_reuse
		)	
	;
		MaybeResult = no,
		ReuseType = no_reuse
	). 
			
	


%-----------------------------------------------------------------------------%

	% Once a dead cell is selected from the table, all the constructions
	% involved with reusing this dead cell have to be marked. 
:- pred annotate_reuses(contextvar::in, value::in, hlds_goal::in, 
		hlds_goal::out) is det.

annotate_reuses(ContextVar, Value, E0 - I0, E - I):- 
	E0 = conj(Goals0),
	list__map(annotate_reuses(ContextVar, Value), Goals0, Goals),
	E = conj(Goals), 
	I = I0.
annotate_reuses(_ContextVar, _Value, E0 - I0, E - I):- 
	E0 = call(_,_,_,_,_,_),
	E = E0, 
	I = I0.
annotate_reuses(_ContextVar, _Value, E0 - I0, E - I):- 
	E0 = generic_call(_,_,_,_),
	E = E0, 
	I = I0. 
annotate_reuses(ContextVar, Value, E0 - I0, E - I):- 
	E0 = switch(V, CF, Cases0),
	list__map(
		pred(C0::in, C::out) is det:- 
		    ( C0 = case(Cons, Goal0),
		      annotate_reuses(ContextVar, Value, Goal0, Goal), 
		      C = case(Cons, Goal)
		    ), 
		Cases0, Cases),
	E = switch(V, CF, Cases), 
	I = I0. 

:- pred make_contextvar(prog_var::in, hlds_goal_info::in, 
		contextvar::out) is det.
make_contextvar(Var, Info, ContextVar):- 
	goal_info_get_context(Info, Context),
	goal_info_get_goal_path(Info, Path), 
	ContextVar = context(Var, Context, Path). 
:- pred contextvar_equal(contextvar::in, contextvar::in) is semidet.
contextvar_equal(C1, C2):-
	C1 = context(Var, Context, Path), 
	C2 = context(Var, Context, Path). 

annotate_reuses(DeadContextVar, Value, E0 - I0, E - I):- 
	E0 = unify(Var, _Rhs, _Mode, _Unification0, _Context),
	make_contextvar(Var, I0, ContextVar), 
	(
		contextvar_equal(ContextVar, DeadContextVar)
	->
		% then this must be a deconstruction
		goal_info_set_reuse(I0, potential_reuse(cell_died), I),
		E = E0
	;
		list__filter(
			pred(ReuseContextVar::in) is semidet :- 
			    (
				contextvar_equal(ContextVar, 
						ReuseContextVar ^ var)
			    ),
			Value ^ vars,
			ReuseVars),
		(
			ReuseVars = []
		->
			I = I0,
			E = E0
		; 
			NoDups = list__remove_dups(ReuseVars), 
			NoDups = [ReuseVar], 
			ReuseVar = context_reuse_var(_, MConsIds, 
				MReuseFields, _),
			MConsIds = yes(ConsIds), 
			MReuseFields = yes(ReuseFields)
		->
			Cond = Value ^ conds,
			(
				Cond = always, 
				Conditional = no
			; 
				Cond = condition(_,_,_),
				Conditional = yes
			),
			CellReused = cell_reused( DeadContextVar ^ pvar, 
					Conditional,
					ConsIds, ReuseFields),
			(
				Conditional = yes, 
				KindReuse = potential_reuse(CellReused)
			; 
				Conditional = no, 
				% If the reuse is unconditional, then
				% reuse is not just potentially possible, 
				% but alwasy possible, so skipping the
				% potential phase is perfectly safe. 
				% (see also sr_indirect__call_verify_reuse)
				KindReuse = reuse(CellReused)
			), 	
			goal_info_set_reuse(I0, KindReuse, I), 
			E = E0
		;
			% ReuseVars = [_|_]
			require__error("(sr_choice_graphing) annotate_reuses: multiple reuses for same contextvariable.\n")
		)
	).

annotate_reuses(ContextVar, Value, E0 - I0, E - I):- 
	E0 = disj(Goals0), 
	list__map(annotate_reuses(ContextVar, Value), Goals0, Goals),
	E = disj(Goals), 
	I = I0. 
annotate_reuses(ContextVar, Value, E0 - I0, E - I):- 
	E0 = not(Goal0), 
	annotate_reuses(ContextVar, Value, Goal0, Goal), 
	E = not(Goal),
	I = I0. 
annotate_reuses(ContextVar, Value, E0 - I0, E - I):- 
	E0 = some(Vars, CanRemove, Goal0), 
	annotate_reuses(ContextVar, Value, Goal0, Goal), 
	E = some(Vars, CanRemove, Goal), 
	I = I0. 
annotate_reuses(ContextVar, Value, E0 - I0, E - I):- 
	E0 = if_then_else(V, If0, Then0, Else0), 
	annotate_reuses(ContextVar, Value, If0, If),
	annotate_reuses(ContextVar, Value, Then0, Then),
	annotate_reuses(ContextVar, Value, Else0, Else),
	E = if_then_else(V, If, Then, Else), 
	I0 = I. 
annotate_reuses(_ContextVar, _Value, E0 - I0, E - I):- 
	E0 = foreign_proc(_, _, _, _, _, _, _), 
	E = E0, 
	I = I0. 
annotate_reuses(_ContextVar, _Value, E0 - I0, E - I):- 
	E0 = par_conj(_), 
	E = E0, 
	I = I0.
annotate_reuses(_ContextVar, _Value, E0 - I0, E - I):- 
	E0 = shorthand(_),
	E = E0, 
	I = I0. 

%-----------------------------------------------------------------------------%
% Genaral manipulations on values, value, etc.. 
%-----------------------------------------------------------------------------%

:- pred highest_degree_value(values::in, contextvar::out, value::out) is det.
highest_degree_value(Values0, Key, Value):-
	map__keys(Values0, Keys), 
	(
		Keys = [K|R]
	->
		map__lookup(Values0, K, V), 
		list__foldl(maximal_degree_value(Values0), R, 
				K - V, Key - Value)
	;
		require__error("(sr_choice_graphing) highest value: empty map.\n")
	).

:- pred maximal_degree_value(map(contextvar, value)::in, 
		contextvar::in, pair(contextvar, value)::in, 
		pair(contextvar, value)::out) is det.
maximal_degree_value(Map, Var, TempMax, NewMax):- 
	map__lookup(Map, Var, Value),
	TempMax = TempVar - TempValue, 
	(
			% if the values are equal, the first solution is kept,
			% i.e. TempMax
		degree_value_gt(Value, TempValue)
	-> 
		NewMax = Var - Value
	; 
		NewMax = TempVar - TempValue
	). 

:- pred degree_value_gt(value::in, value::in) is semidet. 
degree_value_gt(V1, V2):- 
	Val1 = V1 ^ weight, 
	Val2 = V2 ^ weight,
	(
		Val2 = no
	; 
		Val2 = yes(Float2),
		Val1 = yes(Float1),
		D1 = Float1 / float(V1 ^ degree), 
		D2 = Float2 / float(V2 ^ degree), 
		D1 > D2
	). 

:- pred value_gt(value::in, value::in) is semidet. 
value_gt(V1, V2):- 
	Val1 = V1 ^ weight, 
	Val2 = V2 ^ weight,
	(
		Val2 = no
	; 
		Val2 = yes(Float2),
		Val1 = yes(Float1),
		Float1 > Float2
	). 

:- pred value_allows_reuse(value::in) is semidet. 
value_allows_reuse(Value) :- 
	Val = Value ^ weight, 
	Val = yes(Float),
	% the computed value should be larger than zero. 
	Float > 0.0.
	
:- pred highest_value_in_list(list(value)::in, value::in, value::out) is det.
highest_value_in_list([], Val0, Val0).
highest_value_in_list([V | R], Val0, Val):- 
	(
		value_gt(V, Val0)
	-> 
		highest_value_in_list(R, V, Val)
	; 
		highest_value_in_list(R, Val0, Val)
	). 

:- pred average_value(list(value)::in, value::out) is det.
average_value(List, Value):- 
	(
		List = [ Val1 | _ ]
	-> 
		list__length(List, Length),
		list__foldl2(
			pred(V::in, S0::in, S::out, R0::in, R::out) is det:- 
			    (
				MaybeVal = V ^ weight,
				ReuseVars = V ^ vars, 
				(
					MaybeVal = yes(Fnew),
					(
						S0 = yes(F0)
					-> 
						S = yes(F0 + Fnew)
					;
						S = yes(Fnew)
					),
					list__append(ReuseVars, R0, R)
				;
					MaybeVal = no,
					S = S0, R = R0
				)
			     ),
			List, 
			no, TotalS, 
			[], ContextReuseVars ),
		(
			TotalS = yes(Float)
		-> 
			AverageFloat = Float / float(Length),
			AverageVal = yes(AverageFloat)
		;
			AverageVal = no
		), 
		Value = entry(Val1 ^ conds, AverageVal, ContextReuseVars, 1)
	;
		require__error("(sr_choice_graphing) average_value: empty list.\n")
	). 
		
			
				
:- pred value_init(reuse_condition::in, value::out) is det.
value_init(Cond, entry(Cond, no, [], 0)). 


:- func arity_diff(reuse_type) = int. 
arity_diff(T) = R :- 
	( 
		T = reuse_type(_, O, N)
	-> 
		R = O - N
	;  
		require__error("(sr_choice_graphing) arity_diff: no reuse, so no old or new arities.")
	). 
	
%-----------------------------------------------------------------------------%
	% After the selection pass, a final pass is needed to clean up
	% all the pending reuse annotations. All choice-annotations
	% are replaced by either 
	% 	- potential_reuse(cell_died)	% unconditional death
	% 	- potentail_reuse(no_reuse)
	% All other reuse-annotations are kept as is. 
:- pred clean_all_left_overs(hlds_goal::in, hlds_goal::out) is det.

clean_all_left_overs(G0 - I0, G - I):- 
	G0 = conj(Goals0),
	list__map(clean_all_left_overs, Goals0, Goals),
	G  = conj(Goals),
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = call( _, _, _, _, _, _),
	G  = G0,
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = generic_call( _, _, _, _),
	G  = G0, 
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = switch(A, B, Cases0),
	list__map(
		pred(C0::in, C::out) is det:-
		    ( C0 = case(Cons, Goal0), 
		      clean_all_left_overs(Goal0, Goal), 
		      C = case(Cons, Goal) ), 
		Cases0, Cases), 
	G  = switch(A, B, Cases), 
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = unify(A, B, C, Unification0, D),
	goal_info_get_reuse(I0, ReuseInfo0), 
	possible_cgc(Unification0, ReuseInfo0, Unification, ReuseInfo),
	G = unify(A, B, C, Unification, D),
	goal_info_set_reuse(I0, ReuseInfo, I).

:- pred possible_cgc(hlds_goal__unification::in, reuse_goal_info::in, 
		hlds_goal__unification::out, reuse_goal_info::out) is det.
possible_cgc(Unif0, ReuseInfo0, Unif, ReuseInfo):- 
	(
		Unif0 = deconstruct(A, B, C, D, E, _),
		ReuseInfo0 = choice(deconstruct(yes(always)))
	->
		Unif = deconstruct(A, B, C, D, E, yes),
		ReuseInfo = potential_reuse(cell_died)
	; 
		Unif = Unif0,
		(
			ReuseInfo0 = choice(_)
		-> 
			ReuseInfo = potential_reuse(no_reuse)
		; 
			ReuseInfo = ReuseInfo0
		)
	).
			
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = disj(Goals0),
	list__map(clean_all_left_overs, Goals0, Goals), 
	G  = disj(Goals), 
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = not(Goal0),
	clean_all_left_overs(Goal0, Goal), 
	G  = not(Goal), 
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = some(A, B, Goal0),
	clean_all_left_overs(Goal0, Goal), 
	G  = some(A, B, Goal), 
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = if_then_else(A, If0, Then0, Else0),
	clean_all_left_overs(If0, If), 
	clean_all_left_overs(Then0, Then), 
	clean_all_left_overs(Else0, Else), 
	G  = if_then_else(A, If, Then, Else),  
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = foreign_proc(_, _, _, _, _, _, _),
	G  = G0,
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = par_conj(_),
	G  = G0,
	I  = I0.
clean_all_left_overs(G0 - I0, G - I):- 
	G0 = shorthand( _),
	G  = G0,
	I  = I0.
