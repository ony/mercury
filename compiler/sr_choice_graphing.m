%-----------------------------------------------------------------------------%
% Copyright (C) 2001-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_choice_graphing
% Main authors: nancy
% 
% Given a goal annotated with preliminary possible reuse information, this pass
% computes the concrete assignements of which constructions can profit of dead
% cells coming from deconstructions.  The assignment problem is translated into
% a mapping problem (inspired from Debray's paper: "On copy avoidance in single
% assignment languages", and restricted to reuse of dead cells by at most one
% new cell).
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
% Note that cells being deconstructed in the different branches of a
% disjunction can now also be reused after the the disjunction. 
% e.g.:
%	( 
%		..., X => f(... ), ... 		% X dies
%	; 
%		..., X => g(... ), ... 		% X dies
%	), 
%	Y <= f(... ), ... 			% Y can reuse X
% In this example, it is allowed to reuse X for Y. And it will also be
% discovered by the analysis. 
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_choice_graphing.
:- interface. 

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module structure_reuse__sr_choice_util.
:- import_module structure_reuse__sr_data.

:- import_module io, std_util, list. 

:- type background_info. 
:- pred set_background_info(sr_choice_util__strategy::in, module_info::in, 
		vartypes::in, background_info::out) is det.

	% Annotate each deconstruction/construction unification with
	% whether they die, can potentially reuse a dead cell or are
	% not possible for reuse. 
:- pred sr_choice_graphing__process_goal(
		background_info::in, 
		dead_cell_table::in, 
		hlds_goal::in, hlds_goal::out,
		maybe(list(reuse_condition))::out, 
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%
:- implementation. 

:- import_module check_hlds__type_util.
:- import_module hlds__hlds_data.
:- import_module hlds__passes_aux.
:- import_module libs__globals.
:- import_module libs__options.
:- import_module parse_tree__prog_data.

:- import_module term, map, float, bool, set, require, int. 
:- import_module string, multi_map. 
%-----------------------------------------------------------------------------%
:- type background_info 
	---> 	background(
			strategy	:: sr_choice_util__strategy,
			module_info	:: module_info, 
			vartypes	:: vartypes
		).

set_background_info(Strategy, ModuleInfo, VarTypes, BG):-
	BG = background(Strategy, ModuleInfo, VarTypes). 

%-----------------------------------------------------------------------------%
:- type deconstruction_spec
	---> 	decon(
			decon_var	:: prog_var, 
			decon_pp	:: program_point, 
			decon_cons_id	:: cons_id, 
			decon_args	:: prog_vars, 
			decon_conds	:: reuse_condition
		).
:- type construction_spec 
	---> 	con(
			con_pp		:: program_point, 
			con_reuse	:: reuse_type
		).

	% The reuse-type is a basic identification of whether the cons-ids
	% involved in the reuse are the same, what the arities of the old and
	% new cells are, and which arguments don't have to be updated. 
:- type reuse_type 
	---> 	reuse_type(
			same_cons	:: bool, 	
			reuse_fields 	:: list(bool),
				% Each 'no' means that the corresponding
				% argument within the constructed cell does not
				% need to be updated. Note that
				% list__length(reuse_fields) = arity_old. 
			tmp_value	:: float
		). 
		
		% One match is a description of a list of deconstructions and a
		% list of constructions. The deconstructions and constructions
		% can all be coded into reuses, as they are such that at
		% run-time at most one deconstruction yielding the dead cell
		% will occur on the same execution path as a construction that
		% can reuse that cell. 
		% This means that all the deconstructions can be coded as
		% deconstructions yielding dead cell, and all the constructions
		% can be coded as constructions reusing the cell that becomes
		% available through one of the deconstructions.
:- type match
	---> 	match(
			% dead_var	:: prog_var, 
			decon_specs	:: list(deconstruction_spec),
			con_specs	:: list(construction_spec),
			match_value	:: float,
			match_degree	:: int
		).
	
:- type match_table == multi_map(prog_var, match).
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

process_goal(Background, DeadCellTable0, !Goal, MaybeConditions, !IO) :- 
	globals__io_lookup_bool_option(very_verbose, VeryVerbose, !IO),
	process_goal_2(Background, DeadCellTable0, DeadCellTable1, 
		!Goal, [], Conditions, !IO),
	dead_cell_table_remove_conditionals(DeadCellTable1, 
		DeadCellTable), 
	(
		% If there are some unconditional dead cells unassigned, then 
		% annotate them for cgc. 
		\+ map__is_empty(DeadCellTable)
	-> 
		maybe_write_string(VeryVerbose, "% Marking CGC's. \n", !IO), 
		check_cgc(DeadCellTable, !Goal)
	;
		maybe_write_string(VeryVerbose, "% No CGC's. \n", !IO)	
	),
	(
		Conditions = [_|_]
	-> 	MaybeConditions = yes(Conditions)
	;	MaybeConditions = no
	).

:- pred process_goal_2(background_info::in, 
		dead_cell_table::in, dead_cell_table::out, 
		hlds_goal::in, hlds_goal::out, 
		list(reuse_condition)::in, 
		list(reuse_condition)::out, 
		io__state::di, io__state::uo) is det.
process_goal_2(Background, !DC, !Goal, !Conditions, !IO) :- 
	globals__io_lookup_bool_option(very_verbose, VeryVerbose, !IO),
	compute_match_table(Background, !.DC, !.Goal, MatchTable, !IO),  
	(
		multi_map__is_empty(MatchTable)
	-> 
		true
	;
			% 1. select the deconstructions-constructions with
			% highest value. 
		(
			highest_match_degree_ratio(MatchTable, Match)
		->
			% 2. dump all the matches recorded in the table,
			% highlight the match with the highest value. 
			maybe_write_string(VeryVerbose, "% Reuse results: \n", 
				!IO), 
			maybe_dump_match_table(VeryVerbose, MatchTable, 
				Match, !IO), 
			% 3. realise the reuses by explicitly annotating the
			% procedure goal. 
			annotate_reuses(Match, !Goal), 
			% remove the deconstructions from the available map of
			% dead cells: 
			list__foldl(
				(pred(Dec::in, DCin::in, DCout::out) is det :-
					PP = Dec ^ decon_pp, 
					dead_cell_table_remove(PP, DCin, 
						DCout)
				), Match ^ decon_specs, !DC),
			% 4. Add the conditions involved in the reuses to the
			% existing conditions. 
			merge_conditions(Match, !Conditions), 
			% 5. Process the goal for further reuse-matches. 
			process_goal_2(Background, !DC, !Goal, 
				!Conditions, !IO)
		;
			true
		)
	). 

%-----------------------------------------------------------------------------%

:- func line_length = int. 
line_length = 79.

:- pred dump_line(string::in, io__state::di, io__state::uo) is det.
dump_line(Msg, !IO) :- 
	Prefix = "%---", 
	Start = string__append(Prefix, Msg), 
	Remainder = line_length - string__length(Start) - 1, 
	Line = Start ++ string__duplicate_char('-', Remainder),
	io__write_string(Line, !IO),
	io__write_string("%\n", !IO).
	
:- pred maybe_dump_match_table(bool::in, match_table::in, match::in,
		io__state::di, io__state::uo) is det.

maybe_dump_match_table(VeryVerbose, MatchTable, HighestMatch, !IO) :- 
	(
		VeryVerbose = yes
	->
		dump_line("reuse table", !IO), 
		io__write_string("%\t|\tvar\t|\tvalue\t|\tdegree\n", !IO),
		dump_match("%-sel- ", HighestMatch, !IO),
		dump_full_table(MatchTable, !IO),
		dump_line("", !IO)
	;
		true
	).

:- pred dump_match(string::in, match::in, io__state::di, io__state::uo) is det.
dump_match(Prefix, Match, !IO):- 
	io__write_string(Prefix, !IO), 
	io__write_string("\t|\t", !IO),
	io__write_int(term__var_to_int(match_get_dead_var(Match)), !IO),
	io__write_string("\t|\t", !IO),
	Val = Match ^ match_value, 
	(
		Val \= 0.00 
	-> 	
		io__format("%.2f", [f(Val)], !IO)
	; 
		io__write_string("-", !IO)
	),
	Degree = Match ^ match_degree, 
	io__write_string("\t|\t", !IO),
	io__write_int(Degree, !IO),
	io__write_string("\t", !IO), 
	dump_match_details(Match, !IO),
	io__nl(!IO).

:- pred dump_match_details(match::in, io__state::di, io__state::uo) is det.
dump_match_details(Match, !IO) :- 
	Conds = list__map(
		(func(DeconSpec) = Cond :- 
			Cond = DeconSpec ^ decon_conds), 
			Match ^ decon_specs),
	(
		list__takewhile(
			reuse_condition_equal(always), 
			Conds, _, [])
	-> 
		CondsString = "A"
	;
		CondsString = "C"
	), 

	D = list__length(Match ^ decon_specs), 
	C = list__length(Match ^ con_specs), 
	string__append_list(["d: ", int_to_string(D), ", c: ", 
		int_to_string(C), 
		", Co: ", CondsString], Details), 
	io__write_string(Details, !IO).

:- pred dump_full_table(match_table::in, io__state::di, io__state::uo) is det.
dump_full_table(MatchTable, !IO) :- 
	(
		multi_map__is_empty(MatchTable)
	-> 
		dump_line("empty match table", !IO)
	; 
		dump_line("full table (start)", !IO), 
		multi_map__values(MatchTable, Matches), 
		list__foldl(dump_match("%-----"), Matches, !IO),
		dump_line("full table (end)", !IO)
	).

:- pred maybe_dump_full_table(bool::in, match_table::in, io__state::di,
		io__state::uo) is det.
maybe_dump_full_table(no, _M, !IO).
maybe_dump_full_table(yes, M, !IO) :- dump_full_table(M, !IO).

%-----------------------------------------------------------------------------%
:- pred merge_conditions(match::in, list(reuse_condition)::in,
		list(reuse_condition)::out) is det.

merge_conditions(Match, !Conditions) :- 
	P = (pred(D::in, C::out) is det :- 
		C = D ^ decon_conds),
	list__map(P, Match ^ decon_specs, Conds),
	list__append(Conds, !Conditions).

%-----------------------------------------------------------------------------%

% The table is computed by traversing the whole procedure, for each
% dead deconstruction encountered, the value is computed based on
% the code that follows that deconstruction. 

:- pred compute_match_table(background_info::in, 
		dead_cell_table::in, 
		hlds_goal::in, match_table::out, 
		io__state::di, io__state::uo) is det.

compute_match_table(Background, DC, Goal, MatchTable, !IO) :- 
	multi_map__init(MatchTable0), 
	compute_match_table(Background, DC, 
		Goal, [], MatchTable0, MatchTable, !IO).

:- pred compute_match_table(background_info::in,
		dead_cell_table::in, list(hlds_goal)::in, 
		match_table::in, match_table::out, 
		io__state::di, io__state::uo) is det.

compute_match_table(_Background, _DC, [], !Table, !IO). 
compute_match_table(Background, DC, [Goal | Goals], !Table, !IO) :- 
	compute_match_table(Background, DC, Goal, Goals, !Table, !IO).

	% compute_values(BG, CurrentGoal, Continuation, Values0, Values).
:- pred compute_match_table(background_info::in, 
		dead_cell_table::in, hlds_goal::in, 
		list(hlds_goal)::in, match_table::in, match_table::out, 
		io__state::di, io__state::uo) is det.

compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = conj(Goals),
	% continuation Cont might be non-empty. This can occur in the case
	% of if-then-elses, where the if- en then- parts are taken together. 
	list__append(Goals, Cont, NewGoals),
	compute_match_table(Background, DC, NewGoals, !Table, !IO).
compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = call(_, _, _, _, _, _),
	compute_match_table(Background, DC, Cont, !Table, !IO).
compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = generic_call(_, _, _, _),
	compute_match_table(Background, DC, Cont, !Table, !IO).
compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = switch(_, _, Cases),
	list__map(
		pred(C::in, G::out) is det:- 
		    ( C = case(_, G) ),
		Cases, Goals),
	multi_map__init(Table0), 
	list__map_foldl(
		pred(Goal::in, T::out, IO0::di, IO1::uo) is det:- 
		    ( compute_match_table(Background, DC, Goal, [], Table0, 
		    		T, IO0, IO1) ),
		Goals, SwitchTables, !IO),
	list__foldl(multi_map__merge, SwitchTables, !Table),
	% Each of the SwitchTables will contain an entry for each
	% deconstruction yielding a dead variable. If every branch contains the
	% same var dying, then we may need to check if it can not be used
	% outside of the switch. 
	(
		process_possible_common_dead_vars(Background, Cont, 
			SwitchTables, CommonDeadVarsTables, !IO)
	-> 
		list__foldl(multi_map__merge, CommonDeadVarsTables, !Table)
	; 
		true
	),
	compute_match_table(Background, DC, Cont, !Table, !IO).
compute_match_table(Background, DC, Expr - Info, Cont, !Table, !IO) :- 
	Expr = unify(_Var, _Rhs, _Mode, Unification, _Context),
	program_point_init(Info, PP), 
	(
		Unification = deconstruct(Var, ConsId, Args, _, _, _),
		Condition = dead_cell_table_search(PP, DC),
			% XXX this test should move to sr_dead! 
		\+ no_tag_type(Background ^ module_info, 
			Background ^ vartypes, Var)
	->
		deconstruction_spec_init(Var, PP, ConsId, Args, Condition, DS),
		match_init([DS], Match0), 
		find_best_match_in_conjunction(Background, Cont, 
				Match0, Match), 
		multi_map__set(!.Table, Var, Match, !:Table)
	;
		true
	), 
	compute_match_table(Background, DC, Cont, !Table, !IO). 

compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = disj(Goals),
	multi_map__init(DisjTable0), 
	list__map_foldl(
		pred(G::in, T::out, IO0::di, IO1::uo) is det:- 
		    ( compute_match_table(Background, DC, G, [], 
		    		DisjTable0, T, IO0, IO1) ),
		Goals, DisjTables, !IO),
	% Each of the DisjTables will contain an entry for each deconstruction
	% yielding a dead variable. If every branch contains the same var
	% dying, then we may need to check if it can not be used outside of the
	% disjunction. 
	list__foldl(multi_map__merge, DisjTables, !Table), 
	(
		process_possible_common_dead_vars(Background, 
			Cont, DisjTables, 
			CommonDeadVarsDisjTables, !IO)
	-> 
		list__foldl(multi_map__merge, CommonDeadVarsDisjTables, !Table)
	; 
		true
	),
	compute_match_table(Background, DC, Cont, !Table, !IO).

:- pred process_possible_common_dead_vars(background_info::in, 
		hlds_goals::in, list(match_table)::in, 
		list(match_table)::out, 
		io__state::di, io__state::uo) is semidet.
process_possible_common_dead_vars(Background, Cont, DisjTables, 
		ExtraTables, !IO) :-
	globals__io_lookup_bool_option(very_verbose, VeryVerbose, !IO),
	maybe_write_string(VeryVerbose, "\n% Processing possible common dead vars.\n", !IO), 
	list__foldl(maybe_dump_full_table(VeryVerbose), DisjTables, !IO),
	DisjTables = [First | Rest], 
	Intersect = (pred(T::in, Set0::in, Set::out) is det :- 
			map__keys(T, Keys), 
			Set = set__intersect(Set0, list_to_set(Keys))
		),
	FirstSet = list_to_set(map__keys(First)), 
	list__foldl(Intersect, Rest, FirstSet, CommonDeadVars),
	list__filter_map(process_common_var(Background, Cont, DisjTables), 
		to_sorted_list(CommonDeadVars), ExtraTables). 

:- pred process_common_var(background_info::in, hlds_goals::in,
		list(match_table)::in, prog_var::in, 
		match_table::out) is semidet.
process_common_var(Background, Cont, DisjTables, CommonDeadVar, Table) :- 
	P = (pred(T::in, DeconSpecs0::in, DeconSpecs::out) is det :- 
		multi_map__lookup(T, CommonDeadVar, Ms), 
		PP = (pred(M::in, Ds0::in, Ds::out) is det :- 
			D = M ^ decon_specs, 
			append(D, Ds0, Ds)), 
		list__foldl(PP, Ms, [], NewDeconSpecs), 
		append(DeconSpecs0, NewDeconSpecs, DeconSpecs)
		),
	list__foldl(P, DisjTables, [], FullDeconSpecs), 
	match_init(FullDeconSpecs, Match0),
	find_best_match_in_conjunction(Background, Cont, Match0, Match),
	match_allows_reuse(Match), % can fail
	multi_map__init(Table0), 
	multi_map__det_insert(Table0, CommonDeadVar, Match, Table).

compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = not(Goal),
		% if Goal contains deconstructions, they should not 
		% be reused within Cont. 
	compute_match_table(Background, DC, Goal, [], !Table, !IO),
	compute_match_table(Background, DC, Cont, !Table, !IO).
compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = some(_, _, Goal),
	compute_match_table(Background, DC, Goal, Cont, !Table, !IO).
compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = if_then_else(_, If, Then, Else),
	multi_map__init(Table0), 
	compute_match_table(Background, DC, If, [Then], Table0, TableThen, !IO),
	compute_match_table(Background, DC, Else, [], Table0, TableElse, !IO),
	multi_map__merge(TableThen, !Table), 
	multi_map__merge(TableElse, !Table), 
	(
		process_possible_common_dead_vars(Background, Cont, 
			[TableThen, TableElse], CommonDeadVarsTables, !IO)
	-> 
		list__foldl(multi_map__merge, CommonDeadVarsTables, !Table)
	; 
		true
	),
	compute_match_table(Background, DC, Cont, !Table, !IO).

compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = foreign_proc(_, _, _, _, _, _, _),
	compute_match_table(Background, DC, Cont, !Table, !IO).
compute_match_table(Background, DC, Expr - _Info, Cont, !Table, !IO) :- 
	Expr = par_conj(_),
	compute_match_table(Background, DC, Cont, !Table, !IO).
compute_match_table(_Background, _DC, Expr - _Info, _Cont, !Table, !IO) :- 
	Expr = shorthand(_),
	error("(sr_choice_graphing) shorthand goal should not occur.\n").

%-----------------------------------------------------------------------------%
	% Compute the value of a dead cel with respect to its possible
	% reuses. If reuse is possible, add the specification of the
	% construction where it can be reused to the list of constructions
	% already recorded in the match. 

	% In a conjunction, a dead cell can only be reused in at most one of
	% its direct childs. This means that for each child a new value is
	% computed, and at the end of the conjunction, we will only be
	% interested in the one with the highest value. 

	% PS: note that one could keep them all, but then the elimination of
	% the uninteresting branches is simply postponed to later, hence
	% useless information is caried around. 

:- pred find_best_match_in_conjunction(background_info::in, 
		list(hlds_goal)::in, match::in, match::out) is det. 

find_best_match_in_conjunction(Background, Cont, !Match) :- 
	Match0 = !.Match, 
	list__map(
		pred(G::in, M::out) is det:- 
		    ( find_match_in_goal(Background, G, Match0, M)), 
		Cont, ExclusiveMatches), 
	count_candidates(ExclusiveMatches, Degree), 
	(
		Background ^ strategy ^ selection = lifo,
		(
			% Only select a new candidate if there has not been
			% selected any yet. 
			match_empty(Match0), 
				% If all matches are empty, the unification
				% with FirstNonEmpty will fail, hence, we keep
				% the old (empty) match as the solution for the
				% conjunction.
			list__takewhile(match_empty, ExclusiveMatches, 
				_EmptyVals, [FirstNonEmpty|_])
		-> 
			!:Match = FirstNonEmpty
		; 
			!:Match = Match0
		)
	; 
		Background ^ strategy ^ selection = graph, 
		highest_match_in_list(ExclusiveMatches, !Match)
	),
	!:Match = !.Match ^ match_degree := Degree. 

	% Compute the matches for a dead cell in the context of a
	% disjunction. For each of the branches of the disjunction, a
	% different match may be found. At the end, these matches are
	% merged together into one single match, taking the average of
	% match values to be the value of the final match. 
	% Each construction involved in the reuses is counted as a
	% possibility for reuse, hence is reflected in the degree of the final
	% match description.
:- pred find_match_in_disjunction(background_info::in,
		list(hlds_goal)::in, match::in, match::out) is det.
find_match_in_disjunction(Background, Branches, !Match) :- 
	(
		Branches = []
	-> 	
		true
	; 
		list__map(
			pred(G::in, M::out) is det:- 
			    ( find_match_in_goal(Background, G, !.Match, M)), 
			Branches, BranchMatches), 
		% count_candidates(BranchMatches, Degree), 
		average_match(BranchMatches, !:Match)
	).

:- pred count_candidates(list(match)::in, int::out) is det.
count_candidates(Matches, Degree):- 
	list__foldl(
		pred(Match::in, D0::in, D::out) is det:- 
		    (
			D = D0 + Match ^ match_degree
		    ), 
		Matches, 
		0, Degree). 

	% Compute the value of a dead cell for a specific goal. 
:- pred find_match_in_goal(background_info::in, hlds_goal::in, 
		match::in, match::out) is det.

find_match_in_goal(Background, Goal - _Info, !Match) :- 
	Goal = conj(Goals),
	find_best_match_in_conjunction(Background, Goals, !Match).
find_match_in_goal(_Background, Goal - _Info, !Match) :- 
	Goal = call(_, _, _, _, _, _).
find_match_in_goal(_Background, Goal - _Info, !Match) :- 
	Goal = generic_call(_, _, _, _).
find_match_in_goal(Background, Goal - _Info, !Match) :- 
	Goal = switch(_, _, Cases),
	list__map(
		pred(C::in, G::out) is det:- 
		    ( C = case(_, G) ), 
		Cases, Branches), 
	find_match_in_disjunction(Background, Branches, !Match).
find_match_in_goal(Background, Goal - Info, !Match) :- 
	Goal = unify(_, _, _, Unification, _),
	program_point_init(Info, PP),
	(
		Unification = construct(Var, Cons, Args, _, _, _, _),

			% The construction is still looking for
			% reuse-possibilities... 
		goal_info_get_reuse(Info, ReuseInfo), 
		\+ assigned_reuse(ReuseInfo), 

			% Can fail if the construction can not reuse the
			% deconstructed cell. 
		verify_match(Background, Var, Cons, Args, PP, !Match)

		% Note on the scope: the dead variables automatically belong
		% to the scope of the construction that is treated here,
		% given the way continuations are used. 
%		(
%			goal_info_get_reuse(Info,
%				choice(construct(ReuseVars)))
%		-> 
%			PureReuseVars = set__map(
%					func(RV) = V :-
%					    ( V = RV ^ var ),
%					ReuseVars),
%			( 
%				set__contains(PureReuseVars, 
%					match_get_dead_var(!.Match))
%			-> 
%				true
%			; 
%				ReuseVarsStrings = 
%					list__map(int_to_string, 
%					    list__map(var_to_int, 
%						to_sorted_list(PureReuseVars))),
%				string__append_list([
%					"(sr_choice_graphing) ", 
%					"value_of_dead_cel: ", 
%					"scoping error.\n",
%					"Dead Variable ", 
%					int_to_string(
%					    var_to_int(
%						match_get_dead_var(!.Match))),
%					" is not in the list ", 
%					" of available vars: [", 
%					join_list(", ", ReuseVarsStrings), 
%					"]. \n"], Msg), 
%				error(Msg)
%			)
%		; 
%			string__append_list([
%				"(sr_choice_graphing) ", 
%				"value_of_dead_cel: ", 
%				"reuse for construction that didn't ", 
%				"have any candidates for reuse."], Msg), 
%			error(Msg)
%		)
	-> 
		true
	; 
		true
	). 

:- pred assigned_reuse(reuse_goal_info::in) is semidet. 
assigned_reuse(potential_reuse(_)). 
assigned_reuse(reuse(_)). 
		
find_match_in_goal(Background, Goal - _Info, !Match) :- 
	Goal = disj(Branches),
	find_match_in_disjunction(Background, Branches, !Match).
find_match_in_goal(Background, Goal - _Info, !Match) :- 
	Goal = not(NegatedGoal),
	find_match_in_goal(Background, NegatedGoal, !Match).
find_match_in_goal(Background, Goal - _Info, !Match) :- 
	Goal = some(_, _, SGoal),
	find_match_in_goal(Background, SGoal, !Match).
find_match_in_goal(Background, Goal - _Info, !Match) :- 
	Match0 = !.Match, 
	Goal = if_then_else(_, If, Then, Else),
	find_best_match_in_conjunction(Background, [If, Then], !Match),
	find_match_in_goal(Background, Else, Match0, Match2), 
	average_match([!.Match, Match2], !:Match).
find_match_in_goal(_Background, Goal - _Info, !Match) :- 
	Goal = foreign_proc(_, _, _, _, _, _, _).
find_match_in_goal(_Background, Goal - _Info, !Match) :- 
	Goal = par_conj(_).
find_match_in_goal(_Background, Goal - _Info, !Match) :- 
	Goal = shorthand(_), 
	error("(sr_choice_graphing) shorthand goal should not occur.\n").
	

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

:- pred verify_match(background_info::in, prog_var::in, cons_id::in, 
		list(prog_var)::in, program_point::in, 
		match::in, match::out) is semidet.
verify_match(Background, NewVar, NewCons, NewArgs, PP, Match0, Match) :- 
	DeconSpecs = Match0 ^ decon_specs, 
	list__map(compute_reuse_type(Background, NewVar, NewCons, NewArgs),
		DeconSpecs, MaybeReuseTypes),
	glb_reuse_types(MaybeReuseTypes, yes(ReuseType)), % can fail
	ConSpec = con(PP, ReuseType),
	match_add_construction(ConSpec, Match0, Match).

:- pred glb_reuse_types(list(maybe(reuse_type))::in, 
		maybe(reuse_type)::out) is det.

glb_reuse_types(List, MaybeR) :- 
	(
		List = [First|Rest], 
		list__foldl(glb_reuse_types_2, Rest, First, MaybeR)
	;
		List = [], 
		error("(sr_choice_graphing) no reuse types.\n")
	).

:- pred glb_reuse_types_2(maybe(reuse_type)::in, maybe(reuse_type)::in, 
		maybe(reuse_type)::out) is det.

glb_reuse_types_2(MaybeR1, MaybeR2, MaybeR) :- 
	(
		MaybeR1 = yes(R1), 
		MaybeR2 = yes(R2)
	->
		R1 = reuse_type(SameCons1, Fields1, V1),
		R2 = reuse_type(SameCons2, Fields2, V2),
		R = reuse_type(SameCons1 `and` SameCons2, 
			Fields1 `ands` Fields2, 
			(V1 + V2) / 2.00 ), 
		MaybeR = yes(R)
	; 
		MaybeR = no
	). 

:- func ands(list(bool), list(bool)) = list(bool). 
ands(L1, L2) = L :- 
	(
		length(L1) =< length(L2)
	-> 
		L1b = L1, 
		L2b = take_upto(length(L1), L2)
	;
		L1b = take_upto(length(L2), L1),
		L2b = L2
	),
	L = list__map_corresponding(bool__and, L1b, L2b).
	


:- func alfa_value = int is det.
:- func gamma_value = int is det.
:- func beta_value = int is det.
alfa_value = 5. 
gamma_value = 1.
beta_value = 1. 

:- pred compute_reuse_type(background_info::in, prog_var::in, cons_id::in,
		list(prog_var)::in, deconstruction_spec::in, 
		maybe(reuse_type)::out) is det.
	
compute_reuse_type(Background, NewVar, NewCons, NewCellArgs, DeconSpec, 
			MaybeReuseType) :- 
	DeconSpec = decon(DeadVar, _, DeadCons, DeadCellArgs, _),

	Constraint = Background ^ strategy ^ constraint, 
	ModuleInfo = Background ^ module_info, 
	Vartypes   = Background ^ vartypes, 
	NewArity = list__length(NewCellArgs), 
	DeadArity = list__length(DeadCellArgs), 
	(
		% 1. if the new cell has arity zero, it shouldn't be allowed to
		% reuse anything. 
		NewArity \= 0, 

		% 2. the new cell may not be bigger than the dead cell
		NewArity =< DeadArity,

		% 3. verify the reuse constraint, either same cons, or within a
		% certain arity difference: 
		DiffArity = DeadArity - NewArity, 
		( NewCons = DeadCons -> SameCons = yes ; SameCons = no), 
		( 
			Constraint = within_n_cells_difference(N),
			DiffArity =< N
		; 
			Constraint = same_cons_id, 
			SameCons = yes
		),

		% 4. if all the checks are satisfied, determine the number of
		% fields that would not need an update if the construction
		% would use the deconstructed cell: 
		has_secondary_tag(ModuleInfo, Vartypes, NewVar, 
			NewCons, SecTag), 
		has_secondary_tag(ModuleInfo, Vartypes, DeadVar, 
			DeadCons, DeadSecTag), 
		ReuseFields = already_correct_fields(SecTag, NewCellArgs, 
				DeadSecTag - DeadCellArgs),
		UpToDateFields = list__length(
				list__delete_all(ReuseFields, no)),
		%
		% Finally, compute the value of this reuse-configuration.
		( SameCons = yes -> SameConsV = 0; SameConsV = 1),
		Weight = ( (alfa_value + gamma_value) * NewArity + beta_value
				- gamma_value * (NewArity - UpToDateFields)
				- beta_value * SameConsV
				- alfa_value * DiffArity ),
		Weight > 0, 
		ReuseType = reuse_type(SameCons, ReuseFields, float(Weight))
	-> 
		MaybeReuseType = yes(ReuseType)
	; 
		MaybeReuseType = no
	). 

%-----------------------------------------------------------------------------%

	% Once a dead cell is selected from the table, all the constructions
	% involved with reusing this dead cell have to be marked. 
:- pred annotate_reuses(match::in, hlds_goal::in, 
		hlds_goal::out) is det.

annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = conj(Goals0),
	list__map(annotate_reuses(Match), Goals0, Goals),
	E = conj(Goals), 
	I = I0.
annotate_reuses(_Match, E0 - I0, E - I):- 
	E0 = call(_,_,_,_,_,_),
	E = E0, 
	I = I0.
annotate_reuses(_Match, E0 - I0, E - I):- 
	E0 = generic_call(_,_,_,_),
	E = E0, 
	I = I0. 
annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = switch(V, CF, Cases0),
	list__map(
		pred(C0::in, C::out) is det:- 
		    ( C0 = case(Cons, Goal0),
		      annotate_reuses(Match, Goal0, Goal), 
		      C = case(Cons, Goal)
		    ), 
		Cases0, Cases),
	E = switch(V, CF, Cases), 
	I = I0. 

:- pred program_point_equality(program_point::in, program_point::in) 
		is semidet.
program_point_equality(C1, C2):-
	C1 = pp(Context, Path), 
	C2 = pp(Context, Path). 

annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = unify(_Var, _Rhs, _Mode, _Unification0, _Context),
	program_point_init(I0, PP),
	(
		P = (pred(D::in) is semidet :- 
			program_point_equality(D ^ decon_pp, PP)), 
		list__filter(P, Match ^ decon_specs, [_DeconSpec])
	-> 
		% then this must be a deconstruction
		goal_info_set_reuse(potential_reuse(cell_died), I0, I),
		E = E0
	;
		P = (pred(C::in) is semidet :- 
			program_point_equality(C ^ con_pp, PP)), 
		list__filter(P, Match ^ con_specs, [ConSpec])
	-> 
		ConsIds = match_get_cons_ids(Match), 
		Condition = match_get_condition(Match), 
		ReuseFields = ConSpec ^ con_reuse ^ reuse_fields,
		(
			Condition = always, 
			Conditional = no
		; 
			Condition = condition(_,_,_),
			Conditional = yes
		),
		CellReused = cell_reused(match_get_dead_var(Match),
				Conditional, ConsIds, ReuseFields),
		(
			Conditional = yes, 
			KindReuse = potential_reuse(CellReused)
		; 
			Conditional = no, 
			% If the reuse is unconditional, then reuse is not just
			% potentially possible, but alwasy possible, so
			% skipping the potential phase is perfectly safe.  (see
			% also sr_indirect__call_verify_reuse)
			KindReuse = reuse(CellReused)
		), 	
		goal_info_set_reuse(KindReuse, I0, I), 
		E = E0
	; 
		E = E0, 
		I = I0
	).

annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = disj(Goals0), 
	list__map(annotate_reuses(Match), Goals0, Goals),
	E = disj(Goals), 
	I = I0. 
annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = not(Goal0), 
	annotate_reuses(Match, Goal0, Goal), 
	E = not(Goal),
	I = I0. 
annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = some(Vars, CanRemove, Goal0), 
	annotate_reuses(Match, Goal0, Goal), 
	E = some(Vars, CanRemove, Goal), 
	I = I0. 
annotate_reuses(Match, E0 - I0, E - I):- 
	E0 = if_then_else(V, If0, Then0, Else0), 
	annotate_reuses(Match, If0, If),
	annotate_reuses(Match, Then0, Then),
	annotate_reuses(Match, Else0, Else),
	E = if_then_else(V, If, Then, Else), 
	I0 = I. 
annotate_reuses(_Match, E0 - I0, E - I):- 
	E0 = foreign_proc(_, _, _, _, _, _, _), 
	E = E0, 
	I = I0. 
annotate_reuses(_Match, E0 - I0, E - I):- 
	E0 = par_conj(_), 
	E = E0, 
	I = I0.
annotate_reuses(_Match, E0 - _I0, _E - _I):- 
	E0 = shorthand(_),
	error("(sr_choice_graphing) shorthand goal should not occur.\n").

%-----------------------------------------------------------------------------%
% Genaral manipulations on values, value, etc.. 
%-----------------------------------------------------------------------------%

:- pred highest_match_degree_ratio(match_table::in, match::out) is semidet.
highest_match_degree_ratio(MatchTable, Match):-
	multi_map__values(MatchTable, Matches), 
	list__sort(reverse_compare_matches_value_degree, 
			Matches, Sorted), 
	(
		Sorted = [Match|_],
		\+ match_empty(Match)
	; 
		Sorted = [], 
		error("sr_choice_graphing: empty multi_map.\n")
	). 

:- pred compare_matches_value_degree(match::in, match::in, 
		comparison_result::out) is det. 
compare_matches_value_degree(Match1, Match2, Result) :- 
	match_value_degree(Match1, V1), 
	match_value_degree(Match2, V2), 
	compare(Result, V1, V2). 
:- pred reverse_compare_matches_value_degree(match::in, match::in,
		comparison_result::out) is det. 
reverse_compare_matches_value_degree(Match1, Match2, Result) :- 
	compare_matches_value_degree(Match2, Match1, Result). 

:- pred match_value_degree(match::in, float::out) is det.
match_value_degree(Match, V) :- 
	(
		Match ^ match_value \= 0.00
	-> 
		V = Match ^ match_value / float(Match ^ match_degree)
	;
		V = 0.00
	).

:- pred compare_matches_value(match::in, match::in, 
		comparison_result::out) is det.
compare_matches_value(Match1, Match2, Result) :- 
	V1 = Match1 ^ match_value,
	V2 = Match2 ^ match_value,
	compare(Result, V1, V2).
:- pred reverse_compare_matches_value(match::in, match::in, 
		comparison_result::out) is det.
reverse_compare_matches_value(Match1, Match2, Result) :- 
	compare_matches_value(Match2, Match1, Result). 
	
:- pred match_allows_reuse(match::in) is semidet. 
match_allows_reuse(Match) :- 
	Constructions = Match ^ con_specs, 
	Value = Match ^ match_value,  
	Constructions = [_|_], 
	Value > 0.00.
	
:- pred highest_match_in_list(list(match)::in, match::in, match::out) is det.
highest_match_in_list(Matches, Match0, Match) :- 
	list__sort(reverse_compare_matches_value, [Match0 | Matches], Sorted), 
	(
		Sorted = [Match|_]
	;
		Sorted = [], 
		error("sr_choice_graphing: list_sort returned empty list.\n")
	).

	% Given a list of matches concerning the same (list of) deconstruction,
	% compute the average reuse value of that deconstruction. This means
	% merging all the constructions together into one list, and using the
	% average value of the reuses of each of the matches. The final degree
	% of the match is set to the sum of all degrees. 
:- pred average_match(list(match)::in, match::out) is det.
average_match(List, AverageMatch):- 
	(
		List = [First|Rest], 
		list__length(List, Length), 
		P = (pred(M::in, Acc0::in, Acc::out) is det :- 
			DeconSpecs = Acc0 ^ decon_specs, 
			ConSpecs = append(Acc0 ^ con_specs, M ^ con_specs),
			Val = Acc0 ^ match_value + M ^ match_value, 
			Deg = Acc0 ^ match_degree + M ^ match_degree, 
			Acc = match(DeconSpecs, ConSpecs, Val, Deg)),
		list__foldl(P, Rest, First, Match0), 
		AverageMatch = (Match0 ^ match_value := 
				(Match0 ^ match_value / float(Length)))
	; 
		List = [], 
		require__error("(sr_choice_graphing) average_match: empty list.\n")
	). 
			
%-----------------------------------------------------------------------------%
	% After the selection pass, a final pass is performed to annotate all
	% the deconstructions in which a cell dies unconditionally, and which
	% has not yet been involved in a reuse. 

:- pred check_cgc(dead_cell_table::in, 
		hlds_goal::in, hlds_goal::out) is det.

check_cgc(DC, G0 - I0, G - I):- 
	G0 = conj(Goals0),
	list__map(check_cgc(DC), Goals0, Goals),
	G  = conj(Goals),
	I  = I0.
check_cgc(_DC, G0 - I0, G - I):- 
	G0 = call( _, _, _, _, _, _),
	G  = G0,
	I  = I0.
check_cgc(_DC, G0 - I0, G - I):- 
	G0 = generic_call( _, _, _, _),
	G  = G0, 
	I  = I0.
check_cgc(DC, G0 - I0, G - I):- 
	G0 = switch(A, B, Cases0),
	list__map(
		pred(C0::in, C::out) is det:-
		    ( C0 = case(Cons, Goal0), 
		      check_cgc(DC, Goal0, Goal), 
		      C = case(Cons, Goal) ), 
		Cases0, Cases), 
	G  = switch(A, B, Cases), 
	I  = I0.
check_cgc(DC, G0 - I0, G - I):- 
	G0 = unify(A, B, C, Unification0, D),
	program_point_init(I0, PP), 
	(
		Unification0 = deconstruct(A1, B1, C1, D1, E1, _), 
		Condition = dead_cell_table_search(PP, DC), 
		Condition = always
	-> 
		Unification = deconstruct(A1, B1, C1, D1, E1, yes),
		G = unify(A, B, C, Unification, D), 
		ReuseInfo = potential_reuse(cell_died),
		goal_info_set_reuse(ReuseInfo, I0, I)
	;
		G = G0,
		I = I0
	).

check_cgc(DC, G0 - I0, G - I):- 
	G0 = disj(Goals0),
	list__map(check_cgc(DC), Goals0, Goals), 
	G  = disj(Goals), 
	I  = I0.
check_cgc(DC, G0 - I0, G - I):- 
	G0 = not(Goal0),
	check_cgc(DC, Goal0, Goal), 
	G  = not(Goal), 
	I  = I0.
check_cgc(DC, G0 - I0, G - I):- 
	G0 = some(A, B, Goal0),
	check_cgc(DC, Goal0, Goal), 
	G  = some(A, B, Goal), 
	I  = I0.
check_cgc(DC, G0 - I0, G - I):- 
	G0 = if_then_else(A, If0, Then0, Else0),
	check_cgc(DC, If0, If), 
	check_cgc(DC, Then0, Then), 
	check_cgc(DC, Else0, Else), 
	G  = if_then_else(A, If, Then, Else),  
	I  = I0.
check_cgc(_DC, G0 - I0, G - I):- 
	G0 = foreign_proc(_, _, _, _, _, _, _),
	G  = G0,
	I  = I0.
check_cgc(_DC, G0 - I0, G - I):- 
	G0 = par_conj(_),
	G  = G0,
	I  = I0.
check_cgc(_DC, G0 - _I0, _G - _I):- 
	G0 = shorthand( _),
	error("(sr_choice_graphing) check_cgc: shorthand.\n").

%-----------------------------------------------------------------------------%

:- pred deconstruction_spec_init(prog_var::in, program_point::in, cons_id::in, 
		list(prog_var)::in, reuse_condition::in, 
		deconstruction_spec::out) is det.
deconstruction_spec_init(Var, PP, ConsId, Args, Cond, DS) :- 
	DS = decon(Var, PP, ConsId, Args, Cond). 

:- pred match_init(list(deconstruction_spec)::in, match::out) is det.
match_init(DS, match(DS, [], 0.00, 0)).

:- pred match_empty(match::in) is semidet.
match_empty(match(_, [], _, _)).

:- func match_get_dead_var(match) = prog_var. 
match_get_dead_var(Match) = Var :- 
	GetVar = (pred(D::in, V::out) is det :- 
			V = D ^ decon_var), 
	list__map(GetVar, Match ^ decon_specs, DeadVars0), 
	list__remove_dups(DeadVars0, DeadVars), 
	(
		DeadVars = [Var|Rest], 
		(
			Rest = [_|_]
		-> 
			error("(sr_choice_graphing) too many dead vars.\n")
		;
			true
		)
	; 
		DeadVars = [], 
		error("(sr_choice_graphing) too few dead vars.\n")
	).

:- func match_get_cons_ids(match) = list(cons_id).
match_get_cons_ids(Match) = ConsIds :- 
	GetConsId = (pred(D::in, C::out) is det :- 
			C = D ^ decon_cons_id), 
	list__map(GetConsId, Match ^ decon_specs, ConsIds). 

:- func match_get_condition(match) = reuse_condition.
match_get_condition(Match) = Condition :- 
	GetCond = (pred(D::in, C::out) is det :- 
			C = D ^ decon_conds),
	list__map(GetCond, Match ^ decon_specs, Conditions), 
	(
		Conditions = [First | Rest], 
		list__foldl(reuse_condition_merge, Rest, First, Condition)
	; 
		Conditions = [], 
		error("(sr_choice_graphing) no reuse conditions.\n")
	). 

:- pred match_add_construction(construction_spec::in, match::in, 
		match::out) is det.
match_add_construction(ConSpec, Match0, Match) :- 
	Match0 = match(DeconSpecs0, ConSpecs0, Value0, Degree0), 
	ConSpecs = [ConSpec | ConSpecs0],
	Degree = Degree0 + 1, 
	FDegree0 = float(Degree0), 
	FDegree = float(Degree), 
	Value = (Value0 * FDegree0 + ConSpec ^ con_reuse ^ tmp_value) / FDegree,
	Match = match(DeconSpecs0, ConSpecs, Value, Degree).
