%-----------------------------------------------------------------------------%
% Copyright (C) 1997-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% file: lp_rational.m
% main authors: conway,	vjteag.
%
% This module implements:
%
% A linear optimizer that finds an optimal solution to a set of 
% linear [in]equalities with respect to some objective function. It does 
% this using the simplex method.
%
% 	The form of an [in]equation is
% 		a1.x1 + a2.x2 + ... + an.xn {=<,=,>=} b
% 	where all the numbers are rats, a variable xn may occur multiple
% 	times in an equation (or the objective function) - the solver simplifies
% 	all the inequations.
% 	By defaut, there is an additional constraint on each of the `xn's:
%		xn >= 0
% 	If you want xn to take on any value, you can include it in the list
% 	of URS (UnRestricted in Sign) variables.
%
% 	The objective function is simply a weighted sum of the variables.
%
% 	The `x's are represented by `term__var's. The varset from which
% 	they are allocated is passed to the solver because it needs to
% 	introduce new variables as part of the solving algorithm.
%
%
% Fourier-Motzkin elimination, which takes a polyhedron represented by 
% a list of inequations (represented in the same way as in the optimizer) 
% and projects it onto a subset of the variables contained in the inequations. 
%
% 
% A convex hull algorithm, which takes a list of polyhedrons (represented
% by lists of inequations), and computes the smallest convex set which is 
% a superset of all of them. 
% For details of the algorithm, see Benoy and King.
%
%
% A test for entailment of one constraint (a single inequality) by a
% conjunction of other inequalities (a polyhedron).  This uses the optimizer 
% to find the point on the polyhedron closest to the boundary of the 
% constraint, then checks whether it is on the correct side of the boundary.
% It assumes that all variables are non-negative.
%
% A widening algorithm, which takes two polyhedra and retains only the
% inequalities in the first polyhedron which are entailed by the second.
% 
%------------------------------------------------------------------------------%
:- module lp_rational.

:- interface.

%------------------------------------------------------------------------------%

:- import_module io, rat, list, map, std_util, term, varset.

:- type lp_var		==	var.
:- type lp_varset	==	varset.

:- type coeff 		== 	pair(lp_var, rat).

:- type equation
	--->	eqn(list(coeff), operator, rat).

:- type operator
	--->	(=<) ; (=) ; (>=) .

:- type equations	==	list(equation).

:- type objective	==	list(coeff).

:- type direction
	--->	max ; min .

:- type lp_rational__result
	--->	unbounded
	;	inconsistent
	;	satisfiable(rat, map(lp_var, rat))
	.

:- type vector ---> pair(map(lp_var, rat), rat).

% XX Should that be:  :- type vector == pair(map(lp_var, rat), rat).
%    Maybe we can change this later.

:- type matrix == list(vector).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

	% lp_solve(Inequations, MaxOrMin, Objective, Varset, URSVars,
	%		Result)
	% maximize (or minimize - depending on `MaxOrMin') `Objective'
	% subject to the constraints `Inequations'. The variables in
	% the objective and inequations are from `Varset' which is passed
	% so that the solver can allocate fresh variables as required.
	% URSVars is the list of variable that are unrestricted in sign.
	% lp_solve binds Result to `unbounded' if the objective
	% function is not bounded by the constraints, to 'inconsistent'
	% if the given constraints are inconsistent, or to 
	% `satisfiable(ObjVal, MapFromObjVarsToVals)'.

:- pred lp_solve(equations, direction, objective, lp_varset, list(lp_var),
		lp_rational__result).
:- mode lp_solve(in, in, in, in, in, out) is det.


	% project(Equations0, Variables, Equations) takes a list of 
	% inequalities Equations0 and eliminates the variables in the 
	% input list Variables, using Fourier-Motzkin elimination. 
	% This is equivalent to projecting a polyhedron (represented
	% by the list of constraints Equations0) onto the subspace 
	% represented by those variables that are not in the list. 
	% Binds Equations to the projection of the polygon.

:- pred project(equations, list(lp_var), equations).
:- mode project(in, in, out) is det.


	% convex_hull(Polys, Conv_hull, Vars0, Vars):  takes a list of 
	% polyhedra Polys (where each polyhedron is represented as a list 
	% of constraints) and computes the smallest convex set Conv_hull 
	% which is a superset of all of them.  For details of the algorithm, 
	% see Benoy and King.

:- pred convex_hull(list(equations), equations, lp_varset, lp_varset).
:- mode convex_hull(in, out, in, out) is det.


	% widen(Cs1, Cs2, Cs, Vars): Relaxes the constraints Cs1 by selecting
	% those constraints from Cs1 which are implied by Cs2.  Uses entails
	% to check this.  This is equivalent to taking a polyhedron Cs1
	% (represented as a list of constraints) and removing faces 
	% (constraints) to form another polyhedron Cs, according to the 
	% rules that the smallest number of contraints should be removed and 
	% that Cs must contain (be a superset of) the second polygon Cs2. 
	% Note that this is not commutative for Cs1, Cs2.

:- pred widen(equations, equations, lp_varset, equations).
:- mode widen(in, in, in, out) is det.


	% entailed(C, Cs, Vars): Determines whether the constraint C is
	% implied by the set of constraints Cs. 
	% Uses the simplex method to find the point P satisfying Cs
	% which maximises (if C contains '=<') or minimises (if C 
	% contains '>=') a function parallel to C.  Then tests whether P 
	% satisfies C.
	% This assumes that all the variables are non-negative. 

:- pred entailed(equation, equations, lp_varset).
:- mode entailed(in, in, in) is semidet.


	% is_false(Eqn): returns true if Eqn is trivially false, that is if
	% it has all zero coefficients but the constant term causes it to be
	% false (for example 0 >= 5).  

:- pred is_false(equation).
:- mode is_false(in) is semidet.


	% false_eqn(Eqn): creates an equation that is trivially false (0 =< -1).

:- pred false_eqn(equation).
:- mode false_eqn(out) is det.


	% eqns_to_vectors(Equations, Vectors):  converts a list of equations
	% containing the '=<' operator into a vector, i.e. a map from variables
	% to coefficients (rationals) together with a constant (rational).
	% It is an error if any of the equations has an operator other than
	% '=<'

:- pred eqns_to_vectors(equations, list(vector)).
:- mode eqns_to_vectors(in, out) is det.

:- pred vectors_to_eqns(list(vector), equations).
:- mode vectors_to_eqns(in, out) is det.

	% fm_standardize_equations(Input_eqns, Standardized eqns):  ensures all 
	% inequations are of the form a1x1 + ... + anxn =< C.  Inequalities 
	% containing >= are multiplied through by -1, and equations are 
	% converted into two inequations of the form 
	% a1x1 + ... + anxn =< C,  -a1x1 - ... - anxn =< -C. 

:- pred fm_standardize_equations(equations, equations).
:- mode fm_standardize_equations(in, out) is det.


	% Converts a vector into a parallel one where the coefficient of lp_var
	% is plus or minus one.  That is, divides the vector through by the
	% absolute value of the coefficient of lp_var.

:- pred normalize_vector(vector, lp_var, vector).
:- mode normalize_vector(in, in, out) is det.


	% Print equations/vectors in a human-readable format.

:- pred write_vectors(matrix, io__state, io__state).
:- mode write_vectors(in, di, uo) is det.

:- pred write_equations(equations, io__state, io__state).
:- mode write_equations(in, di, uo) is det.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module bool, int, io, require, set, string, array.

:- type lp_info
	---> lp(
		lp_varset,
		map(lp_var, pair(lp_var)),	% map from variables with URS to
					% the corresponding pair of variables
					% that represent that variable in
					% the standard form (x = x' - x'',
					% x', x'' >= 0).
		list(lp_var),		% slack variables
		list(lp_var)		% artificial variables
	).

is_false(eqn([], (>=), Const)) :-
	Const > zero.
is_false(eqn([], (=<), Const)) :-
	Const < zero.
is_false(eqn([], (=), Const)) :-
	not (Const = zero).

false_eqn(eqn([], (=<), rat(-1,1))).
	

lp_solve(Eqns, Dir, Obj, Varset, URSVars, Result) :-
	lp_info_init(Varset, URSVars, Info0),
	lp_solve2(Eqns, Dir, Obj, Result, Info0, _).

%
% lp_solve2(Eqns, Dir, Obj, Res, LPInfo0, LPInfo) takes a list
% of inequations `Eqns', a direction for optimization `Dir', an objective
% function `Obj' and an lp_info structure `LPInfo0'.
% See inline comments for details on the algorithm.
%

:- pred lp_solve2(equations, direction, objective, lp_rational__result,
		lp_info, lp_info).
:- mode lp_solve2(in, in, in, out, in, out) is det.
lp_solve2(Eqns0, Dir, Obj0, Result, Info0, Info) :-
		% simplify the inequations and convert them
		% to standard form by introducing slack/excess/
		% artificial variables. We also expand URS variables
		% by replacing them with the difference of two
		% fresh variables.
	standardize_equations(Eqns0, Eqns, Info0, Info1),

		% If we're maximizing the objective function then we need
		% to negate all the coefficients in the objective.
	(
		Dir = max,
		negate_equation(eqn(Obj0, (=), zero), eqn(Obj1, _, _))
	;
		Dir = min,
		Obj1 = Obj0
	),
	simplify_coeffs(Obj1, Obj2),

	get_urs_vars(URS, Info1, _),
	expand_urs_vars(Obj2, URS, Obj),
	list__length(Eqns, Rows),
	collect_vars(Eqns, Obj, Vars),
	set__to_sorted_list(Vars, VarList),
	list__length(VarList, Cols),
	map__init(VarNums0),
	number_vars(VarList, 0, VarNums0, VarNums),
	get_art_vars(ArtVars, Info1, Info),
	init_tableau(Rows, Cols, VarNums, URS, Tableau0),
	insert_equations(Eqns, 1, Cols, VarNums,
		Tableau0, Tableau1),
	(
		ArtVars = [_|_],
		% There are one or more artificial variables, so we use
		% the two-phase method for solving the system.
		two_phase(Obj0, Obj, ArtVars, VarNums, Tableau1, Result0)
	 ;
		ArtVars = [],
		one_phase(Obj0, Obj, VarNums, Tableau1, Result0)
	),
	(
		Dir = max,
		Result = Result0
	;
		Dir = min,
		(
			Result0 = unbounded,
			Result = Result0
		;
			Result0 = inconsistent,
			Result = Result0
		;
			Result0 = satisfiable(NOptVal, OptCoffs),
			OptVal is -NOptVal,
			Result = satisfiable(OptVal, OptCoffs)
		)
	).

%------------------------------------------------------------------------------%

:- pred one_phase(list(coeff), list(coeff), map(lp_var, int), tableau,
							lp_rational__result).
:- mode one_phase(in, in, in, in, out) is det.
one_phase(Obj0, Obj, VarNums, Tableau0, Result) :-
	insert_coeffs(Obj, 0, VarNums, Tableau0, Tableau1),
	GetObjVar = lambda([V::out] is nondet, (
		list__member(X, Obj0),
		X = V - _Cof
	)),
	solutions(GetObjVar, ObjVars),
	optimize(ObjVars, Tableau1, _, Result).
%------------------------------------------------------------------------------%

:- pred two_phase(list(coeff), list(coeff), list(lp_var), map(lp_var, int),
		tableau, lp_rational__result).
:- mode two_phase(in, in, in, in, in, out) is det.
two_phase(Obj0, Obj, ArtVars, VarNums, Tableau0, Result) :-

		% Do phase 1:
		%	minimize the sum of the artificial variables
	construct_art_objective(ArtVars, ArtObj),
	insert_coeffs(ArtObj, 0, VarNums, Tableau0, Tableau1a),
	ensure_zero_obj_coeffs(ArtVars, Tableau1a, Tableau1b),
	optimize(ArtVars, Tableau1b, Tableau1c, Res0),
	(
		Res0 = unbounded,
		Result = unbounded

	;
		Res0 = inconsistent,
		Result = inconsistent
	;
		Res0 = satisfiable(Val, _ArtRes),
		( Val \= zero ->
			Result = inconsistent
		;
			fix_basis_and_rem_cols(ArtVars, Tableau1c, Tableau2),
				% Do phase 2:
				%	insert the real objective,
				%	zero the objective coefficients of the
				%	basis variables,
				%	optimize the objective.
			insert_coeffs(Obj, 0, VarNums, Tableau2, Tableau3),
			get_basis_vars(Tableau3, BasisVars),
			ensure_zero_obj_coeffs(BasisVars,
					Tableau3, Tableau4),
			GetObjVar = lambda([V::out] is nondet, (
				list__member(X, Obj0),
				X = V - _Cof
			)),
			solutions(GetObjVar, ObjVars),
			optimize(ObjVars, Tableau4, _, Result)
		)
	).

%------------------------------------------------------------------------------%

:- pred construct_art_objective(list(lp_var), list(coeff)).
:- mode construct_art_objective(in, out) is det.

construct_art_objective([], []).
construct_art_objective([V|Vs], [V - (one)|Rest]) :-
	construct_art_objective(Vs, Rest).

%------------------------------------------------------------------------------%

:- pred standardize_equations(equations, equations, lp_info, lp_info).
:- mode standardize_equations(in, out, in, out) is det.

standardize_equations(Eqns0, Eqns) -->
	list__map_foldl(standardize_equation, Eqns0, Eqns).

	% standardize_equation peforms the following operations on an
	% equation:
	%	- ensures the constant is >= 0 (multiplying by -1 if
	%		necessary)
	%	- introduces slack, excess and artificial variables
	%	- replace the URS variables with their corresponding
	%		difference pair
:- pred standardize_equation(equation, equation, lp_info, lp_info).
:- mode standardize_equation(in, out, in, out) is det.

standardize_equation(Eqn0, Eqn) -->
	{ Eqn0 = eqn(Coeffs0, (=<), Const0) },
	( { Const0 < zero } ->
		{ negate_equation(Eqn0, Eqn1) },
		standardize_equation(Eqn1, Eqn) 
	;
		new_slack_var(Var),
		{ Coeffs = [Var - one|Coeffs0] },
		{ simplify(eqn(Coeffs, (=<), Const0), Eqn1) },
		get_urs_vars(URS),
		{ expand_urs_vars_e(Eqn1, URS, Eqn) }
	).

standardize_equation(Eqn0, Eqn) -->
	{ Eqn0 = eqn(Coeffs0, (=), Const0) },
	( { Const0 < zero } ->
		{ negate_equation(Eqn0, Eqn1) },
		standardize_equation(Eqn1, Eqn)
	;
		new_art_var(Var),
		{ Coeffs = [Var - one|Coeffs0] },
		{ simplify(eqn(Coeffs, (=<), Const0), Eqn1) },
		get_urs_vars(URS),
		{ expand_urs_vars_e(Eqn1, URS, Eqn) }
	).

standardize_equation(Eqn0, Eqn) -->
	{ Eqn0 = eqn(Coeffs0, (>=), Const0) },
	( { Const0 < zero } ->
		{ negate_equation(Eqn0, Eqn1) },
		standardize_equation(Eqn1, Eqn)
	;
		new_slack_var(SVar),
		new_art_var(AVar),
		{ Coeffs = [SVar - (-one), AVar - (one)|Coeffs0] },
		{ simplify(eqn(Coeffs, (>=), Const0), Eqn1) },
		get_urs_vars(URS),
		{ expand_urs_vars_e(Eqn1, URS, Eqn) }
	).

:- pred negate_equation(equation, equation).
:- mode negate_equation(in, out) is det.

negate_equation(eqn(Coeffs0, Op0, Const0), eqn(Coeffs, Op, Const)) :-
	(
		Op0 = (=<), Op = (>=)
	;
		Op0 = (=), Op = (=)
	;
		Op0 = (>=), Op = (=<)
	),
	Neg = lambda([Pair0::in, Pair::out] is det, (
		Pair0 = V - X0,
		X is -X0,
		Pair = V - X
	)),
	list__map(Neg, Coeffs0, Coeffs),
	Const is -Const0.

:- pred simplify(equation, equation).
:- mode simplify(in, out) is det.

simplify(eqn(Coeffs0, Op, Const), eqn(Coeffs, Op, Const)) :-
	simplify_coeffs(Coeffs0, Coeffs).

:- pred simplify_coeffs(list(coeff), list(coeff)).
:- mode simplify_coeffs(in, out) is det.

simplify_coeffs(Coeffs0, Coeffs) :-
	map__init(CoeffMap0),
	AddCoeff = lambda([Pair::in, Map0::in, Map::out] is det, (
		Pair = Var - Coeff,
		add_var(Map0, Var, Coeff, Map)
	)),
	list__foldl(AddCoeff, Coeffs0, CoeffMap0, CoeffMap),
	map__to_assoc_list(CoeffMap, Coeffs).

:- pred add_var(map(lp_var, rat), lp_var, rat, map(lp_var, rat)).
:- mode add_var(in, in, in, out) is det.

add_var(Map0, Var, Coeff, Map) :-
	( map__search(Map0, Var, Acc0) ->
		Acc1 = Acc0
	;
		Acc1 = zero
	),
	Acc is Acc1 + Coeff,
	map__set(Map0, Var, Acc, Map).

:- pred expand_urs_vars_e(equation, map(lp_var, pair(lp_var)), equation).
:- mode expand_urs_vars_e(in, in, out) is det.

expand_urs_vars_e(eqn(Coeffs0, Op, Const), Vars, eqn(Coeffs, Op, Const)) :-
	expand_urs_vars(Coeffs0, Vars, Coeffs).

:- pred expand_urs_vars(list(coeff), map(lp_var, pair(lp_var)), list(coeff)).
:- mode expand_urs_vars(in, in, out) is det.

expand_urs_vars(Coeffs0, Vars, Coeffs) :-
	expand_urs_vars(Coeffs0, Vars, [], Coeffs1),
	list__reverse(Coeffs1, Coeffs).

:- pred expand_urs_vars(list(coeff), map(lp_var, pair(lp_var)),
		list(coeff), list(coeff)).
:- mode expand_urs_vars(in, in, in, out) is det.

expand_urs_vars([], _Vars, Coeffs, Coeffs).
expand_urs_vars([Var - Coeff|Rest], Vars, Coeffs0, Coeffs) :-
	( map__search(Vars, Var, PVar - NVar) ->
		NCoeff is -Coeff,
		Coeffs1 = [NVar - NCoeff, PVar - Coeff|Coeffs0]
	;
		Coeffs1 = [Var - Coeff|Coeffs0]
	),
	expand_urs_vars(Rest, Vars, Coeffs1, Coeffs).

%------------------------------------------------------------------------------%

:- pred collect_vars(equations, objective, set(lp_var)).
:- mode collect_vars(in, in, out) is det.

collect_vars(Eqns, Obj, Vars) :-
	GetVar = lambda([Var::out] is nondet, (
		(
			list__member(Eqn, Eqns),
			Eqn = eqn(Coeffs, _, _),
			list__member(Pair, Coeffs),
			Pair = Var - _
		;
			list__member(Pair, Obj),
			Pair = Var - _
		)
	)),
	solutions(GetVar, VarList),
	set__list_to_set(VarList, Vars).

:- pred number_vars(list(lp_var), int, map(lp_var, int), map(lp_var, int)).
:- mode number_vars(in, in, in, out) is det.

number_vars([], _, VarNums, VarNums).
number_vars([Var|Vars], N, VarNums0, VarNums) :-
	map__det_insert(VarNums0, Var, N, VarNums1),
	N1 is N + 1,
	number_vars(Vars, N1, VarNums1, VarNums).

:- pred insert_equations(equations, int, int, map(lp_var, int), tableau, tableau).
:- mode insert_equations(in, in, in, in, in, out) is det.

insert_equations([], _, _, _, Tableau, Tableau).
insert_equations([Eqn|Eqns], Row, ConstCol, VarNums, Tableau0, Tableau) :-
	Eqn = eqn(Coeffs, _Op, Const),
	insert_coeffs(Coeffs, Row, VarNums, Tableau0, Tableau1),
	set_index(Tableau1, Row, ConstCol, Const, Tableau2),
	Row1 is Row + 1,
	insert_equations(Eqns, Row1, ConstCol, VarNums, Tableau2, Tableau).

:- pred insert_coeffs(list(coeff), int, map(lp_var, int), tableau, tableau).
:- mode insert_coeffs(in, in, in, in, out) is det.

insert_coeffs([], _Row, _VarNums, Tableau, Tableau).
insert_coeffs([Coeff|Coeffs], Row, VarNums, Tableau0, Tableau) :-
	Coeff = Var - Const,
	map__lookup(VarNums, Var, Col),
	set_index(Tableau0, Row, Col, Const, Tableau1),
	insert_coeffs(Coeffs, Row, VarNums, Tableau1, Tableau).

%------------------------------------------------------------------------------%

:- pred optimize(list(lp_var), tableau, tableau, lp_rational__result).
:- mode optimize(in, in, out, out) is det.

optimize(ObjVars, A0, A, Result) :- 
	simplex(A0, A, Res0),
	(
		Res0 = no ,
		Result = unbounded 
	;
		Res0 = yes,
		rhs_col(A, M),
		index(A, 0, M, ObjVal),
		extract_objective(ObjVars, A, ObjMap),
		Result = satisfiable(ObjVal, ObjMap)
	).

:- pred extract_objective(list(lp_var), tableau, map(lp_var, rat)).
:- mode extract_objective(in, in, out) is det.

extract_objective(ObjVars, Tab, Res) :-
	map__init(Res0),
	list__foldl(extract_obj_var(Tab), ObjVars, Res0, Res).

:- pred extract_obj_var(tableau, lp_var, map(lp_var, rat), map(lp_var, rat)).
:- mode extract_obj_var(in, in, in, out) is det.

extract_obj_var(Tab, Var, Map0, Map) :-
	urs_vars(Tab, Vars),
	( map__search(Vars, Var, Pos - Neg) ->
		extract_obj_var2(Tab, Pos, PosVal),
		extract_obj_var2(Tab, Neg, NegVal),
		Val is PosVal - NegVal
	;
		extract_obj_var2(Tab, Var, Val)
	),
	map__set(Map0, Var, Val, Map).

:- pred extract_obj_var2(tableau, lp_var, rat).
:- mode extract_obj_var2(in, in, out) is det.

extract_obj_var2(Tab, Var, Val) :-
	var_col(Tab, Var, Col),
	GetCell = lambda([Val0::out] is nondet, (
		all_rows(Tab, Row),
		index(Tab, Row, Col, one),
		rhs_col(Tab, RHS),
		index(Tab, Row, RHS, Val0)
	)),
	solutions(GetCell, Solns),
	( Solns = [Val1] ->
		Val = Val1
	;
		Val = zero
	).

:- pred simplex(tableau, tableau, bool).
:- mode simplex(in, out, out) is det.

simplex(A0, A, Result) :-
	AllColumns = all_cols(A0),
	MinAgg = lambda([Col::in, Min0::in, Min::out] is det, (
		(
			Min0 = no,
			index(A0, 0, Col, MinVal),
			( MinVal < zero ->
				Min = yes(Col - MinVal)
			;
				Min = no
			)
		;
			Min0 = yes(_ - MinVal0),
			index(A0, 0, Col, CellVal),
			( CellVal < MinVal0 ->
				Min = yes(Col - CellVal)
			;
				Min = Min0
			)
		)
	)),
	aggregate(AllColumns, MinAgg, no, MinResult),
	(
		MinResult = no,
		A = A0,
		Result = yes
	;
		MinResult = yes(Q - _Val),
		AllRows = all_rows(A0),
		MaxAgg = lambda([Row::in, Max0::in, Max::out] is det, (
			(
				Max0 = no,
				index(A0, Row, Q, MaxVal),
				( MaxVal > zero ->
					rhs_col(A0, RHSC),
					index(A0, Row, RHSC, MVal),
					require(nz(MaxVal), "simplex: zero 
						divisor MaxVal"),
					CVal is MVal/MaxVal,
					Max = yes(Row - CVal)
				;
					Max = no
				)
			;
				Max0 = yes(_ - MaxVal0),
				index(A0, Row, Q, CellVal),
				rhs_col(A0, RHSC),
				index(A0, Row, RHSC, MVal),
				( CellVal =< zero ->
				% CellVal = 0 indicates multiple optimal sol'ns
					Max = Max0
				;
					require(nz(CellVal), "simplex: zero 
					divisor CellVal"), 	
					MaxVal1 is MVal/CellVal,
					( MaxVal1 =< MaxVal0 ->
						Max = yes(Row - MaxVal1)
					;
						Max = Max0
					)
				)
			)
		)),
		aggregate(AllRows, MaxAgg, no, MaxResult),
		(
			MaxResult = no,
			A = A0,
			Result = no
		;
			MaxResult = yes(P - _),
			pivot(P, Q, A0, A1),
			simplex(A1, A, Result)
		)
	).

%------------------------------------------------------------------------------%

:- pred ensure_zero_obj_coeffs(list(lp_var), tableau, tableau).
:- mode ensure_zero_obj_coeffs(in, in, out) is det.

ensure_zero_obj_coeffs([], Tableau, Tableau).
ensure_zero_obj_coeffs([V|Vs], Tableau0, Tableau) :-
	var_col(Tableau0, V, Col),
	index(Tableau0, 0, Col, Val),
	( Val = zero ->
		ensure_zero_obj_coeffs(Vs, Tableau0, Tableau)
	;
		FindOne = lambda([P::out] is nondet, (
			all_rows(Tableau0, R),
			index(Tableau0, R, Col, ValF0),
			ValF0 \= zero,
			P = R - ValF0
		)),
		solutions(FindOne, Ones),
		(
			Ones = [Row - Fac0|_],
			require(nz(Fac0), "ensure_zero_obj_coeffs: 
				zero divisor Fac0"),
			Fac is -Val/Fac0,
			row_op(Fac, Row, 0, Tableau0, Tableau1),
			ensure_zero_obj_coeffs(Vs, Tableau1, Tableau)
		;
			Ones = [],
			error("problem with artificial variable")
		)
	).

:- pred fix_basis_and_rem_cols(list(lp_var), tableau, tableau).
:- mode fix_basis_and_rem_cols(in, in, out) is det.

fix_basis_and_rem_cols([], Tab, Tab).
fix_basis_and_rem_cols([V|Vs], Tab0, Tab) :-
	var_col(Tab0, V, Col),
	BasisAgg = lambda([R::in, Ones0::in, Ones::out] is det, (
		index(Tab0, R, Col, Val),
		( Val = zero ->
			Ones = Ones0
		;
			Ones = [Val - R|Ones0]
		)
	)),
	aggregate(all_rows(Tab0), BasisAgg, [], Res),
	(
		Res = [one - Row]
	->
		PivGoal = lambda([Col1::out] is nondet, (
			all_cols(Tab0, Col1),
			Col \= Col1,
			index(Tab0, Row, Col1, Zz),
			Zz \= zero
		)),
		solutions(PivGoal, PivSolns),
		(
			PivSolns = [],
			remove_col(Col, Tab0, Tab0a),
			remove_row(Row, Tab0a, Tab1)
		;
			PivSolns = [Col2|_],
			pivot(Row, Col2, Tab0, Tab0a),
			remove_col(Col, Tab0a, Tab1)
		)
	;
		Tab1 = Tab0
	),
	remove_col(Col, Tab1, Tab2),
	fix_basis_and_rem_cols(Vs, Tab2, Tab).

%------------------------------------------------------------------------------%

:- type cell	--->	cell(int, int).

:- pred pivot(int, int, tableau, tableau).
:- mode pivot(in, in, in, out) is det.

pivot(P, Q, A0, A) :-
	index(A0, P, Q, Apq),
	MostCells = lambda([Cell::out] is nondet, (
		all_rows0(A0, J),
		J \= P,
		all_cols0(A0, K),
		K \= Q,
		Cell = cell(J, K)
	)),
	ScaleCell = lambda([Cell::in, T0::in, T::out] is det, (
		Cell = cell(J, K),
		index(T0, J, K, Ajk),
		index(T0, J, Q, Ajq),
		index(T0, P, K, Apk),
		require(nz(Apq), "ScaleCell: zero divisor"),
		NewAjk is Ajk - Apk * Ajq / Apq,
		set_index(T0, J, K, NewAjk, T)
	)),
	aggregate(MostCells, ScaleCell, A0, A1),
	QColumn = lambda([Cell::out] is nondet, (
		all_rows0(A1, J),
		Cell = cell(J, Q)
	)),
	Zero = lambda([Cell::in, T0::in, T::out] is det, (
		Cell = cell(J, K),
		set_index(T0, J, K, zero, T)
	)),
	aggregate(QColumn, Zero, A1, A2),
	PRow = all_cols0(A2),
	ScaleRow = lambda([K::in, T0::in, T::out] is det, (
		index(T0, P, K, Apk),
		require(nz(Apq), "ScaleRow: zero divisor"),
		NewApk is Apk / Apq,
		set_index(T0, P, K, NewApk, T)
	)),
	aggregate(PRow, ScaleRow, A2, A3),
	set_index(A3, P, Q, one, A).

:- pred row_op(rat, int, int, tableau, tableau).
:- mode row_op(in, in, in, in, out) is det.

row_op(Scale, From, To, A0, A) :-
	AllCols = all_cols0(A0),
	AddRow = lambda([Col::in, T0::in, T::out] is det, (
		index(T0, From, Col, X),
		index(T0, To, Col, Y),
		Z is Y + (Scale * X),
		set_index(T0, To, Col, Z, T)
	)),
	aggregate(AllCols, AddRow, A0, A).

%------------------------------------------------------------------------------%

:- type tableau
	---> tableau(
		int,
		int,
		map(lp_var, int),
		map(lp_var, pair(lp_var)),
		list(int),	% shunned rows
		list(int),	% shunned cols
		map(pair(int), rat)
	).

:- pred init_tableau(int::in, int::in, map(lp_var, int)::in, 
		map(lp_var, pair(lp_var))::in, tableau::out) is det.

init_tableau(Rows, Cols, VarNums, URSVars, Tableau) :-
	map__init(Cells),
	Tableau = tableau(Rows, Cols, VarNums, URSVars, [], [], Cells).

:- pred index(tableau, int, int, rat).
:- mode index(in, in, in, out) is det.

index(Tableau, J, K, R) :-
	Tableau = tableau(_, _, _, _, SR, SC, Cells),
	(
		( list__member(J, SR)
		; list__member(K, SC)
		)
	->
		error("attempt to address shunned row/col")
	;
		true
	),
	(
		map__search(Cells, J - K, R0)
	->
		R = R0
	;
		R = zero
	).

:- pred set_index(tableau, int, int, rat, tableau).
:- mode set_index(in, in, in, in, out) is det.

set_index(Tableau0, J, K, R, Tableau) :-
	Tableau0 = tableau(Rows, Cols, VarNums, URS, SR, SC, Cells0),
	(
		( list__member(J, SR)
		; list__member(K, SC)
		)
	->
		error("attempt to write shunned row/col")
	;
		true
	),
	( R = zero ->
		map__delete(Cells0, J - K, Cells)
	;
		map__set(Cells0, J - K, R, Cells)
	),
	Tableau = tableau(Rows, Cols, VarNums, URS, SR, SC, Cells).

:- pred rhs_col(tableau, int).
:- mode rhs_col(in, out) is det.

rhs_col(tableau(_, RHS, _, _, _, _, _), RHS).

:- pred all_rows0(tableau, int).
:- mode all_rows0(in, out) is nondet.

all_rows0(Tableau, Row) :-
	Tableau = tableau(Rows, _Cols, _, _, SR, _, _),
	between(0, Rows, Row),
	\+ list__member(Row, SR).

:- pred all_rows(tableau, int).
:- mode all_rows(in, out) is nondet.

all_rows(Tableau, Row) :-
	Tableau = tableau(Rows, _Cols, _, _, SR, _, _),
	between(1, Rows, Row),
	\+ list__member(Row, SR).

:- pred all_cols0(tableau, int).
:- mode all_cols0(in, out) is nondet.

all_cols0(Tableau, Col) :-
	Tableau = tableau(_Rows, Cols, _, _, _, SC, _),
	between(0, Cols, Col),
	\+ list__member(Col, SC).

:- pred all_cols(tableau, int).
:- mode all_cols(in, out) is nondet.

all_cols(Tableau, Col) :-
	Tableau = tableau(_Rows, Cols, _, _, _, SC, _),
	Cols1 is Cols - 1,
	between(0, Cols1, Col),
	\+ list__member(Col, SC).

:- pred var_col(tableau, lp_var, int).
:- mode var_col(in, in, out) is det.

var_col(Tableau, Var, Col) :-
	Tableau = tableau(_, _, VarCols, _, _, _, _),
	map__lookup(VarCols, Var, Col).

:- pred urs_vars(tableau, map(lp_var, pair(lp_var))).
:- mode urs_vars(in, out) is det.

urs_vars(Tableau, URS) :-
	Tableau = tableau(_, _, _, URS, _, _, _).

:- pred remove_row(int, tableau, tableau).
:- mode remove_row(in, in, out) is det.

remove_row(R, Tableau0, Tableau) :-
	Tableau0 = tableau(Rows, Cols, VarNums, URS, SR, SC, Cells),
	Tableau = tableau(Rows, Cols, VarNums, URS, [R|SR], SC, Cells).

:- pred remove_col(int, tableau, tableau).
:- mode remove_col(in, in, out) is det.

remove_col(C, Tableau0, Tableau) :-
	Tableau0 = tableau(Rows, Cols, VarNums, URS, SR, SC, Cells),
	Tableau = tableau(Rows, Cols, VarNums, URS, SR, [C|SC], Cells).

:- pred get_basis_vars(tableau, list(lp_var)).
:- mode get_basis_vars(in, out) is det.

get_basis_vars(Tab, Vars) :-
	BasisCol = lambda([C::out] is nondet, (
		all_cols(Tab, C),
		NonZeroGoal = lambda([P::out] is nondet, (
			all_rows(Tab, R),
			index(Tab, R, C, Z),
			Z \= zero,
			P = R - Z
		)),
		solutions(NonZeroGoal, Solns),
		Solns = [_ - one]
	)),
	solutions(BasisCol, Cols),
	BasisVars = lambda([V::out] is nondet, (
		list__member(Col, Cols),
		Tab = tableau(_, _, VarCols, _, _, _, _),
		map__member(VarCols, V, Col)
	)),
	solutions(BasisVars, Vars).

%------------------------------------------------------------------------------%

	% For debugging ....

:- pred show_tableau(tableau, io__state, io__state).
:- mode show_tableau(in, di, uo) is det.

show_tableau(Tableau) -->
	{ Tableau = tableau(N, M, _, _, _, _, _) },
	{ string__format("Tableau (%d, %d):\n", [i(N), i(M)], Str) },
	io__write_string(Str),
	aggregate(all_rows0(Tableau), show_row(Tableau)).

:- pred show_row(tableau, int, io__state, io__state).
:- mode show_row(in, in, di, uo) is det.

show_row(Tableau, Row) -->
	aggregate(all_cols0(Tableau), show_cell(Tableau, Row)),
	io__write_string("\n").

:- pred show_cell(tableau, int, int, io__state, io__state).
:- mode show_cell(in, in, in, di, uo) is det.

show_cell(Tableau, Row, Col) -->
	{ index(Tableau, Row, Col, Val) },
	{ string__format("%2.2f\t", [f(float(Val))], Str) },
	io__write_string(Str),
	io__write(Val).

%------------------------------------------------------------------------------%

:- pred lp_info_init(lp_varset, list(lp_var), lp_info).
:- mode lp_info_init(in, in, out) is det.

lp_info_init(Varset0, URSVars, LPInfo) :-
	Introduce = lambda([Orig::in, VP0::in, VP::out] is det, (
		VP0 = VS0 - VM0,
		varset__new_var(VS0, V1, VS1),
		varset__new_var(VS1, V2, VS),
		map__set(VM0, Orig, V1 - V2, VM),
		VP = VS - VM
	)),
	map__init(URSMap0),
	list__foldl(Introduce, URSVars, Varset0 - URSMap0, Varset - URSMap),
	LPInfo = lp(Varset, URSMap, [], []).

:- pred new_slack_var(lp_var::out, lp_info::in, lp_info::out) is det.

new_slack_var(Var) -->
	get_varset(Varset0),
	{ varset__new_var(Varset0, Var, Varset) },
	set_varset(Varset),
	get_slack_vars(Vars),
	set_slack_vars([Var|Vars]).

:- pred new_art_var(lp_var::out, lp_info::in, lp_info::out) is det.

new_art_var(Var) -->
	get_varset(Varset0),
	{ varset__new_var(Varset0, Var, Varset) },
	set_varset(Varset),
	get_art_vars(Vars),
	set_art_vars([Var|Vars]).

:- pred get_varset(lp_varset::out, lp_info::in, lp_info::out) is det.

get_varset(Varset, Info, Info) :-
	Info = lp(Varset, _URSVars, _Slack, _Art).

:- pred set_varset(lp_varset::in, lp_info::in, lp_info::out) is det.

set_varset(Varset, Info0, Info) :-
	Info0 = lp(_Varset, URSVars, Slack, Art),
	Info  = lp(Varset, URSVars, Slack, Art).

:- pred get_urs_vars(map(lp_var, pair(lp_var))::out, lp_info::in, lp_info::out) is det.

get_urs_vars(URSVars, Info, Info) :-
	Info = lp(_Varset, URSVars, _Slack, _Art).

:- pred set_urs_vars(map(lp_var, pair(lp_var))::in, lp_info::in, lp_info::out) is det.

set_urs_vars(URSVars, Info0, Info) :-
	Info0 = lp(Varset, _URSVars, Slack, Art),
	Info  = lp(Varset, URSVars, Slack, Art).

:- pred get_slack_vars(list(lp_var)::out, lp_info::in, lp_info::out) is det.

get_slack_vars(Slack, Info, Info) :-
	Info = lp(_Varset, _URSVars, Slack, _Art).

:- pred set_slack_vars(list(lp_var)::in, lp_info::in, lp_info::out) is det.

set_slack_vars(Slack, Info0, Info) :-
	Info0 = lp(Varset, URSVars, _Slack, Art),
	Info  = lp(Varset, URSVars, Slack, Art).

:- pred get_art_vars(list(lp_var)::out, lp_info::in, lp_info::out) is det.

get_art_vars(Art, Info, Info) :-
	Info = lp(_Varset, _URSVars, _Slack, Art).

:- pred set_art_vars(list(lp_var)::in, lp_info::in, lp_info::out) is det.

set_art_vars(Art, Info0, Info) :-
	Info0 = lp(Varset, URSVars, Slack, _Art),
	Info  = lp(Varset, URSVars, Slack, Art).

%------------------------------------------------------------------------------%

:- pred between(int, int, int).
:- mode between(in, in, out) is nondet.

between(Min, Max, I) :-
	Min =< Max,
	(
		I = Min
	;
		Min1 is Min + 1,
		between(Min1, Max, I)
	).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%


% Fourier-Motzkin elimination.

% project(Equations0, Variables, Equations) takes a list of inequalities 
% and eliminates the variables in the input list, i.e. it projects onto
% those variables not in the list. 
project(Eqns, [], Eqns).
project(Eqns0, Vars, Eqns) :-
	Vars = [_|_],
	fm_standardize_equations(Eqns0, Eqns1),
	eqns_to_vectors(Eqns1, Vecs),
	eliminate_vars(Vars, Vecs, Matrix),
	vectors_to_eqns(Matrix, Eqns).


% fm_standardize_equations ensures all inequations are of the form
% a1x1 + ... + anxn =< C.  Inequalities containing >= are multiplied
% through by -1, and equations are converted into two inequations 
% of the form a1x1 + ... + anxn =< C, -a1x1 - ... - anxn =< -C. 
fm_standardize_equations(Eqns0, Eqns1) :- 
	fm_standardize_equations_acc(Eqns0, [], Eqns1).

:- pred fm_standardize_equations_acc(equations, equations, equations).
:- mode fm_standardize_equations_acc(in, in, out) is det.

fm_standardize_equations_acc([], Acc, Acc).
fm_standardize_equations_acc([Eqn0|Eqns], Acc0, Acc) :-
	(
		Eqn0 = eqn(_, (=<), _),
		Acc1 = [Eqn0|Acc0]
	;
		Eqn0 = eqn(Coeffs, (=), Const),
		Acc1 = [eqn(Coeffs, (=<), Const), Neg_eqn | Acc0],
		negate_equation(eqn(Coeffs, (>=), Const), Neg_eqn)
	;
		Eqn0 = eqn(Coeffs, (>=), Const),
		Acc1 = [Neg_eqn | Acc0],
		negate_equation(eqn(Coeffs, (>=), Const), Neg_eqn)
	),
	fm_standardize_equations_acc(Eqns, Acc1, Acc).


eqns_to_vectors(Eqns, Vecs) :-
	Eqn_to_vec = lambda([eqn(List, Op, Num)::in, 
						pair(Map, Num)::out] is det, (
		( Op = (=<) ->
			map__init(Map0),	
			coeff_list_to_map(List, Map0, Map)
		;
			error("Equality or >= passed to eqns_to_vectors\n")
		)
	)),
	list__map(Eqn_to_vec, Eqns, Vecs).


%:- pred vectors_to_eqns(list(vector), equations).
%:- mode vectors_to_eqns(in, out) is det.

vectors_to_eqns(Vectors, Equations) :-
	Vec_to_eqn = lambda([pair(Map,Rat)::in, Eqn::out] is det, (
		map__to_assoc_list(Map, List),
		Eqn = eqn(List, (=<), Rat)
	)),
	list__map(Vec_to_eqn, Vectors, Equations).	
		

% Add a list of coefficients to a map and returns the resulting map.
% Ensures that there are no zeros in the resulting map.
:- pred coeff_list_to_map(list(coeff), map(lp_var, rat), map(lp_var, rat)).
:- mode coeff_list_to_map(in, in, out) is det.

coeff_list_to_map([], Map, Map).
coeff_list_to_map([Var-Num | Coeffs], Map0, Map) :-
	( Num = zero ->
		Map1 = Map0
	;
		( map__search(Map0, Var, Num1) ->
			( Num1 + Num = zero ->
				map__delete(Map0, Var, Map1)
			;
				map__det_update(Map0, Var, Num+Num1, Map1)
			)
		;
			map__det_insert(Map0, Var, Num, Map1)	
		)
	),
	coeff_list_to_map(Coeffs, Map1, Map). 


% normalize_vector(Vec0, Var, Vec1) divides all coefficients in
% Vec0 by the absolute value of the coefficient of Var.
% (We are considering here the values, not the "coeff" type.)
% It is an error if the map contains a zero coefficient.
%:- pred normalize_vector(vector, lp_var, vector).
%:- mode normalize_vector(in, in, out) is det.

normalize_vector(pair(Map0, Num0), Var0, pair(Map, Num)) :-
	( map__search(Map0, Var0, Coeff) ->
		Is_map_key = lambda([Var::out] is nondet, (
			map__member(Map0, Var, _)	
		)),
		Divide_map_val = lambda([Var::in, Map1::in, Map2::out] is det, (
			map__lookup(Map1, Var, Coeff0),
			( Coeff0 = zero ->
				error("normalize_vector: map contains a zero coefficient")
			;
				require(nz(Coeff), 
					"normalize_vector: zero divisor"),
				Coeff1 = Coeff0 / abs(Coeff),
				map__det_update(Map1, Var, Coeff1, Map2)
			)
		)),	
		aggregate(Is_map_key, Divide_map_val, Map0, Map),
		require(nz(Coeff), "normalize_vector: zero divisor"),
		Num = Num0 / abs(Coeff)
	;
		Map = Map0,
		Num = Num0 
	).

% separate_vectors(List1, Variable, Positives, Negatives, Zeroes):
% Breaks a list of vectors up into three lists of vectors according to
% whether the coefficient of Variable is positive, negative or zero.
% Applies normalize_vector to each vector.
:- pred separate_vectors(matrix, lp_var, matrix, matrix, matrix).
:- mode separate_vectors(in, in, out, out, out) is det.

separate_vectors(Matrix, Var, Pos, Neg, Zero) :-
	separate_vectors_acc(Matrix, Var, [], [], [], Pos, Neg, Zero).

:- pred separate_vectors_acc(matrix, lp_var, matrix, matrix, 
				matrix, matrix, matrix, matrix).	
:- mode separate_vectors_acc(in, in, in, in, in, out, out, out) is det.

separate_vectors_acc([], _, Pos, Neg, Zeros, Pos, Neg, Zeros).
separate_vectors_acc([Vec0|Vectors], Var, Pos0, Neg0, Zeros0, Pos, Neg, Zeros):-
	( get_var_coeff(Vec0, Var, Coeff) ->
		normalize_vector(Vec0, Var, Vec1),
		( Coeff > zero ->  
			Pos1 = [Vec1 | Pos0],
			Neg1 = Neg0,
			Zeros1 = Zeros0
		;
			Pos1 = Pos0,
			Neg1 = [Vec1 | Neg0],
			Zeros1 = Zeros0
		)
	;
		Pos1 = Pos0,
		Neg1 = Neg0,
		Zeros1 = [Vec0 | Zeros0]
	),
	separate_vectors_acc(Vectors, Var, Pos1, Neg1, Zeros1, Pos, Neg, Zeros).

		
% Fails if the variable searched for is not in the vector
% (i.e. if it has coefficient zero). 
:- pred get_var_coeff(vector, lp_var, rat).
:- mode get_var_coeff(in, in, out) is semidet.

get_var_coeff(pair(Varmap, _), Var, Num) :-
	map__search(Varmap, Var, Num).

% add_vectors(Vec0, Vec1, Vec2): Vec2 is the sum of Vec0 and Vec1.
:- pred add_vectors(vector, vector, vector).
:- mode add_vectors(in, in, out) is det.

add_vectors(pair(Map0, Rat0), pair(Map1, Rat1), pair(Map2, Rat2)) :- 
	Rat2 = Rat0 + Rat1,
	Is_map_key = lambda([Var::out] is nondet, (
		map__member(Map0, Var, _)
	)),
	Add_val = lambda([Var::in, Map_i::in, Map_o::out] is det, (
		map__lookup(Map0, Var, Num0),
		( map__search(Map_i, Var, Num1) ->
			( Num0 + Num1 = zero ->
				map__delete(Map_i, Var, Map_o)
			;
				map__det_update(Map_i, Var, Num0+Num1, Map_o)
			)
		;
			map__det_insert(Map_i, Var, Num0, Map_o)
		)
	)),
	aggregate(Is_map_key, Add_val, Map1, Map2).

% Eliminates a variable V from three sets of linear inequalities, 
% assuming that the inequations in the first list have a positive
% coefficient for V, and that the second and third lists contain negative
% and zero coefficients respectively.
:- pred eliminate_var(lp_var, matrix, matrix, matrix, matrix).
:- mode eliminate_var(in, in, in, in, out) is det.		

eliminate_var(_, [], _, Matrix, Matrix).
eliminate_var(Var, [Vec_P|Pos], Neg, Zeros, Result) :-
	Add_vec = lambda([Vec0::in, Vec1::out] is semidet, (
		add_vectors(Vec_P, Vec0, Vec1),
		Vec1 = pair(Map1, Const),
		not ( map__is_empty(Map1), Const >= zero )
	)),
	list__filter_map(Add_vec, Neg, Zeros1),
	list__append(Zeros1, Zeros, New_zeros),
	eliminate_var(Var, Pos, Neg, New_zeros, Result). 


:- pred eliminate_vars(list(lp_var), matrix, matrix).
:- mode eliminate_vars(in, in, out) is det.

eliminate_vars([], Matrix, Matrix). 
eliminate_vars([Var|Vars], Matrix, Result) :-
	separate_vectors(Matrix, Var, Pos, Neg, Zeros),
	eliminate_var(Var, Pos, Neg, Zeros, New_zeros1),
	list__sort_and_remove_dups(New_zeros1, New_zeros),

	%This seems to slow it down (a lot).
	%remove_some_redundancies(New_zeros2, [], New_zeros),

	eliminate_vars(Vars, New_zeros, Result).
	

% Removes all constraints of the form a1x1 + ... + anxn <= A
% where there exists another constraint a1x1 + ... + anxn <= B
% and B <= A.
:- pred remove_some_redundancies(matrix, matrix, matrix).
:- mode remove_some_redundancies(in, in, out) is det.

remove_some_redundancies([], Constraints, Constraints).
remove_some_redundancies([Constr0|Equations0], Constrs, Equations) :-
	find_strongest_remove_weaker(Constr0, Constr, Equations0, Equations1),
	remove_some_redundancies(Equations1, [Constr|Constrs], Equations).


% Removes all equations in the given list which are
% weaker than the given constraint Vec0. Returns the strongest vector
% which is comparable to Vec0, and the list with the redundant 
% constraints removed.
:- pred find_strongest_remove_weaker(vector, vector, matrix, matrix).
:- mode find_strongest_remove_weaker(in, out, in, out) is det.

find_strongest_remove_weaker(Vec0, Vec, Matrix0, Matrix) :-
	Comp_constraints = lambda([Vec1::in, Str_vec0::in, Str_vec1::out, 
				   List1::in, List2::out] is det, (
		( compare_constraints(Str_vec0, Vec1, Str_vec) ->
			( Str_vec = Str_vec0 ->
				List2 = List1,
				Str_vec1 = Str_vec0
			;
				List2 = List1,
				Str_vec1 = Vec1
			)
		;
			List2 = [Vec1|List1],
			Str_vec1 = Str_vec0
		)
	)),
	list__foldl2(Comp_constraints, Matrix0, Vec0, Vec, [], Matrix).


% Fails if neither constraint implies the other.
% Otherwise, returns the stronger constraint.
% XX Works only with normalized vectors 
%    because   x +  y <= 2   should imply   2x + 2y <= 4   and it doesn't.
%    OR must be specified : normalized vectors in input.

:- pred compare_constraints(vector, vector, vector).
:- mode compare_constraints(in, in, out) is semidet.

compare_constraints(pair(Map0,Rat0), pair(Map1,Rat1), pair(Map3,Rat)) :-
	map__keys(Map0, Keylist),
	Del_same_keys = lambda([Var0::in, Map4::in, Map5::out] is semidet, (
		map__lookup(Map0, Var0, Num0),
		map__remove(Map4, Var0, Num4, Map5),
		Num4 = Num0
	)),
	list__foldl(Del_same_keys, Keylist, Map1, Map2),
	map__is_empty(Map2),
	Map3 = Map0,
	( Rat0 < Rat1 ->
		Rat = Rat0
	;
		Rat = Rat1
	). 







%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% Convex Hull


:- type var_info 
	---> 	var_info(
			 list(map(lp_var, lp_var)), 
			 			% Maps from original variables
						% to new (temporary) ones.
						% A variable which occurs in 
						% more than one polyhedron is
						% mapped to a separate variable
						% for each one.
						% This list contains one map
						% for each polyhedron.

			 list(lp_var), 	% List of sigma variables.

			 lp_varset
			).

:- type eqn_info
	---> 	eqn_info(
			 map(lp_var, lp_var),	% Map from original variables
						% to new (temporary) ones.
						% There is one of these for
						% each equation. 
			 lp_varset
  			 ).
 
% convex_hull takes a list of polyhedra (represented as lists of constraints)
% and computes the smallest convex set which is a superset of all of them. 
% For details of the algorithm, see Benoy and King.
convex_hull([], [], Vars, Vars).
convex_hull([Poly], Poly, Vars, Vars).
convex_hull([Poly0,Poly1|Polys_in], Poly, Vars1, Vars) :-
	Polys0 = [Poly0,Poly1|Polys_in],
	
		% tranform all equations in '=<' equations
	list__map(fm_standardize_equations, Polys0, Polys),

		% rename all variables in the equations of the polyhedra 
		% and add sigma variables (and the related equations)
	transform_polys(Polys, Eqns1, var_info([], [], Vars1), 
					var_info(Map_list, Sigmas, Vars)),
	add_sigma_eqns(Eqns1, Sigmas, Eqns2),
	
		% add the equations related to the original variables
	add_last_eqns(Eqns2, Map_list, Eqns3),

		% project all the equations on the original variables,
		% that is eliminating sigma and new (temporary) variables
	Append_values = lambda([Map::in, Varlist0::in, Varlist::out] is det, (
		map__values(Map, List),
		append(List, Varlist0, Varlist)
	)),	
	list__foldl(Append_values, Map_list, [], Values),	
	append(Sigmas, Values, Variables),
	project(Eqns3, Variables, Poly).
	

:- pred transform_polys(list(equations), equations, var_info, var_info). 
:- mode transform_polys(in, out, in, out) is det.

transform_polys(Polys, Eqns, Var_info0, Var_info) :-
	list__foldl2(transform_poly, Polys, [], Eqns, Var_info0, Var_info).


% transform_poly: takes a polygon (with original variables), a list
% of the polygons transformed so far and variable information.  
% It substitutes new (temporary) variables for all of the variables
% in the polygon while constructing a map from old variables to new
% ones.  The new polygon is then added to the list of transformed ones.  
% It then updates the variable info by adding the new map and a new
% sigma variable.
:- pred transform_poly(equations, equations, equations, var_info, var_info).
:- mode transform_poly(in, in, out, in, out) is det.

transform_poly(Poly, Polys0, Polys, var_info(Maps0, Sigmas0, Vars0), Var_info):-
	map__init(Newmap),
	varset__new_var(Vars0, Sigma, Vars1),
	Trans_eqn = lambda([Eqn0::in, Eqn::out, Eq_inf0::in, 
							Eq_inf1::out] is det, ( 
		transform_eqn(Eqn0, Eqn, Sigma, Eq_inf0, Eq_inf1)
	)),
	list__map_foldl(Trans_eqn, Poly, New_eqns, eqn_info(Newmap, Vars1), 
				eqn_info(Map, Vars)),
	append(New_eqns, Polys0, Polys),
	Var_info = var_info([Map|Maps0], [Sigma|Sigmas0], Vars).  
 
% transform_eqn: takes an equation (with original variables) and the sigma 
% variable to add, and returns the equation where the original variables 
% are substituted for new ones and where the sigma variable is included. 
% The map of old to new variables is updated if necessary.
:- pred transform_eqn(equation, equation, lp_var, eqn_info, eqn_info).
:- mode transform_eqn(in, out, in, in, out) is det.

transform_eqn(eqn(Coeffs0, Op, Num0), eqn(Coeffs, Op, Num), Sigma,
				eqn_info(Map0, Vars0), eqn_info(Map, Vars)) :- 
	list__map_foldl(change_var, Coeffs0, Coeffs1, 
		eqn_info(Map0, Vars0), eqn_info(Map, Vars)), 
	NegNum0 is -Num0,
	Coeffs = [Sigma - NegNum0|Coeffs1],
	Num = zero.

% change_var: takes a Var-Num pair with an old variable and returns one with
% a new variable which the old variable maps to.  Updates the map of old to 
% new variables if necessary.
:- pred change_var(coeff, coeff, eqn_info, eqn_info).
:- mode change_var(in, out, in, out) is det.

change_var(Var0-Num, Var-Num, eqn_info(Map0, Varset0), eqn_info(Map, Varset)) :-
	% Have we already mapped this original variable to a new one?
	( map__search(Map0, Var0, Var2) ->
		Var = Var2,
		Map = Map0,
		Varset = Varset0
	;
		varset__new_var(Varset0, Nvar, Varset),
		map__det_insert(Map0, Var0, Nvar, Map),
		Var = Nvar
	).



% add_sigma_eqns: Takes the list of equations so far and appends
% the non-negativity equation for each sigma variable,
% and an equation stating that the sum of the sigmas is one. 
:- pred add_sigma_eqns(equations, list(lp_var), equations).
:- mode add_sigma_eqns(in, in, out) is det.

add_sigma_eqns(Eqns0, Sigmas, Eqns) :- 
	Non_neg = lambda([Var::in, Eqn::out] is det, (
		NegOne = -one,
		Eqn = eqn([Var - NegOne], (=<), zero)
	)),
	list__map(Non_neg, Sigmas, Eqns1),
	append(Eqns1, Eqns0, Eqns2),
	Var_to_coeff = lambda([Var::in, Coeff::out] is det, (
		Coeff = Var-one
	)),
	list__map(Var_to_coeff, Sigmas, Coefflist),
	fm_standardize_equations([eqn(Coefflist, (=), one)], Eqns3),
	append(Eqns3, Eqns2, Eqns).
		 
% add_last_eqns: Adds the equations stating that each original
% variable is the sum of the temporary variables to which it has
% been mapped.
:- pred add_last_eqns(equations, list(map(lp_var,lp_var)), equations).
:- mode add_last_eqns(in, in, out) is det.

add_last_eqns(Eqns0, Old_to_new_var_maps, Eqns) :-
	get_map_keys(Old_to_new_var_maps, [],  Keys1),
	VarComp = lambda([Var1::in, Var2::in, Res::out] is det, (
		compare(Res, Var1, Var2)
	)),
	list__sort_and_remove_dups(VarComp, Keys1, Keys),
	Original_var_to_eqn = lambda([Orig_var::in, Eqn::out] is semidet, (
		original_var_to_eqn(Orig_var, Old_to_new_var_maps, Eqn)
	)),
	list__filter_map(Original_var_to_eqn, Keys, Eqns1),
	fm_standardize_equations(Eqns1, Eqns2),
	append(Eqns2, Eqns0, Eqns).


:- pred original_var_to_eqn(lp_var, list(map(lp_var,lp_var)), equation).
:- mode original_var_to_eqn(in, in, out) is semidet.

original_var_to_eqn(Original_var, Maplist, Eqn) :-
	Corresp_vars = lambda([Map::in, Coeffs0::in, Coeffs::out] is semidet, (
		map__search(Map, Original_var, Newvar),  
		NegOne = -one,
		Coeffs = [Newvar - NegOne |Coeffs0]
	)),
	list__foldl(Corresp_vars, Maplist, [], Coefflist),
	Eqn = eqn([Original_var-one|Coefflist], (=), zero).


% get_map_keys: Given a list of maps, return a list of all the keys in 
% the list of maps.
:- pred get_map_keys(list(map(lp_var,lp_var)), list(lp_var), list(lp_var)).
:- mode get_map_keys(in, in, out) is det.

get_map_keys([], Keys, Keys).
get_map_keys([Map|Maps], Keys0, Keys) :-
	map__keys(Map, Keys1),
	append(Keys1, Keys0, NewKeys),
	get_map_keys(Maps, NewKeys, Keys).

%-----------------------------------------------------------------------------%
% Widening

% widen(Cs1, Cs2, Vars, Cs): Relaxes the constraints Cs1 by selecting
% those constraints from Cs1 which are implied by Cs2. 
widen(Poly1, Poly2, Vars, Wide_poly) :-
	Entailed_by_Poly2 = lambda([Constraint::in] is semidet, (
		entailed(Constraint, Poly2, Vars)
	)),
	list__filter(Entailed_by_Poly2, Poly1, Wide_poly).


% entailed(C, Cs, Vars): Determines whether the constraint C is
% implied by the set of constraints Cs. 
% Uses the simplex method to find the point P satisfying Cs
% which maximises (or minimises if C contains >= ) a function parallel 
% to C.  Then tests whether P satisfies C.
% This assumes that all the variables are non-negative. 
entailed(eqn(Coeff_list, (=<), Const), Poly, Vars) :-
	Objective = Coeff_list,
	lp_solve(Poly, max, Objective, Vars, [], Result),  
	( 
		Result = satisfiable(Max_val, _),
		Max_val =< Const	
	;
		Result = inconsistent,
		error("inconsistent polygon passed to entailed")
	;
		Result = unbounded,
		fail
	).
	

entailed(eqn(Coeff_list, (>=), Const), Poly, Vars) :-
	Objective = Coeff_list,
	lp_solve(Poly, min, Objective, Vars, [], Result),  
	( 
		Result = satisfiable(Min_val, _),
		Min_val >= Const	
	;
		Result = inconsistent,
		error("inconsistent polygon passed to entailed")
	;
		Result = unbounded,
		fail
	).
	

entailed(eqn(Coeff_list, (=), Const), Poly, Vars) :-
	entailed(eqn(Coeff_list, (=<), Const), Poly, Vars),
	entailed(eqn(Coeff_list, (>=), Const), Poly, Vars).


:- pred nz(rat::in) is semidet.

nz(X) :- X \= zero.


%-----------------------------------------------------------------------------
% Printing equations and vectors.

write_equations(Equations, IO0, IO) :-
	fm_standardize_equations(Equations, Standardized_eqns),
	eqns_to_vectors(Standardized_eqns, Vectors),
	write_vectors(Vectors, IO0, IO).

write_vectors(Matrix, IO0, IO) :-
	io__write_list(Matrix, "\n", write_vector, IO0, IO).

:- pred write_vector(vector, io__state, io__state).
:- mode write_vector(in, di, uo) is det.
write_vector(pair(Map, Rat)) --> 
	{ map__to_assoc_list(Map, List) },
	io__write_list(List, " ", write_term),
	io__write_char(' '),
	io__write_string("=<"),
	io__write_char(' '),
	io__write_int(numer(Rat)),
	io__write_char('/'),
	io__write_int(denom(Rat)).


% writes nothing if the coefficient of the term is 0.
:- pred write_term(coeff, io__state, io__state).
:- mode write_term(in, di, uo) is det.

write_term(Var-Rat) -->
	( { Rat = one } ->
		io__write_char('+'),
		io__write_char(' ')
	;
		io__write_char('('),
		io__write_int(numer(Rat)),
		io__write_char('/'),
		io__write_int(denom(Rat)),
		io__write_char(')')
	),
	io__write_char('x'),
	{ term__var_to_int(Var, Int) },
	io__write_int(Int).
