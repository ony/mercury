%---------------------------------------------------------------------------%
% Copyright (C) 2001-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: xrobdd.m.
% Main author: dmo
% Stability: low

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module xrobdd__tfenr_robdd.

:- interface.

:- import_module term, robdd.

:- type xrobdd(T).
:- type xrobdd == xrobdd(generic).

:- inst xrobdd == ground. % XXX

:- mode di_xrobdd == in. % XXX
:- mode uo_xrobdd == out. % XXX

% Constants.
:- func one = xrobdd(T).
:- func zero = xrobdd(T).

% Conjunction.
:- func xrobdd(T) * xrobdd(T) = xrobdd(T).

% Disjunction.
:- func xrobdd(T) + xrobdd(T) = xrobdd(T).

%-----------------------------------------------------------------------------%

:- func var(var(T)::in, xrobdd(T)::in(xrobdd)) = (xrobdd(T)::out(xrobdd))
		is det.

:- func not_var(var(T)::in, xrobdd(T)::in(xrobdd)) = (xrobdd(T)::out(xrobdd))
		is det.

:- func eq_vars(var(T)::in, var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func neq_vars(var(T)::in, var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func imp_vars(var(T)::in, var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func conj_vars(vars(T)::in, xrobdd(T)::di_xrobdd) = (xrobdd(T)::uo_xrobdd)
		is det.

:- func conj_not_vars(vars(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func disj_vars(vars(T)::in, xrobdd(T)::di_xrobdd) = (xrobdd(T)::uo_xrobdd)
		is det.

:- func at_most_one_of(vars(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func not_both(var(T)::in, var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func io_constraint(var(T)::in, var(T)::in, var(T)::in, xrobdd(T)::di_xrobdd)
		= (xrobdd(T)::uo_xrobdd) is det.

		% disj_vars_eq(Vars, Var) <=> (disj_vars(Vars) =:= Var).
:- func disj_vars_eq(vars(T)::in, var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func var_restrict_true(var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

:- func var_restrict_false(var(T)::in, xrobdd(T)::di_xrobdd) =
		(xrobdd(T)::uo_xrobdd) is det.

%-----------------------------------------------------------------------------%

	% Succeed iff the var is entailed by the xROBDD.
:- pred var_entailed(xrobdd(T)::in, var(T)::in) is semidet.

	% Return the set of vars entailed by the xROBDD.
:- func vars_entailed(xrobdd(T)) = vars_entailed_result(T).

	% Return the set of vars disentailed by the xROBDD.
:- func vars_disentailed(xrobdd(T)) = vars_entailed_result(T).

	% Existentially quantify away the var in the xROBDD.
:- func restrict(var(T), xrobdd(T)) = xrobdd(T).

	% Existentially quantify away all vars greater than the specified var.
:- func restrict_threshold(var(T), xrobdd(T)) = xrobdd(T).

:- func restrict_filter(pred(var(T))::(pred(in) is semidet),
		xrobdd(T)::di_xrobdd) = (xrobdd(T)::uo_xrobdd) is det.

%-----------------------------------------------------------------------------%

	% labelling(Vars, xROBDD, TrueVars, FalseVars)
	%	Takes a set of Vars and an xROBDD and returns a value assignment
	%	for those Vars that is a model of the Boolean function
	%	represented by the xROBDD.
	%	The value assignment is returned in the two sets TrueVars (set
	%	of variables assigned the value 1) and FalseVars (set of
	%	variables assigned the value 0).
	%
	% XXX should try using sparse_bitset here.
:- pred labelling(vars(T)::in, xrobdd(T)::in, vars(T)::out, vars(T)::out)
		is nondet.

	% minimal_model(Vars, xROBDD, TrueVars, FalseVars)
	%	Takes a set of Vars and an xROBDD and returns a value assignment
	%	for those Vars that is a minimal model of the Boolean function
	%	represented by the xROBDD.
	%	The value assignment is returned in the two sets TrueVars (set
	%	of variables assigned the value 1) and FalseVars (set of
	%	variables assigned the value 0).
	%
	% XXX should try using sparse_bitset here.
:- pred minimal_model(vars(T)::in, xrobdd(T)::in, vars(T)::out, vars(T)::out)
		is nondet.

%-----------------------------------------------------------------------------%


:- implementation.

:- import_module robdd, sparse_bitset, bool, int.

% T - true vars, F - False Vars, E - equivalent vars, N -
% non-equivalent vars, R - ROBDD.
%
% Combinations to try:
%	R	(straight ROBDD)
%	TER	(Peter Schachte's extension)
%	TFENR	(Everything)

:- type xrobdd(T)
	--->	xrobdd(
			true_vars :: vars(T),
			false_vars :: vars(T),
			robdd :: robdd(T)
		).

one = xrobdd(init, init, one).

zero = xrobdd(init, init, zero).

xrobdd(TA, FA, RA) * xrobdd(TB, FB, RB) = 
		normalise(xrobdd(TA `union` TB, FA `union` FB, RA * RB)).

xrobdd(TA, FA, RA0) + xrobdd(TB, FB, RB0) = X :-
	( RA0 = zero ->
		X = xrobdd(TB, FB, RB0)
	; RB0 = zero ->
		X = xrobdd(TA, FA, RA0)
	;
		RA = RA0 * conj_vars(TA `difference` TB) * 
			conj_not_vars(FA `difference` FB),
		RB = RB0 * conj_vars(TB `difference` TA) *
			conj_not_vars(FB `difference` FA),
		X = xrobdd(TA `intersect` TB, FA `intersect` FB, RA + RB)
	).

var_entailed(X, V) :-
	(X ^ robdd = zero ; X ^ true_vars `contains` V).

vars_entailed(X) =
	(X ^ robdd = zero ->
		all_vars
	;
		some_vars(X ^ true_vars)
	).

vars_disentailed(X) =
	(X ^ robdd = zero ->
		all_vars
	;
		some_vars(X ^ false_vars)
	).

restrict(V, xrobdd(T, F, R)) =
	xrobdd(T `delete` V, F `delete` V, restrict(V, R)).

restrict_threshold(V, xrobdd(T, F, R)) =
		xrobdd(filter(P, T), filter(P, F), restrict_threshold(V, R)) :-
	P = (pred(U::in) is semidet :- \+ compare((>), U, V)).

var(V, X) =
	( T `contains` V ->
		X
	; F `contains` V ->
		zero
	;
		normalise(xrobdd(T `insert` V, F, R))
	) :-
	X = xrobdd(T, F, R).

not_var(V, X) =
	( F `contains` V ->
		X
	; T `contains` V ->
		zero
	;
		normalise(xrobdd(T, F `insert` V, R))
	) :-
	X = xrobdd(T, F, R).

eq_vars(VarA, VarB, X) = 
	( 
		( T `contains` VarA, T `contains` VarB
		; F `contains` VarA, F `contains` VarB
		)
	->
		X
	;
		( T `contains` VarA, F `contains` VarB
		; F `contains` VarA, T `contains` VarB
		)
	->
		zero
	;
		normalise(xrobdd(T, F, R * eq_vars(VarA, VarB)))
	) :-
	X = xrobdd(T, F, R).

neq_vars(VarA, VarB, X) = 
	( 
		( T `contains` VarA, T `contains` VarB
		; F `contains` VarA, F `contains` VarB
		)
	->
		zero
	;
		( T `contains` VarA, F `contains` VarB
		; F `contains` VarA, T `contains` VarB
		)
	->
		X
	;
		normalise(xrobdd(T, F, R * neq_vars(VarA, VarB)))
	) :-
	X = xrobdd(T, F, R).

imp_vars(VarA, VarB, X) =
	( T `contains` VarA, F `contains` VarB ->
		zero
	; T `contains` VarB ->
		X
	; F `contains` VarA ->
		X
	;
		normalise(xrobdd(T, F, R * imp_vars(VarA, VarB)))
	) :-
	X = xrobdd(T, F, R).

conj_vars(Vars, X) =
	( Vars `subset` T ->
		X
	; \+ empty(Vars `intersect` F) ->
		zero
	;
		normalise(xrobdd(T `union` Vars, F, R))
	) :-
	X = xrobdd(T, F, R).

conj_not_vars(Vars, X) =
	( Vars `subset` F ->
		X
	; \+ empty(Vars `intersect` T) ->
		zero
	;
		normalise(xrobdd(T, F `union` Vars, R))
	) :-
	X = xrobdd(T, F, R).

disj_vars(Vars, xrobdd(T, F, R)) =
	( \+ empty(Vars `intersect` T) ->
		xrobdd(T, F, R)
	; Vars `subset` F ->
		zero
	;
		normalise(xrobdd(T, F, R * disj_vars(Vars)))
	).

at_most_one_of(Vars, X) =
	( count(Vars `difference` F) =< 1 ->
		X
	; count(Vars `intersect` T) > 1 ->
		zero
	;
		normalise(xrobdd(T, F, R * at_most_one_of(Vars)))
	) :-
	X = xrobdd(T, F, R).

not_both(VarA, VarB, X) =
	normalise(X ^ robdd := X ^ robdd * ~(var(VarA) * var(VarB))).

io_constraint(V_in, V_out, V_, X) = 
	normalise(X ^ robdd :=
		X ^ robdd * 
			( var(V_out) =:= var(V_in) + var(V_) ) *
			( ~(var(V_in) * var(V_)) )).

disj_vars_eq(Vars, Var, X) = 
	( F `contains` Var ->
		( Vars `subset` F ->
			X
		;
			X ^ conj_not_vars(Vars)
		)
	; T `contains` Var ->
		( Vars `subset` F ->
			zero
		;
			X ^ disj_vars(Vars)
		)
	;
		normalise(xrobdd(T, F, R * (disj_vars(Vars) =:= var(Var))))
	) :-
	X = xrobdd(T, F, R).

var_restrict_true(V, xrobdd(T, F, R)) =
	( F `contains` V ->
		zero
	; T `contains` V ->
		xrobdd(T `delete` V, F, R)
	;
		normalise(xrobdd(T, F, var_restrict_true(V, R)))
	).

var_restrict_false(V, xrobdd(T, F, R)) =
	( T `contains` V ->
		zero
	; F `contains` V ->
		xrobdd(T, F `delete` V, R)
	;
		normalise(xrobdd(T, F, var_restrict_false(V, R)))
	).

restrict_filter(P, xrobdd(T, F, R)) =
	xrobdd(filter(P, T), filter(P, F), restrict_filter(P, R)).

labelling(Vars, xrobdd(T, F, R), TrueVars `intersect` Vars `union` T,
		FalseVars `intersect` Vars `union` F) :-
	labelling(Vars, R, TrueVars, FalseVars).

minimal_model(Vars, xrobdd(T, F, R), TrueVars `intersect` Vars `union` T,
		FalseVars `intersect` Vars `union` F) :-
	minimal_model(Vars, R, TrueVars, FalseVars).

%-----------------------------------------------------------------------------%

:- func normalise(xrobdd(T)::di_xrobdd) = (xrobdd(T)::uo_xrobdd) is det.

normalise(xrobdd(TrueVars0, FalseVars0, Robdd0)) = X :-
	%( some [V] (V `member` TrueVars0, V `member` FalseVars0) ->
	( \+ empty(TrueVars0 `intersect` FalseVars0) ->
		X = zero
	;
		Robdd1 = restrict_true_false_vars(TrueVars0, FalseVars0,
				Robdd0),
		(
			definite_vars(Robdd1,
				some_vars(TrueVars1), some_vars(FalseVars1))
		->
			(
				empty(TrueVars1),
				empty(FalseVars1)
			->
				X = xrobdd(TrueVars0, FalseVars0, Robdd1)
			;
				X = xrobdd(TrueVars0 `union` TrueVars1,
					FalseVars0 `union` FalseVars1,
					restrict_true_false_vars(TrueVars1,
						FalseVars1, Robdd1))
			)
		;
			X = zero
		)
	).
