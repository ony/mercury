%---------------------------------------------------------------------------%
% Copyright (C) 2001-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: tfr_robdd.m.
% Main author: dmo
% Stability: low

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module xrobdd__tfr_robdd.

:- interface.

:- import_module term, robdd.

:- type tfr(T).
:- type tfr == tfr(generic).

:- inst tfr == ground. % XXX

:- mode di_tfr == in. % XXX
:- mode uo_tfr == out. % XXX

% Constants.
:- func one = tfr(T).
:- func zero = tfr(T).

% Conjunction.
:- func tfr(T) * tfr(T) = tfr(T).

% Disjunction.
:- func tfr(T) + tfr(T) = tfr(T).

%-----------------------------------------------------------------------------%

:- func var(var(T)::in, tfr(T)::in(tfr)) = (tfr(T)::out(tfr))
		is det.

:- func not_var(var(T)::in, tfr(T)::in(tfr)) = (tfr(T)::out(tfr))
		is det.

:- func eq_vars(var(T)::in, var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func neq_vars(var(T)::in, var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func imp_vars(var(T)::in, var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func conj_vars(vars(T)::in, tfr(T)::di_tfr) = (tfr(T)::uo_tfr)
		is det.

:- func conj_not_vars(vars(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func disj_vars(vars(T)::in, tfr(T)::di_tfr) = (tfr(T)::uo_tfr)
		is det.

:- func at_most_one_of(vars(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func not_both(var(T)::in, var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func io_constraint(var(T)::in, var(T)::in, var(T)::in, tfr(T)::di_tfr)
		= (tfr(T)::uo_tfr) is det.

		% disj_vars_eq(Vars, Var) <=> (disj_vars(Vars) =:= Var).
:- func disj_vars_eq(vars(T)::in, var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func var_restrict_true(var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

:- func var_restrict_false(var(T)::in, tfr(T)::di_tfr) =
		(tfr(T)::uo_tfr) is det.

%-----------------------------------------------------------------------------%

	% Succeed iff the var is entailed by the xROBDD.
:- pred var_entailed(tfr(T)::in, var(T)::in) is semidet.

	% Return the set of vars entailed by the xROBDD.
:- func vars_entailed(tfr(T)) = vars_entailed_result(T).

	% Return the set of vars disentailed by the xROBDD.
:- func vars_disentailed(tfr(T)) = vars_entailed_result(T).

	% Existentially quantify away the var in the xROBDD.
:- func restrict(var(T), tfr(T)) = tfr(T).

	% Existentially quantify away all vars greater than the specified var.
:- func restrict_threshold(var(T), tfr(T)) = tfr(T).

:- func restrict_filter(pred(var(T))::(pred(in) is semidet),
		tfr(T)::di_tfr) = (tfr(T)::uo_tfr) is det.

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
:- pred labelling(vars(T)::in, tfr(T)::in, vars(T)::out, vars(T)::out)
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
:- pred minimal_model(vars(T)::in, tfr(T)::in, vars(T)::out, vars(T)::out)
		is nondet.
%-----------------------------------------------------------------------------%

% XXX
:- func robdd(tfr(T)) = robdd(T).


%-----------------------------------------------------------------------------%


:- implementation.

:- import_module robdd, sparse_bitset, bool, int, list.

% T - true vars, F - False Vars, E - equivalent vars, N -
% non-equivalent vars, R - ROBDD.
%
% Combinations to try:
%	R	(straight ROBDD)
%	TER	(Peter Schachte's extension)
%	TFENR	(Everything)

:- type tfr(T)
	--->	xrobdd(
			true_vars :: vars(T),
			false_vars :: vars(T),
			robdd :: robdd(T)
		).

one = xrobdd(init, init, one).

zero = xrobdd(init, init, zero).

xrobdd(TA, FA, RA) * xrobdd(TB, FB, RB) = 
	normalise(xrobdd(TA1 `union` TB1, FA1 `union` FB1, RA1 * RB1)) :-

	TU = TA `union` TB,
	FU = FA `union` FB,
	xrobdd(TA1, FA1, RA1) = normalise(xrobdd(TU, FU, RA)),
	xrobdd(TB1, FB1, RB1) = normalise(xrobdd(TU, FU, RB)).

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
		X `x` eq_vars(VarA, VarB)
	) :-
	X = xrobdd(T, F, _R).

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
		X `x` neq_vars(VarA, VarB)
	) :-
	X = xrobdd(T, F, _R).

imp_vars(VarA, VarB, X) =
	( T `contains` VarA, F `contains` VarB ->
		zero
	; T `contains` VarB ->
		X
	; F `contains` VarA ->
		X
	;
		X `x` imp_vars(VarA, VarB)
	) :-
	X = xrobdd(T, F, _R).

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

disj_vars(Vars, X) =
	( \+ empty(Vars `intersect` T) ->
		X
	; Vars `subset` F ->
		zero
	;
		X `x` disj_vars(Vars)
	) :-
	X = xrobdd(T, F, _R).

at_most_one_of(Vars, X) =
	( count(Vars `difference` F) =< 1 ->
		X
	; count(Vars `intersect` T) > 1 ->
		zero
	;
		X `x` at_most_one_of(Vars)
	) :-
	X = xrobdd(T, F, _R).

/*
not_both(VarA, VarB, X) =
	normalise(X ^ robdd := X ^ robdd * ~(var(VarA) * var(VarB))).
*/
not_both(VarA, VarB, X) =
	( F `contains` VarA ->
		X
	; F `contains` VarB ->
		X
	; T `contains` VarA ->
		not_var(VarB, X)
	; T `contains` VarB ->
		not_var(VarA, X)
	;
		X `x` (not_var(VarA) + not_var(VarB))
	) :-
	X = xrobdd(T, F, _R).

io_constraint(V_in, V_out, V_, X) = 
	X ^ not_both(V_in, V_) ^ disj_vars_eq(Vars, V_out) :-
	Vars = list_to_set([V_in, V_]).

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
		X `x` (disj_vars(Vars) =:= var(Var))
	) :-
	X = xrobdd(T, F, _R).

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

labelling(Vars, xrobdd(T, F, R), T `intersect` Vars `union` TrueVars,
		F `intersect` Vars `union` FalseVars) :-
	labelling(Vars `difference` T `difference` F, R, TrueVars, FalseVars).

minimal_model(Vars, xrobdd(T, F, R), T `intersect` Vars `union` TrueVars,
		F `intersect` Vars `union` FalseVars) :-
	minimal_model(Vars `difference` T `difference` F, R,
		TrueVars, FalseVars).

%-----------------------------------------------------------------------------%

:- func normalise(tfr(T)::di_tfr) = (tfr(T)::uo_tfr) is det.

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

:- func x(tfr(T)::di_tfr, robdd(T)::in) = (tfr(T)::uo_tfr) is det.

x(X, R) = X * xrobdd(init, init, R).
