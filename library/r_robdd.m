%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: xrobdd.m.
% Main author: dmo
% Stability: low

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module xrobdd.

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
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module robdd, sparse_bitset.

% T - true vars, F - False Vars, E - equivalent vars, N -
% non-equivalent vars, R - ROBDD.
%
% Combinations to try:
%	R	(straight ROBDD)
%	TER	(Peter Schachte's extension)
%	TFENR	(Everything)

:- type xrobdd(T)
	--->	xrobdd(
			robdd :: robdd(T)
		).

one = xrobdd(one).

zero = xrobdd(zero).

X * Y = xrobdd(X ^ robdd * Y ^ robdd).

X + Y = xrobdd(X ^ robdd + Y ^ robdd).

var_entailed(X, V) :-
	var_entailed(X ^ robdd, V).

vars_entailed(X) =
	vars_entailed(X ^ robdd).

vars_disentailed(X) = 
	vars_disentailed(X ^ robdd).

restrict(V, F) =
	xrobdd(restrict(V, F ^ robdd)).

restrict_threshold(V, F) =
	xrobdd(restrict_threshold(V, F ^ robdd)).

% XXX should be able to implement var and not_var more efficiently.
var(V, X) = X ^ robdd :=
	X ^ robdd * var(V).

not_var(V, X) = X ^ robdd :=
	X ^ robdd * not_var(V).

eq_vars(VarA, VarB, X) = X ^ robdd :=
	X ^ robdd * eq_vars(VarA, VarB).

neq_vars(VarA, VarB, X) = X ^ robdd :=
	X ^ robdd * neq_vars(VarA, VarB).

imp_vars(VarA, VarB, X) = X ^ robdd :=
	X ^ robdd * imp_vars(VarA, VarB).

conj_vars(Vars, X) = X ^ robdd :=
	X ^ robdd * conj_vars(Vars).

disj_vars(Vars, X) = X ^ robdd :=
	X ^ robdd * disj_vars(Vars).

at_most_one_of(Vars, X) = X ^ robdd :=
	X ^ robdd * at_most_one_of(Vars).

not_both(VarA, VarB, X) = X ^ robdd :=
	X ^ robdd * ~(var(VarA) * var(VarB)).

io_constraint(V_in, V_out, V_, X) = X ^ robdd :=
	X ^ robdd * 
		( var(V_out) =:= var(V_in) + var(V_) ) *
		( ~(var(V_in) * var(V_)) ).

disj_vars_eq(Vars, Var, X) = X ^ robdd :=
	X ^ robdd * ( disj_vars(Vars) =:= var(Var) ).

var_restrict_true(V, X) = X ^ robdd :=
	var_restrict_true(V, X ^ robdd).

var_restrict_false(V, X) = X ^ robdd :=
	var_restrict_false(V, X ^ robdd).

restrict_filter(P, X) = X ^ robdd :=
	restrict_filter(P, X ^ robdd).

labelling(Vars, X, TrueVars, FalseVars) :-
	labelling(Vars, X ^ robdd, TrueVars, FalseVars).

minimal_model(Vars, X, TrueVars, FalseVars) :-
	minimal_model(Vars, X ^ robdd, TrueVars, FalseVars).

%-----------------------------------------------------------------------------%

