%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: robdd.m.
% Main author: dmo
% Stability: low

% This module contains a Mercury interface to Peter Schachte's C
% implementation of Reduced Ordered Binary Decision Diagrams (ROBDDs).
% ROBDDs are an efficent representation for Boolean constraints.

% Boolean variables are represented using the type var(T) from the
% `term' library module (see the `term' module documentation for
% more information).

% Example usage:
%	% Create some variables.
% 	term__init_var_supply(VarSupply0),
%	term__create_var(VarSupply0, A, VarSupply1),
%	term__create_var(VarSupply1, B, VarSupply2),
%	term__create_var(VarSupply2, C, VarSupply),
%	
%	% Create some ROBDDs.
%	R1 = ( var(A) =:= var(B) * (~var(C)) ),
%	R2 = ( var(A) =< var(B) ),
%	
%	% Test if R1 entails R2 (should succeed).
%	R1 `entails` R2,
%
%	% Project R1 onto A and B.
%	R3 = restrict(C, R1),
%
%	% Test R2 and R3 for equivalence (should succeed).
%	R2 = R3.

% ROBDDs are implemented so that two ROBDDs, R1 and R2, represent
% the same Boolean constraint if and only iff `R1 = R2'.  Checking
% equivalence of ROBDDs is fast since it involves only a single
% pointer comparison.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module robdd.

:- interface.

:- import_module term, io, sparse_bitset, list, map.

:- type robdd(T).
:- type robdd == robdd(generic).

:- type vars(T) == sparse_bitset(var(T)). % XXX experiment with different reps.

:- func empty_vars_set = vars(T).

% Constants.
:- func one = robdd(T).
:- func zero = robdd(T).

% If-then-else.
:- func ite(robdd(T), robdd(T), robdd(T)) = robdd(T).

% The functions *, +, =<, =:=, =\= and ~ correspond to the names
% used in the SICStus clp(B) library.

% Conjunction.
:- func robdd(T) * robdd(T) = robdd(T).

% Disjunction.
:- func robdd(T) + robdd(T) = robdd(T).

% Implication.
:- func (robdd(T) =< robdd(T)) = robdd(T).

% Equivalence.
:- func (robdd(T) =:= robdd(T)) = robdd(T).

% Non-equivalence (XOR).
:- func (robdd(T) =\= robdd(T)) = robdd(T).

% Negation.
:- func (~ robdd(T)) = robdd(T).

%-----------------------------------------------------------------------------%

	% var(X) is the ROBDD that is true iff X is true.
:- func var(var(T)) = robdd(T).

% The following functions operate on individual variables and are
% more efficient than the more generic versions above that take
% ROBDDs as input.

	% not_var(V) = ~ var(V).
:- func not_var(var(T)) = robdd(T).

	% ite_var(V, FA, FB) = ite(var(V), FA, FB).
:- func ite_var(var(T), robdd(T), robdd(T)) = robdd(T).

	% eq_vars(X, Y) = ( var(X) =:= var(Y) ).
:- func eq_vars(var(T), var(T)) = robdd(T).

	% neq_vars(X, Y) = ( var(X) =\= var(Y) ).
:- func neq_vars(var(T), var(T)) = robdd(T).

	% imp_vars(X, Y) = ( var(X) =< var(Y) ).
:- func imp_vars(var(T), var(T)) = robdd(T).

	% conj_vars([V1, V2, ..., Vn]) = var(V1) * var(V2) * ... * var(Vn).
:- func conj_vars(vars(T)) = robdd(T).

	% conj_not_vars([V1, V2, ..., Vn]) = not_var(V1) * ... * not_var(Vn).
:- func conj_not_vars(vars(T)) = robdd(T).

	% disj_vars([V1, V2, ..., Vn]) = var(V1) + var(V2) + ... + var(Vn).
:- func disj_vars(vars(T)) = robdd(T).

	% at_most_one_of(Vs) = 
	%	foreach pair Vi, Vj in Vs where Vi \= Vj. ~(var(Vi) * var(Vj)).
:- func at_most_one_of(vars(T)) = robdd(T).

	% var_restrict_true(V, F) = restrict(V, F * var(V)).
:- func var_restrict_true(var(T), robdd(T)) = robdd(T).

	% var_restrict_false(V, F) = restrict(V, F * not_var(V)).
:- func var_restrict_false(var(T), robdd(T)) = robdd(T).

%-----------------------------------------------------------------------------%

	% X `entails` Y
	% 	Succeed iff X entails Y.
	%	Does not create any new ROBDD nodes.
:- pred robdd(T) `entails` robdd(T).
:- mode in `entails` in is semidet.

	% Succeed iff the var is entailed by the ROBDD.
:- pred var_entailed(robdd(T)::in, var(T)::in) is semidet.

	% Return the set of vars entailed by the ROBDD.
:- func vars_entailed(robdd(T)) = vars_entailed_result(T).

	% Return the set of vars disentailed by the ROBDD.
:- func vars_disentailed(robdd(T)) = vars_entailed_result(T).

	% definite_vars(R, T, F) <=> T = vars_entailed(R) /\
	% 			     F = vars_disentailed(R)
:- pred definite_vars(robdd(T)::in, vars_entailed_result(T)::out,
		vars_entailed_result(T)::out) is det.

:- func equivalent_vars(robdd(T)) = equivalent_result(T).

:- type entailment_result(T)
	--->	all_vars
	;	some_vars(vars :: T).

:- type vars_entailed_result(T) == entailment_result(vars(T)).

:- type equivalent_result(T) == entailment_result(map(var(T), var(T))).

	% Existentially quantify away the var in the ROBDD.
:- func restrict(var(T), robdd(T)) = robdd(T).

	% Existentially quantify away all vars greater than the specified var.
:- func restrict_threshold(var(T), robdd(T)) = robdd(T).

	% Existentially quantify away all vars for which the predicate fails.
:- func restrict_filter(pred(var(T)), robdd(T)) = robdd(T).
:- mode restrict_filter(pred(in) is semidet, in) = out is det.

	% restrict_filter(P, D, R)
	%	Existentially quantify away all vars for which P fails,
	%	except, if D fails for a var, do not existentially quantify away
	%	that var on any greater than it.  I.e D can be used to set a
	%	depth limit on the existential quantification.
:- func restrict_filter(pred(var(T)), pred(var(T)), robdd(T)) = robdd(T).
:- mode restrict_filter(pred(in) is semidet, pred(in) is semidet, in) = out
		is det.

:- func restrict_true_false_vars(vars(T), vars(T), robdd(T)) = robdd(T).

	% Given a leader map, remove all but the least variable in each
	% equivalence class from the ROBDD.
	% Note: the leader map MUST correspond to actual equivalences within the
	% ROBDD, (e.g. have been produced by 'equivalent_vars/1').
:- func squeeze_equiv(map(var(T), var(T)), robdd(T)) = robdd(T).

:- func make_equiv(map(var(T), var(T))) = robdd(T).

:- func expand_equiv(map(var(T), var(T)), robdd(T)) = robdd(T).

%-----------------------------------------------------------------------------%

	% Print out the ROBDD in disjunctive form.
:- pred print_robdd(robdd(T)::in, io__state::di, io__state::uo) is det.

	% robdd_to_dot(ROBDD, WriteVar, FileName, IO0, IO).
	%	Output the ROBDD in a format that can be processed by the 
	%	graph-drawing program `dot'.
:- pred robdd_to_dot(robdd(T)::in, write_var(T)::in(write_var),
		string::in, io__state::di, io__state::uo) is det.

	% robdd_to_dot(ROBDD, WriteVar, IO0, IO).
	%	Output the ROBDD in a format that can be processed by the 
	%	graph-drawing program `dot'.
:- pred robdd_to_dot(robdd(T)::in, write_var(T)::in(write_var),
		io__state::di, io__state::uo) is det.

:- type write_var(T) == pred(var(T), io__state, io__state).
:- inst write_var = (pred(in, di, uo) is det).

	% Apply the variable substitution to the ROBDD.
:- func rename_vars(func(var(T)) = var(T), robdd(T)) = robdd(T).

	% Succeed iff ROBDD = one or ROBDD = zero.
:- pred is_terminal(robdd(T)::in) is semidet.

	% Output the number of nodes and the depth of the ROBDD.
:- pred size(robdd(T)::in, int::out, int::out) is det.

	% Output the number of nodes, the depth of the ROBDD and the
	% variables it contains.
:- pred size(robdd(T)::in, int::out, int::out, list(var(T))::out) is det.

	% Succeed iff the var is constrained by the ROBDD.
:- pred var_is_constrained(robdd(T)::in, var(T)::in) is semidet.

	% Succeed iff all the vars in the set are constrained by the ROBDD.
:- pred vars_are_constrained(robdd(T)::in, vars(T)::in) is semidet.

%-----------------------------------------------------------------------------%

	% labelling(Vars, ROBDD, TrueVars, FalseVars)
	%	Takes a set of Vars and an ROBDD and returns a value assignment
	%	for those Vars that is a model of the Boolean function
	%	represented by the ROBDD.
	%	The value assignment is returned in the two sets TrueVars (set
	%	of variables assigned the value 1) and FalseVars (set of
	%	variables assigned the value 0).
	%
	% XXX should try using sparse_bitset here.
:- pred labelling(vars(T)::in, robdd(T)::in, vars(T)::out,
		vars(T)::out) is nondet.

	% minimal_model(Vars, ROBDD, TrueVars, FalseVars)
	%	Takes a set of Vars and an ROBDD and returns a value assignment
	%	for those Vars that is a minimal model of the Boolean function
	%	represented by the ROBDD.
	%	The value assignment is returned in the two sets TrueVars (set
	%	of variables assigned the value 1) and FalseVars (set of
	%	variables assigned the value 0).
	%
	% XXX should try using sparse_bitset here.
:- pred minimal_model(vars(T)::in, robdd(T)::in, vars(T)::out,
		vars(T)::out) is nondet.

%-----------------------------------------------------------------------------%

	% Zero the internal caches used for ROBDD operations.
	% This allows nodes in the caches to be garbage-collected.
	% This operation is pure and does not perform any I/O, but we need
	% to either declare it impure or pass io__states to ensure that
	% the compiler won't try to optimise away the call.

:- pred clear_caches(io__state::di, io__state::uo) is det.

:- impure pred clear_caches is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module set_unordlist, list, string, map, bool, set_bbbtree, int.
:- import_module multi_map, require.
:- import_module hash_table.

:- type robdd(T) ---> robdd(int).
% :- type robdd(T) ---> robdd(c_pointer).
	% Can't use a c_pointer since we want to memo ROBDD operations and
	% pragma memo does not support c_pointers.

empty_vars_set = sparse_bitset__init.

:- pragma c_header_code("
#define USE_ITE_CONSTANT
#include ""bryant.h""
").

:- pragma c_code(one = (F::out), [will_not_call_mercury],
		"F = (Word) trueVar();").

:- pragma c_code(zero = (F::out), [will_not_call_mercury],
		"F = (Word) falseVar();").

:- pragma c_code(var(V::in) = (F::out), [will_not_call_mercury],
		"F = (Word) variableRep(V);").

:- pragma c_code(ite(F::in, G::in, H::in) = (ITE::out),
		[will_not_call_mercury],
		"ITE = (Word) ite((node *) F, (node *) G, (node *) H);").

:- pragma c_code(ite_var(V::in, G::in, H::in) = (ITE::out), 
		[will_not_call_mercury],
		"ITE = (Word) ite_var(V, (node *) G, (node *) H);").
X * Y = R :-
	R = glb(X, Y),

	% XXX debugging code.
	( R = zero ->
		report_zero_constraint
	;
		true
	).

% XXX :- pragma c_code((X::in) * (Y::in) = (F::out), [will_not_call_mercury],
:- func glb(robdd(T), robdd(T)) = robdd(T).
:- pragma c_code(glb(X::in, Y::in) = (F::out), [will_not_call_mercury],
		"F = (Word) glb((node *) X, (node *) Y);").

% XXX
:- pred report_zero_constraint is det.
:- pragma c_code(report_zero_constraint, [will_not_call_mercury],
		"fprintf(stderr, ""Zero constraint!!!\\n"");").

:- pragma c_code((X::in) + (Y::in) = (F::out), [will_not_call_mercury],
		"F = (Word) lub((node *) X, (node *) Y);").

:- pragma c_code(((X::in) =< (Y::in)) = (F::out), [will_not_call_mercury],
		"F = (Word) implies((node *) X, (node *) Y);").

(F =:= G) = ite(F, G, ~G).

(F =\= G) = ite(F, ~G, G).

(~F) = ite(F, zero, one).

:- pragma c_code(entails(X::in, Y::in), [will_not_call_mercury],
	"SUCCESS_INDICATOR =
		(ite_constant((node *) X, (node *) Y, one) == one);").

:- pragma c_code(var_entailed(F::in, V::in), [will_not_call_mercury],
		"SUCCESS_INDICATOR = var_entailed((node *) F, (int) V);").

:- pragma memo(vars_entailed/1).

vars_entailed(R) =
	( R = one ->
		some_vars(empty_vars_set)
	; R = zero ->
		all_vars
	;
		(
			R^fa = zero
		->
			(vars_entailed(R^tr) `intersection` vars_entailed(R^fa))
				`insert` R^value
		;
			vars_entailed(R^tr) `intersection` vars_entailed(R^fa)
		)
	).

:- pragma memo(vars_disentailed/1).

vars_disentailed(R) =
	( R = one ->
		some_vars(empty_vars_set)
	; R = zero ->
		all_vars
	;
		(
			R^tr = zero
		->
			(vars_disentailed(R^tr) `intersection`
				vars_disentailed(R^fa)) `insert` R^value
		;
			vars_disentailed(R^tr) `intersection`
				vars_disentailed(R^fa)
		)
	).

:- pragma memo(definite_vars/3).

definite_vars(R, T, F) :-
	( R = one ->
		T = some_vars(empty_vars_set),
		F = some_vars(empty_vars_set)
	; R = zero ->
		T = all_vars,
		F = all_vars
	;
		definite_vars(R^tr, T_tr, F_tr),
		definite_vars(R^fa, T_fa, F_fa),
		T0 = T_tr `intersection` T_fa,
		F0 = F_tr `intersection` F_fa,
		( R^fa = zero ->
			T = T0 `insert` R^value,
			F = F0
		; R^tr = zero ->
			T = T0,
			F = F0 `insert` R^value
		;
			T = T0,
			F = F0
		)
	).

equivalent_vars(R) = rev_map(equivalent_vars_2(R)).

:- type equivalent_vars_map(T) ---> equivalent_vars_map(map(var(T), vars(T))).

:- func equivalent_vars_2(robdd(T)) = entailment_result(equivalent_vars_map(T)).

:- pragma memo(equivalent_vars_2/1).

equivalent_vars_2(R) = EQ :-
	( R = one ->
		EQ = some_vars(equivalent_vars_map(map__init))
	; R = zero ->
		EQ = all_vars
	;
		EQVars = vars_entailed(R ^ tr) `intersection`
				vars_disentailed(R ^ fa),
		EQ0 = equivalent_vars_2(R ^ tr) `intersection`
				equivalent_vars_2(R ^ fa),
		(
		    EQVars = all_vars,
		    error("equivalent_vars: unexpected result")
		    % If this condition occurs it means the ROBDD invariants
		    % have been violated somewhere since both branches of R
		    % must have been zero.
		;
		    EQVars = some_vars(Vars),
		    ( empty(Vars) ->
			EQ = EQ0
		    ;
			(
			    EQ0 = all_vars,
			    error("equivalent_vars: unexpected result")
			    % If this condition occurs it means the ROBDD
			    % invariants have been violated somewhere since both
			    % branches of R must have been zero.
			;
			    EQ0 = some_vars(equivalent_vars_map(M0)),
			    map__det_insert(M0, R ^ value, Vars, M),
			    EQ = some_vars(equivalent_vars_map(M))
			)
		    )
		)
	).

:- func rev_map(entailment_result(equivalent_vars_map(T))) =
		equivalent_result(T).

rev_map(all_vars) = all_vars.
rev_map(some_vars(equivalent_vars_map(EQ0))) = some_vars(EQ) :-
	map__foldl2(
		( pred(V::in, Vs::in, Seen0::in, Seen::out, in, out) is det -->
		    ( { Seen0 `contains` V } ->
			{ Seen = Seen0 }
		    ;
			^ elem(V) := V,
			sparse_bitset__foldl((pred(Ve::in, in, out) is det -->
				^ elem(Ve) := V
			    ), Vs),
			{ Seen = Seen0 `sparse_bitset__union` Vs }
		    )
		), EQ0, sparse_bitset__init, _, map__init, EQ).

:- typeclass intersectable(T) where [
	func T `intersection` T = T
].

:- instance intersectable(sparse_bitset(T)) where [
	func(intersection/2) is sparse_bitset__intersect
].

:- instance intersectable(entailment_result(T)) <= intersectable(T) where [
	( all_vars `intersection` R = R ),
	( some_vars(Vs) `intersection` all_vars = some_vars(Vs) ),
	( some_vars(Vs0) `intersection` some_vars(Vs1) =
		some_vars(Vs0 `intersection` Vs1) )
].

:- instance intersectable(equivalent_vars_map(T)) where [
	( equivalent_vars_map(MapA) `intersection` equivalent_vars_map(MapB) =
		equivalent_vars_map(map__foldl((func(V, VsA, M) =
			( Vs = VsA `intersect` (MapB ^ elem(V)) ->
				( empty(Vs) ->
					M
				;
					M ^ elem(V) := Vs
				)
			;
				M
			)), MapA, map__init))
	)
].

:- func vars_entailed_result(T) `insert` var(T) = vars_entailed_result(T).

all_vars `insert` _ = all_vars.
some_vars(Vs) `insert` V = some_vars(Vs `insert` V).

% Access to the struct members.
% WARNING!  The functions are unsafe.  You must not call these functions
% on the terminal robdds (i.e. `zero' and `one').
:- func value(robdd(T)) = var(T).
:- func tr(robdd(T)) = robdd(T).
:- func fa(robdd(T)) = robdd(T).

:- pragma c_code(value(F::in) = (Value::out), [will_not_call_mercury],
		"Value = (Word) ((node *) F)->value;").
:- pragma c_code(tr(F::in) = (Tr::out), [will_not_call_mercury],
		"Tr = (Word) ((node *) F)->tr;").
:- pragma c_code(fa(F::in) = (Fa::out), [will_not_call_mercury],
		"Fa = (Word) ((node *) F)->fa;").

/*
:- pragma c_code(print_robdd(F::in, IO0::di, IO::uo), [will_not_call_mercury],
		"printOut((node *) F); update_io(IO0, IO)").
*/

print_robdd(F) -->
	( { F = one } ->
		io__write_string("TRUE\n")
	; { F = zero } ->
		io__write_string("FALSE\n")
	;
		{ init(Trues) },
		{ init(Falses) },
		print_robdd_2(F, Trues, Falses)
	).

:- pred print_robdd_2(robdd(T)::in, set_unordlist(var(T))::in,
		set_unordlist(var(T))::in, io__state::di, io__state::uo) is det.

print_robdd_2(F, Trues, Falses) -->
	( { F = one } ->
		{ All = to_sorted_list(Trues `union` Falses) },
		io__write_string("("),
		list__foldl((pred(Var::in, di, uo) is det -->
			{ Var `set_unordlist__member` Trues ->
				C = ' '
			;
				C = ('~')
			},
			{ term__var_to_int(Var, N) },
			io__format(" %c%02d", [c(C), i(N)])
		), All),
		io__write_string(")\n")
	; { F \= zero } ->
		print_robdd_2(F^tr, Trues `insert` F^value, Falses),
		print_robdd_2(F^fa, Trues, Falses `insert` F^value)
	;
		% Don't do anything for zero terminal
		[]
	).

:- pragma c_code(restrict(V::in, F::in) = (R::out), [will_not_call_mercury],
		"R = (Word) restrict(V, (node *) F);").

:- pragma c_code(restrict_threshold(V::in, F::in) = (R::out),
		[will_not_call_mercury],
		"R = (Word) restrictThresh(V, (node *) F);").

rename_vars(Subst, F) = 
	( is_terminal(F) ->
		F
	;
		ite(var(Subst(F^value)),
			rename_vars(Subst, F^tr),
			rename_vars(Subst, F^fa))
	).

% make_node(Var, Then, Else).
% The make_node() function.  WARNING!! If you use this function you are
% responsible for making sure that the ROBDD invariant holds that all the
% variables in both the Then and Else sub graphs are > Var.

:- func make_node(var(T), robdd(T), robdd(T)) = robdd(T).
:- pragma c_code(make_node(Var::in, Then::in, Else::in) = (Node::out),
		[will_not_call_mercury],
	"Node = (Word) make_node((int) Var, (node *) Then, (node *) Else);").


not_var(V) = make_node(V, zero, one).

eq_vars(VarA, VarB) = F :-
	compare(R, VarA, VarB),
	(
		R = (=),
		F = one
	;
		R = (<),
		F = make_node(VarA, var(VarB), not_var(VarB))
	;
		R = (>),
		F = make_node(VarB, var(VarA), not_var(VarA))
	).

neq_vars(VarA, VarB) = F :-
	compare(R, VarA, VarB),
	(
		R = (=),
		F = zero
	;
		R = (<),
		F = make_node(VarA, not_var(VarB), var(VarB))
	;
		R = (>),
		F = make_node(VarB, not_var(VarA), var(VarA))
	).

imp_vars(VarA, VarB) = F :-
	compare(R, VarA, VarB),
	(
		R = (=),
		F = one
	;
		R = (<),
		F = make_node(VarA, var(VarB), one)
	;
		R = (>),
		F = make_node(VarB, one, not_var(VarA))
	).

conj_vars(Vars) = foldr(func(V, R) = make_node(V, R, zero), Vars, one).

conj_not_vars(Vars) = foldr(func(V, R) = make_node(V, zero, R), Vars, one).

disj_vars(Vars) = foldr(func(V, R) = make_node(V, one, R), Vars, zero).

at_most_one_of(Vars) = at_most_one_of_2(Vars, one, one).

:- func at_most_one_of_2(vars(T), robdd(T), robdd(T)) = robdd(T).

at_most_one_of_2(Vars, OneOf0, NoneOf0) = R :-
	list__foldl2(
		(pred(V::in, One0::in, One::out, None0::in, None::out) is det :-
			None = make_node(V, zero, None0),
			One = make_node(V, None0, One0)
		), list__reverse(to_sorted_list(Vars)), 
		OneOf0, R, NoneOf0, _).

:- pragma memo(var_restrict_true/2).

var_restrict_true(V, F0) = F :-
	( is_terminal(F0) ->
		F = F0
	;
		compare(R, F0^value, V),
		(
			R = (<),
			F = make_node(F0^value,
				var_restrict_true(V, F0^tr),
				var_restrict_true(V, F0^fa))
		;
			R = (=),
			F = F0^tr
		;
			R = (>),
			F = F0
		)
	).

:- pragma memo(var_restrict_false/2).

var_restrict_false(V, F0) = F :-
	( is_terminal(F0) ->
		F = F0
	;
		compare(R, F0^value, V),
		(
			R = (<),
			F = make_node(F0^value,
				var_restrict_false(V, F0^tr),
				var_restrict_false(V, F0^fa))
		;
			R = (=),
			F = F0^fa
		;
			R = (>),
			F = F0
		)
	).

%/*
restrict_true_false_vars(TrueVars, FalseVars, R0) = R :-
    size(R0, _Nodes, _Depth), % XXX
	P = (pred(V::in, di, uo) is det --> io__write_int(var_to_int(V))), % XXX
	unsafe_perform_io(robdd_to_dot(R0, P, "rtf.dot")), % XXX
	restrict_true_false_vars_2(TrueVars, FalseVars, R0, R).

:- pred restrict_true_false_vars_2(vars(T)::in, vars(T)::in,
	robdd(T)::in, robdd(T)::out) is det.

%:- pragma memo(restrict_true_false_vars_2/4).

restrict_true_false_vars_2(TrueVars0, FalseVars0, R0, R) :-
	( is_terminal(R0) ->
	    R = R0
	; empty(TrueVars0), empty(FalseVars0) ->
	    R = R0
	;	
	    Var = R0 ^ value,
	    TrueVars = TrueVars0 `remove_leq` Var,
	    FalseVars = FalseVars0 `remove_leq` Var,
	    ( TrueVars0 `contains` Var ->
		restrict_true_false_vars_2(TrueVars, FalseVars, R0 ^ tr, R)
	    ; FalseVars0 `contains` Var ->
		restrict_true_false_vars_2(TrueVars, FalseVars, R0 ^ fa, R)
	    ;
		restrict_true_false_vars_2(TrueVars, FalseVars, R0 ^ tr, R_tr),
		restrict_true_false_vars_2(TrueVars, FalseVars, R0 ^ fa, R_fa),
		R = make_node(R0 ^ value, R_tr, R_fa)
	    )
	).
%*/
/*
restrict_true_false_vars(TrueVars, FalseVars, R0) = R :-
	restrict_true_false_vars_2(TrueVars, FalseVars, R0, R,
		hash_table__new(robdd_double_hash, 12, 0.9), _).

:- pred restrict_true_false_vars_2(vars(T)::in, vars(T)::in,
	robdd(T)::in, robdd(T)::out,
	hash_table(robdd(T), robdd(T))::hash_table_di,
	hash_table(robdd(T), robdd(T))::hash_table_uo) is det.

restrict_true_false_vars_2(TrueVars0, FalseVars0, R0, R, Seen0, Seen) :-
	( is_terminal(R0) ->
		R = R0,
		Seen = Seen0
	; empty(TrueVars0), empty(FalseVars0) ->
		R = R0,
		Seen = Seen0
	; search(Seen0, R0, R1) ->
		R = R1,
		Seen = Seen0
	;	
		Var = R0 ^ value,
		TrueVars = TrueVars0 `remove_leq` Var,
		FalseVars = FalseVars0 `remove_leq` Var,
		( TrueVars0 `contains` Var ->
			restrict_true_false_vars_2(TrueVars, FalseVars,
				R0 ^ tr, R, Seen0, Seen2)
		; FalseVars0 `contains` Var ->
			restrict_true_false_vars_2(TrueVars, FalseVars,
				R0 ^ fa, R, Seen0, Seen2)
		;
			restrict_true_false_vars_2(TrueVars, FalseVars,
				R0 ^ tr, R_tr, Seen0, Seen1),
			restrict_true_false_vars_2(TrueVars, FalseVars,
				R0 ^ fa, R_fa, Seen1, Seen2),
			R = make_node(R0 ^ value, R_tr, R_fa)
		),
		Seen = det_insert(Seen2, R0, R)
	).
*/

:- pred robdd_double_hash(robdd(T)::in, int::out, int::out) is det.

robdd_double_hash(R, H1, H2) :-
	int_double_hash(node_num(R), H1, H2).

restrict_filter(P, F0) =
	restrict_filter(P, (pred(_::in) is semidet :- true), F0).

restrict_filter(P, D, F0) = F :-
	filter_2(P, D, F0, F, map__init, _, map__init, _).

:- type robdd_cache(T) == map(robdd(T), robdd(T)).
:- type var_cache(T) == map(var(T), bool).

:- pred filter_2(pred(var(T)), pred(var(T)), robdd(T), robdd(T),
	var_cache(T), var_cache(T), robdd_cache(T), robdd_cache(T)).
:- mode filter_2(pred(in) is semidet, pred(in) is semidet, in, out, in, out,
	in, out) is det.

filter_2(P, D, F0, F, SeenVars0, SeenVars, SeenNodes0, SeenNodes) :-
	( is_terminal(F0) ->
		F = F0,
		SeenVars = SeenVars0,
		SeenNodes = SeenNodes0
	; \+ D(F0^value) ->
		F = F0,
		SeenVars = SeenVars0,
		SeenNodes = SeenNodes0
	; map__search(SeenNodes0, F0, F1) ->
		F = F1,
		SeenVars = SeenVars0,
		SeenNodes = SeenNodes0
	;
		filter_2(P, D, F0^tr, Ftrue, SeenVars0, SeenVars1, SeenNodes0,
			SeenNodes1),
		filter_2(P, D, F0^fa, Ffalse, SeenVars1, SeenVars2, SeenNodes1,
			SeenNodes2),
		V = F0^value,
		( map__search(SeenVars0, V, SeenF) ->
			SeenVars = SeenVars2,
			(
				SeenF = yes,
				F = make_node(V, Ftrue, Ffalse)
			;
				SeenF = no,
				F = Ftrue + Ffalse
			)
		; P(V) ->
			F = make_node(V, Ftrue, Ffalse),
			map__det_insert(SeenVars2, V, yes, SeenVars)
		;
			F = Ftrue + Ffalse,
			map__det_insert(SeenVars2, V, no, SeenVars)
		),
		map__det_insert(SeenNodes2, F0, F, SeenNodes)
	).

squeeze_equiv(LeaderMap, R0) =
	( Max = map__max_key(LeaderMap) ->
		restrict_filter(
			( pred(V::in) is semidet :-
				map__search(LeaderMap, V, L) => L = V
			),
			( pred(V::in) is semidet :-
				\+ compare(>, V, Max)
			), R0)
	;
		R0
	).

make_equiv(LeaderMap) =
	make_equiv_2(map__sorted_keys(LeaderMap), LeaderMap, init).

:- func make_equiv_2(list(var(T)), map(var(T), var(T)), vars(T)) = robdd(T).

make_equiv_2([], _, _) = one.
make_equiv_2([V | Vs], LM, Trues) =
	( L = V ->
		make_node(V, make_equiv_2(Vs, LM, Trues `insert` V),
			make_equiv_2(Vs, LM, Trues))
	; Trues `contains` L ->
		make_node(V, make_equiv_2(Vs, LM, Trues), zero)
	;
		make_node(V, zero, make_equiv_2(Vs, LM, Trues))
	) :-
	L = LM ^ det_elem(V).

expand_equiv(LeaderMap, R) =
	expand_equiv_2(map__sorted_keys(LeaderMap), LeaderMap, init, R).

:- func expand_equiv_2(list(var(T)), map(var(T), var(T)), vars(T), robdd(T)) =
		robdd(T).

expand_equiv_2([], _, _, R) = R.
expand_equiv_2([V | Vs], LM, Trues, R) =
	( R = one ->
		make_equiv_2([V | Vs], LM, Trues)
	; R = zero ->
		zero
	; compare((<), R ^ value, V) ->
		make_node(R ^ value,
			expand_equiv_2([V | Vs], LM, Trues, R ^ tr),
			expand_equiv_2([V | Vs], LM, Trues, R ^ fa))
	; compare((<), V, R ^ value) ->
		( L = V ->
			make_node(V,
				expand_equiv_2(Vs, LM, Trues `insert` V, R),
				expand_equiv_2(Vs, LM, Trues, R))
		; Trues `contains` L ->
			make_node(V, expand_equiv_2(Vs, LM, Trues, R), zero)
		;
			make_node(V, zero, expand_equiv_2(Vs, LM, Trues, R))
		)
	; L = V ->
		make_node(V,
			expand_equiv_2(Vs, LM, Trues `insert` V, R ^ tr),
			expand_equiv_2(Vs, LM, Trues, R ^ fa))
	; Trues `contains` L ->
		make_node(V, expand_equiv_2(Vs, LM, Trues, R ^ tr), zero)
	;
		make_node(V, zero, expand_equiv_2(Vs, LM, Trues, R ^ fa))
	) :-
	L = LM ^ det_elem(V).

:- pragma c_code(is_terminal(F::in), [will_not_call_mercury, thread_safe],
	"SUCCESS_INDICATOR = IS_TERMINAL(F);").

size(F, Nodes, Depth) :-
	size(F, Nodes, Depth, _).

size(F, Nodes, Depth, Vars) :-
	size_2(F, 0, Nodes, 0, Depth, 0, set_bbbtree__init, Seen),
	Vars = sort_and_remove_dups(list__map(value, to_sorted_list(Seen))).

	% XXX should see if sparse_bitset is more efficient than set_bbbtree.
:- pred size_2(robdd(T)::in, int::in, int::out, int::in, int::out, int::in,
		set_bbbtree(robdd(T))::in, set_bbbtree(robdd(T))::out) is det.

size_2(F, Nodes0, Nodes, Depth0, Depth, Val0, Seen0, Seen) :-
	
	( is_terminal(F) ->
		Nodes = Nodes0, Depth = Depth0, Seen = Seen0
	; term__var_to_int(F^value) =< Val0 ->
		error("robdd invariant broken (possible loop)")
	; F `member` Seen0 ->
		Nodes = Nodes0, Depth = Depth0, Seen = Seen0
	;
		Val = term__var_to_int(F^value),
		size_2(F^tr, Nodes0+1, Nodes1, Depth0, Depth1, Val,
			Seen0, Seen1),
		size_2(F^fa, Nodes1, Nodes, Depth0, Depth2, Val,
			Seen1, Seen2),
		max(Depth1, Depth2, Max),
		Depth = Max + 1,
		Seen = Seen2 `insert` F
	).

var_is_constrained(F, V) :-
	( is_terminal(F) ->
		fail
	;
		compare(R, F^value, V),
		(
			R = (<),
			( var_is_constrained(F^tr, V)
			; var_is_constrained(F^fa, V)
			)
		;
			R = (=)
		)
	).

vars_are_constrained(F, Vs) :-
	vars_are_constrained_2(F, to_sorted_list(Vs)).

:- pred vars_are_constrained_2(robdd(T)::in, list(var(T))::in) is semidet.

vars_are_constrained_2(_, []).
vars_are_constrained_2(F, Vs) :-
	Vs = [V | Vs1],
	( is_terminal(F) ->
		fail
	;
		compare(R, F^value, V),
		(
			R = (<),
			Vs2 = Vs
		;
			R = (=),
			Vs2 = Vs1
		),
		( vars_are_constrained_2(F^tr, Vs2)
		; vars_are_constrained_2(F^fa, Vs2)
		)
	).

robdd_to_dot(Robdd, WV, Filename) -->
	io__tell(Filename, Result),
	(
		{ Result = ok },
		robdd_to_dot(Robdd, WV),
		io__told
	;
		{ Result = error(Err) },
		io__stderr_stream(StdErr),
		io__nl(StdErr),
		io__write_string(StdErr, io__error_message(Err)),
		io__nl(StdErr)
	).

robdd_to_dot(Robdd, WV) -->
	io__write_string(
"digraph G{
	center=true;
	size=""7,11"";
	ordering=out;
	node [shape=record,height=.1];
"),
	{ multi_map__init(Ranks0) },
	robdd_to_dot_2(Robdd, WV, set_bbbtree__init, _, Ranks0, Ranks),
	map__foldl((pred(_::in, Nodes::in, di, uo) is det -->
		io__write_string("{rank = same; "),
		list__foldl((pred(Node::in, di, uo) is det -->
			io__format("%s; ", [s(node_name(Node))])), Nodes),
		io__write_string("}\n")
		), Ranks),
	io__write_string("}\n").

	% XXX should see if sparse_bitset is more efficient than set_bbbtree.
:- pred robdd_to_dot_2(robdd(T)::in, write_var(T)::in(write_var),
		set_bbbtree(robdd(T))::in, set_bbbtree(robdd(T))::out,
		multi_map(var(T), robdd(T))::in,
		multi_map(var(T), robdd(T))::out,
		io__state::di, io__state::uo) is det.

robdd_to_dot_2(Robdd, WV, Seen0, Seen, Ranks0, Ranks) -->
	( { is_terminal(Robdd) } ->
		{ Seen = Seen0 },
		{ Ranks = Ranks0 }
	; { Robdd `member` Seen0 } ->
		{ Seen = Seen0 },
		{ Ranks = Ranks0 }
	;
		robdd_to_dot_2(Robdd^tr, WV, Seen0, Seen1, Ranks0, Ranks1),
		robdd_to_dot_2(Robdd^fa, WV, Seen1, Seen2, Ranks1, Ranks2),
		write_node(Robdd, WV),
		write_edge(Robdd, Robdd^tr, yes),
		write_edge(Robdd, Robdd^fa, no),
		{ Seen = Seen2 `insert` Robdd },
		{ multi_map__set(Ranks2, Robdd^value, Robdd, Ranks) }
	).

:- pred write_node(robdd(T)::in, write_var(T)::in(write_var),
		io__state::di, io__state::uo) is det.

write_node(R, WV) -->
	io__format("%s [label=""<f0> %s|<f1> ",
		[s(node_name(R)), s(terminal_name(R^tr))]),
	WV(R^value),
	io__format("|<f2> %s", [s(terminal_name(R^fa))]),
	io__write_string("""];\n").

:- func node_name(robdd(T)) = string.

node_name(R) =
	( R = one ->
		"true"
	; R = zero ->
		"false"
	;
		string__format("node%d", [i(node_num(R))])
	).

:- func node_num(robdd(T)) = int.
:- pragma c_code(node_num(R::in) = (N::out), [will_not_call_mercury],
	"N = (Integer)R;\n").

:- func terminal_name(robdd(T)) = string.

terminal_name(R) =
	( R = zero ->
		"0"
	; R = one ->
		"1"
	;
		""
	).

:- pred write_edge(robdd(T)::in, robdd(T)::in, bool::in,
		io__state::di, io__state::uo) is det.

write_edge(R0, R1, Arc) -->
	( { is_terminal(R1) } ->
		[]
	;
		io__format("""%s"":%s -> ""%s"":f1 ;\n",
			[s(node_name(R0)), s(Arc = yes -> "f0" ; "f2"),
			s(node_name(R1))])
	).

labelling(Vars, R, TrueVars, FalseVars) :-
	labelling_2(to_sorted_list(Vars), R, empty_vars_set, TrueVars,
		empty_vars_set, FalseVars).

:- pred labelling_2(list(var(T))::in, robdd(T)::in, vars(T)::in,
		vars(T)::out, vars(T)::in, vars(T)::out) is nondet.

labelling_2([], _, TrueVars, TrueVars, FalseVars, FalseVars).
labelling_2([V | Vs], R0, TrueVars0, TrueVars, FalseVars0, FalseVars) :-
	R = var_restrict_false(V, R0),
	R \= zero,
	labelling_2(Vs, R, TrueVars0, TrueVars, FalseVars0 `insert` V,
		FalseVars).
labelling_2([V | Vs], R0, TrueVars0, TrueVars, FalseVars0, FalseVars) :-
	R = var_restrict_true(V, R0),
	R \= zero,
	labelling_2(Vs, R, TrueVars0 `insert` V, TrueVars, FalseVars0,
		FalseVars).

minimal_model(Vars, R, TrueVars, FalseVars) :-
	( empty(Vars) ->
		TrueVars = empty_vars_set,
		FalseVars = empty_vars_set
	;
		minimal_model_2(to_sorted_list(Vars), R, empty_vars_set,
			TrueVars0, empty_vars_set, FalseVars0),
		(
			TrueVars = TrueVars0,
			FalseVars = FalseVars0
		;
			minimal_model(Vars, R * (~conj_vars(TrueVars0)),
				TrueVars, FalseVars)
		)
	).

:- pred minimal_model_2(list(var(T))::in, robdd(T)::in, vars(T)::in,
		vars(T)::out, vars(T)::in, vars(T)::out) is semidet.

minimal_model_2([], _, TrueVars, TrueVars, FalseVars, FalseVars).
minimal_model_2([V | Vs], R0, TrueVars0, TrueVars, FalseVars0, FalseVars) :-
	R1 = var_restrict_false(V, R0),
	( R1 \= zero ->
		minimal_model_2(Vs, R1, TrueVars0, TrueVars,
			FalseVars0 `insert` V, FalseVars)
	;
		R2 = var_restrict_true(V, R0),
		R2 \= zero,
		minimal_model_2(Vs, R2, TrueVars0 `insert` V, TrueVars,
			FalseVars0, FalseVars)
	).

%-----------------------------------------------------------------------------%

:- pragma promise_pure(clear_caches/2).
clear_caches -->
	{ impure clear_caches }.

:- pragma c_code(clear_caches, [will_not_call_mercury], "init_caches();").

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

% XXX

:- pred unsafe_perform_io(pred(io__state, io__state)).
:- mode unsafe_perform_io(pred(di, uo) is det) is det.

:- pragma c_code(
unsafe_perform_io(P::(pred(di, uo) is det)),
	[may_call_mercury],
"{
	ML_lazy_io_call_io_pred_det(P);
}").

:- pred call_io_pred(pred(io__state, io__state), io__state, io__state).
:- mode call_io_pred(pred(di, uo) is det, di, uo) is det.

:- pragma export(call_io_pred(pred(di, uo) is det, di, uo),
		"ML_lazy_io_call_io_pred_det").

call_io_pred(P) --> P.

