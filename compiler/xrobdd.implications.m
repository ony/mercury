%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: xrobdd.implications.m.
% Main author: dmo

:- module implications.

:- interface.

:- import_module robdd, bool, term.
:- import_module xrobdd__equiv_vars.

:- type imp_vars(T).

:- func init_imp_vars = imp_vars(T).

:- pred normalise_true_false_implication_vars(bool::out, vars(T)::in,
	vars(T)::out, vars(T)::in, vars(T)::out, imp_vars(T)::in,
	imp_vars(T)::out) is det.

:- pred propagate_equivalences_into_implications(equiv_vars::in, bool::out,
	imp_vars(T)::in, imp_vars(T)::out) is semidet.

:- pred propagate_implications_into_equivalences(imp_vars(T)::in, bool::out,
	equiv_vars(T)::in, equiv_vars(T)::out) is semidet.

:- pred extract_implication_vars_from_robdd(bool::out, robdd(T)::in,
	robdd(T)::out, imp_vars(T)::in, imp_vars(T)::out) is det.

:- implementation.

:- type imp_vars(T)
	--->	imp_vars(
			imps :: imp_map(T),		%  K =>  V
			rev_imps ::imp_map(T),		% ~K => ~V
			dis_imps :: imp_map(T),		%  K => ~V
			rev_dis_imps :: imp_map(T)	% ~K =>  V
		).

:- type imp_map(T) == map(var(T), vars(T)).

% imp_map invariant:
%	forall IM : imp_map
%		forall K, Vs . (K -> Vs) in IM
%			forall V in Vs
%				K < V

init_imp_vars = imp_vars(init, init, init, init).

normalise_true_false_implication_vars(Changed, TrueVars0, TrueVars,
		FalseVars0, FalseVars, ImpVars0, ImpVars) :-
	(
	    empty(TrueVars0),
	    empty(FalseVars0)
	->
	    TrueVars = TrueVars0,
	    FalseVars = FalseVars0,
	    ImpVars = ImpVars0
	;
	    ImpVars0 = imp_vars(Imps0, RevImps0, DisImps0, RevDisImps0),
	    normalise_true_false_imp_map(no, Changed0, TrueVars0, TrueVars1,
		FalseVars0, FalseVars1, Imps0, Imps),
	    normalise_true_false_imp_map(no, Changed1, FalseVars1, FalseVars2,
		TrueVars1, TrueVars2, RevImps0, RevImps),
	    normalise_true_false_imp_map(yes, Changed2, FalseVars2, FalseVars3,
		TrueVars2, TrueVars3, DisImps0, DisImps),
	    normalise_true_false_imp_map(yes, Changed3, TrueVars3, TrueVars4,
		FalseVars3, FalseVars4, RevDisImps0, RevDisImps),
	    ImpVars4 = imp_vars(Imps4, RevImps4, DisImps4, RevDisImps4),
	    Changed = (Changed0 or Changed1 or Changed2 or Changed3),

	    ( Changed = yes ->
		normalise_true_false_implication_vars(_, TrueVars4, TrueVars,
		    FalseVars4, FalseVars, ImpVars4, ImpVars)
	    ;
		TrueVars = TrueVars4,
		FalseVars = FalseVars4,
		ImpVars = ImpVars4
	    )
	).

:- pred normalise_true_false_imp_map(bool::in, bool::out,
	vars(T)::in, vars(T)::out, vars(T)::in, vars(T)::out,
	imp_map(T)::in, imp_map(T)::out) is det.

normalise_true_false_imp_map(IsDisImp, Changed, TrueVars0, TrueVars,
		FalseVars0, FalseVars, ImpMap0, ImpMap) :-
	{TrueVars, FalseVars, ImpMap, Changed} = map__foldl(
	    ( func(V, Vs, {Ts0, Fs0, IMs0, C0}) = {Ts, Fs, IMs, C} :-
		(
		    ( DisImp = yes -> Fs0 ; Ts0 ) `contains` V
		->
		    Ts = Ts0 `union` Vs,
		    Fs = Fs0,
		    IMs = IMs0 `delete` V,
		    C = yes
		;
		    ( DisImp = yes -> Ts0 ; Fs0 ) `contains` V
		->
		    Ts = Ts0,
		    Fs = Fs0,
		    IMs = IMs0 `delete` V,
		    C = yes
		;
		    FVs = Fs0 `intersect` Vs,
		    \+ empty(FVs)
		->
		    Ts = ( DisImp = yes -> Ts0 `insert` V ; Ts0 ),
		    Fs = ( DisImp = yes -> Fs0 ; Fs0 `insert` V ),
		    IMs = IMs0 `delete` V,
		    C = yes
		;
		    TVs = Ts0 `intersect` Vs,
		    \+ empty(TVs)
		->
		    Ts = Ts0,
		    Fs = Fs0,
		    UTVs = Vs `difference` TVs,
		    IMs = ( empty(UTVs) ->
			IMs0 `delete` V
		    ;
			Ims0 ^ elem(V) := UTVs
		    ),
		    C = yes
		;
		    Ts = Ts0,
		    Fs = Fs0,
		    IMs = Ims0,
		    C = C0
		)
	    ), ImpMap0, {TrueVars0, FalseVars0, ImpMap0, no}).
		 
%------------------------------------------------------------------------%

propagate_equivalences_into_implications(EQVars, Changed, ImpVars0, ImpVars) :-
	ImpVars0 = imp_vars(Imps0, RevImps0, DisImps, RevDisImps),

	propagate_equivalences_into_disimplications(EQVars, DisImps),
	propagate_equivalences_into_disimplications(EQVars, RevDisImps),

	propagate_equivalences_into_implications_2(EQVars, Changed0,
	    Imps0, Imps),
	propagate_equivalences_into_implications_2(EQVars, Changed1,
	    RevImps0, RevImps),

	ImpVars = imp_vars(Imps, RevImps, DisImps, RevDisImps),
	Changed = Changed0 `bool__or` Changed1.

propagate_equivalences_into_implications_2(equiv_vars(T)::in, bool::out,
	imp_map(T)::in, imp_map(T)::out) is det.

propagate_equivalences_into_implications_2(EQVars, Changed, ImpMap0, ImpMap) :-
	ImpMap = foldl((func(V, Vs, IM0) = IM :-
		
		
