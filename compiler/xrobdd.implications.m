%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: xrobdd.implications.m.
% Main author: dmo

:- module implications.

:- interface.

:- import_module robdd, bool.
:- import_module xrobdd__equiv_vars.

:- func init_imp_vars = imp_vars(T).

:- func imp_vars(T) * imp_vars(T) = imp_vars(T).

:- func imp_vars(T) + imp_vars(T) = imp_vars(T).

:- func imp_vars(T) `difference` imp_vars(T) = imp_vars(T).

:- func imp_vars(T) `delete` var(T) = imp_vars(T).

:- func restrict_threshold(var(T), imp_vars(T)) = imp_vars(T).

:- func filter(pred(var(T)), imp_vars(T)) = imp_vars(T).
:- mode filter(pred(in) is semidet, in) = out is det.

:- func neq_vars(var(T), var(T), imp_vars(T)) = imp_vars(T).

:- func imp_vars(var(T), var(T), imp_vars(T)) = imp_vars(T).

:- func at_most_one_of(vars(T), imp_vars(T)) = imp_vars(T).

:- func not_both(var(T), var(T), imp_vars(T)) = imp_vars(T).

:- pred normalise_true_false_implication_vars(bool::out, vars(T)::in,
	vars(T)::out, vars(T)::in, vars(T)::out, imp_vars(T)::in,
	imp_vars(T)::out) is det.

:- pred propagate_equivalences_into_implications(equiv_vars(T)::in, bool::out,
	imp_vars(T)::in, imp_vars(T)::out) is semidet.

:- pred propagate_implications_into_equivalences(bool::out, equiv_vars(T)::in,
	equiv_vars(T)::out, imp_vars(T)::in, imp_vars(T)::out) is det.

:- pred extract_implication_vars_from_robdd(bool::out, robdd(T)::in,
	robdd(T)::out, imp_vars(T)::in, imp_vars(T)::out) is det.

:- func add_equalities_to_imp_vars(equiv_vars(T), imp_vars(T)) = imp_vars(T).

:- implementation.

:- import_module map, require, assoc_list, std_util.

% imp_map invariant:
% for all imp_maps, IM:
% all [VA, VB] ( member(IM, VA, Vs), member(VB, Vs) ) => compare(<, VA, VB)

init_imp_vars = imp_vars(init, init, init, init).

ImpVarsA * ImpVarsB =
	apply_to_coresp_imp_maps(union, ImpVarsA, ImpVarsB).

ImpVarsA + ImpVarsB =
	apply_to_coresp_imp_maps(intersect, ImpVarsA, ImpVarsB).

ImpVarsA `difference` ImpVarsB =
	apply_to_coresp_imp_maps(imp_map_difference, ImpVarsA, ImpVarsB).

ImpVars `delete` Var =
	apply_to_imp_maps(delete_var_from_imp_map(Var), ImpVars).

restrict_threshold(Threshold, ImpVars) =
	apply_to_imp_maps(func(IM) =
		restrict_threshold_2(Threshold, to_assoc_list(IM), init),
	    ImpVars).

:- func restrict_threshold_2(var(T), assoc_list(var(T), vars(T)), imp_map(T))
	= imp_map(T).

restrict_threshold_2(_Threshold, [], IM) = IM.
restrict_threshold_2(Threshold, [V - Vs | AL], IM) =
	( compare((>), V, Threshold) ->
	    IM
	;
	    restrict_threshold_2(Threshold, AL,
	    	IM ^ entry(V) := remove_gt(Vs, Threshold))
	).

filter(P, ImpVars) = apply_to_imp_maps(filter_imp_map(P), ImpVars).

:- func filter_imp_map(pred(var(T)), imp_map(T)) = imp_map(T).
:- mode filter_imp_map(pred(in) is semidet, in) = out is det.

filter_imp_map(P, IM) =
	map__foldl(func(V, Vs, M) =
		( P(V) ->
		    M ^ entry(V) := filter(P, Vs)
		;
		    M `delete` V
		),
	    IM, IM).

neq_vars(VarA0, VarB0, ImpVars) =
	(ImpVars ^ dis_imps ^ new_relation(VarA) := VarB )
		 ^ rev_dis_imps ^ new_relation(VarA) := VarB :-
	( compare((<), VarA0, VarB0) ->
	    VarA = VarA0,
	    VarB = VarB0
	;
	    VarA = VarB0,
	    VarB = VarA0
	).

imp_vars(VarA, VarB, ImpVars) =
	( compare((=), VarA, VarB) ->
		ImpVars
	; compare((<), VarA, VarB) ->
		ImpVars ^ imps ^ new_relation(VarA) := VarB
	;
		ImpVars ^ rev_imps ^ new_relation(VarB) := VarA
	).

at_most_one_of(Vars0, ImpVars) =
	( remove_least(Vars0, Var, Vars) ->
	    at_most_one_of(Vars,
			ImpVars ^ dis_imps ^ new_relations(Var) := Vars)
	;
	    ImpVars
	).

not_both(VarA0, VarB0, ImpVars) =
	ImpVars ^ dis_imps ^ new_relation(VarA) := VarB :-
	( compare((<), VarA0, VarB0) ->
	    VarA = VarA0,
	    VarB = VarB0
	;
	    VarA = VarB0,
	    VarB = VarA0
	).

normalise_true_false_implication_vars(Changed, TrueVars0, TrueVars,
		FalseVars0, FalseVars, ImpVars0, ImpVars) :-
	(
	    empty(TrueVars0),
	    empty(FalseVars0)
	->
	    TrueVars = TrueVars0,
	    FalseVars = FalseVars0,
	    ImpVars = ImpVars0,
	    Changed = no
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

	    normalise_pairs(keys, Imps, DisImps, Changed4,
		FalseVars4, FalseVars5),
	    normalise_pairs(keys, RevImps, RevDisImps, Changed5,
		TrueVars4, TrueVars5),
	    normalise_pairs(values, RevImps, DisImps, Changed6,
		FalseVars5, FalseVars6),
	    normalise_pairs(values, Imps, RevDisImps, Changed7,
		TrueVars5, TrueVars6),

	    ImpVars6 = imp_vars(Imps, RevImps, DisImps, RevDisImps),
	    Changed = (Changed0 or Changed1 or Changed2 or Changed3 or
	    		Changed4 or Changed5 or Changed6 or Changed7),

	    ( Changed = yes ->
		normalise_true_false_implication_vars(_, TrueVars6, TrueVars,
		    FalseVars6, FalseVars, ImpVars6, ImpVars)
	    ;
		TrueVars = TrueVars6,
		FalseVars = FalseVars6,
		ImpVars = ImpVars6
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
		    ( IsDisImp = yes -> Fs0 ; Ts0 ) `contains` V
		->
		    Ts = Ts0 `union` Vs,
		    Fs = Fs0,
		    IMs = IMs0 `delete` V,
		    C = yes
		;
		    ( IsDisImp = yes -> Ts0 ; Fs0 ) `contains` V
		->
		    Ts = Ts0,
		    Fs = Fs0,
		    IMs = IMs0 `delete` V,
		    C = yes
		;
		    FVs = Fs0 `intersect` Vs,
		    \+ empty(FVs)
		->
		    Ts = ( IsDisImp = yes -> Ts0 `insert` V ; Ts0 ),
		    Fs = ( IsDisImp = yes -> Fs0 ; Fs0 `insert` V ),
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
			IMs0 ^ elem(V) := UTVs
		    ),
		    C = yes
		;
		    Ts = Ts0,
		    Fs = Fs0,
		    IMs = IMs0,
		    C = C0
		)
	    ), ImpMap0, {TrueVars0, FalseVars0, ImpMap0, no}).

:- type extract ---> keys ; values.

:- pred normalise_pairs(extract::in, imp_map(T)::in, imp_map(T)::in, bool::out,
	vars(T)::in, vars(T)::out) is det.

normalise_pairs(Extract, Imps, DisImps, Changed, FalseVars0, FalseVars) :-
	Intersect = Imps `intersect` DisImps,
	( is_empty(Intersect) ->
	    Changed = no,
	    FalseVars = FalseVars0
	;
	    Changed = yes,
	    (
		Extract = keys,
		Keys = sorted_list_to_set(Intersect ^ sorted_keys),
		FalseVars = FalseVars0 `union` Keys
	    ;
		Extract = values,
		Values = list__foldl(union, Intersect ^ values, init),
		FalseVars = FalseVars0 `union` Values
	    )
	).

		 
%------------------------------------------------------------------------%

propagate_equivalences_into_implications(EQVars, Changed, ImpVars0, ImpVars) :-
	ImpVars0 = imp_vars(Imps0, RevImps0, DisImps, RevDisImps),

	propagate_equivalences_into_disimplications(EQVars, DisImps,
	    RevDisImps),

	propagate_equivalences_into_implications_2(EQVars, Changed0,
	    Imps0, Imps),
	propagate_equivalences_into_implications_2(EQVars, Changed1,
	    RevImps0, RevImps),

	ImpVars = imp_vars(Imps, RevImps, DisImps, RevDisImps),
	Changed = Changed0 `bool__or` Changed1.

:- pred propagate_equivalences_into_implications_2(equiv_vars(T)::in,
	bool::out, imp_map(T)::in, imp_map(T)::out) is det.

propagate_equivalences_into_implications_2(EQVars, Changed, ImpMap0, ImpMap) :-
	{ImpMap, Changed} = foldl((func(V, Vs0, {IM, C}) =
		( empty(Vs) ->
			{IM, yes}
		;
			{IM ^ elem(V) := Vs, ( Vs = Vs0 -> C ; yes )}
		) :-
		Vs = filter(vars_are_not_equivalent(EQVars, V), Vs0)
	    ), ImpMap0, {init, no}).

:- pred propagate_equivalences_into_disimplications(equiv_vars(T)::in,
	imp_map(T)::in, imp_map(T)::in) is semidet.

propagate_equivalences_into_disimplications(EQVars, DisImps, RevDisImps) :-
	ImpMap = DisImps `intersect` RevDisImps,
	( all [VA, VB]
		% XXX this could be very slow.  May want to do it more
		% efficiently.
		( member(ImpMap, VA, Vs), member(VB, Vs) )
	=>
		vars_are_not_equivalent(EQVars, VA, VB)
	).

%------------------------------------------------------------------------%

% Look for occurrences of A => B and A <= B and replace then by A <=> B.
propagate_implications_into_equivalences(Changed, EQVars0, EQVars,
		ImpVars0, ImpVars) :-
	ImpVars0 = imp_vars(Imps0, RevImps0, DisImps, RevDisImps),

	( ( is_empty(Imps0) ; is_empty(RevImps0) ) ->
	    Changed = no,
	    EQVars = EQVars0,
	    ImpVars = ImpVars0
	;
	    {Changed, EQVars, Imps, RevImps} = foldl(
		( func(V, IVs, {C0, E0, I0, R0}) = {C, E, I, R} :-
		    (
			RVs = R0 ^ elem(V),
			EVs = IVs `intersect` RVs,
			\+ empty(EVs)
		    ->
			C = yes,
			E = add_equalities(EVs `insert` V, E0),
			I = I0 ^ entry(V) := IVs `difference` RVs,
			R = R0 ^ entry(V) := RVs `difference` IVs
		    ;
			C = C0, E = E0, I = I0, R = R0
		    )
		), Imps0, {no, EQVars0, Imps0, RevImps0}),
	    ImpVars = imp_vars(Imps, RevImps, DisImps, RevDisImps)
	).

%------------------------------------------------------------------------%

extract_implication_vars_from_robdd(Changed, Robdd0, Robdd,
		ImpVars0, ImpVars) :-
	ImpVars1 = extract_implications(Robdd0),
	ImpVars = ImpVars0 * ImpVars1,
	Robdd = remove_implications(ImpVars, Robdd0),

	Changed = ( Robdd = Robdd0, empty(ImpVars1) -> no ; yes ).

%------------------------------------------------------------------------%

add_equalities_to_imp_vars(EQVars, ImpVars) =
	map__foldl(func(VA, VB, IVs) =
		IVs ^ imp_vars(VA, VB) ^ imp_vars(VB, VA),
	    EQVars ^ leader_map, ImpVars).

%------------------------------------------------------------------------%

:- func 'entry :='(var(T), imp_map(T), vars(T)) = imp_map(T).

'entry :='(V, M, Vs) =
	( empty(Vs) ->
		M `delete` V
	;
		M ^ elem(V) := Vs
	).

:- func 'new_relation :='(var(T), imp_map(T), var(T)) = imp_map(T).

'new_relation :='(VA, M, VB) =
	( Vs = M ^ elem(VA) ->
	    M ^ elem(VA) := Vs `insert` VB
	;
	    M ^ elem(VA) := make_singleton_set(VB)
	).

:- func 'new_relations :='(var(T), imp_map(T), vars(T)) = imp_map(T).

'new_relations :='(V, M, NewVs) =
	( Vs = M ^ elem(V) ->
	    M ^ elem(V) := Vs `union` NewVs
	;
	    M ^ elem(V) := NewVs
	).

:- pred imp_map_contains(var(T)::in, var(T)::in, imp_map(T)::in) is semidet.

imp_map_contains(VA, VB, IM) :-
	( compare((<), VA, VB) ->
		IM ^ elem(VA) `contains` VB
	;
		error("imp_map_contains: variable ordering error")
	).

:- pred empty(imp_vars(T)::in) is semidet.

empty(imp_vars(I, RI, DI, RDI)) :-
	is_empty(I),
	is_empty(RI),
	is_empty(DI),
	is_empty(RDI).

%------------------------------------------------------------------------%

:- func apply_to_imp_maps(func(imp_map(T)) = imp_map(T), imp_vars(T)) =
		imp_vars(T).

apply_to_imp_maps(F, ImpVars0) = ImpVars :-
	ImpVars0 = imp_vars(I, RI, DI, RDI),
	ImpVars = imp_vars(F(I), F(RI), F(DI), F(RDI)).

:- func apply_to_coresp_imp_maps(func(imp_map(T), imp_map(T)) = imp_map(T),
	imp_vars(T), imp_vars(T)) = imp_vars(T).

apply_to_coresp_imp_maps(F, ImpVarsA, ImpVarsB) = ImpVars :-
	ImpVarsA = imp_vars(IA, RIA, DIA, RDIA),
	ImpVarsB = imp_vars(IB, RIB, DIB, RDIB),
	ImpVars = imp_vars(F(IA, IB), F(RIA, RIB), F(DIA, DIB), F(RDIA, RDIB)).

:- func imp_map(T) `union` imp_map(T) = imp_map(T).

IMA `union` IMB = union(union, IMA, IMB).

:- func imp_map(T) `intersect` imp_map(T) = imp_map(T).

IMA `intersect` IMB = remove_empty_sets(intersect(intersect, IMA, IMB)).

:- func imp_map(T) `imp_map_difference` imp_map(T) = imp_map(T).

IMA `imp_map_difference` IMB =
	map__foldl(func(V, VsB, M) =
		( VsA = M ^ elem(V) ->
		    M ^ entry(V) := VsA `difference` VsB
		;
		    M
		),
	    IMA, IMB).

:- func remove_empty_sets(imp_map(T)) = imp_map(T).

remove_empty_sets(IM) =
	map__foldl(func(V, Vs, M) =
		( empty(Vs) ->
		    M `delete` V
		;
		    M
		),
	    IM, IM).

:- func delete_var_from_imp_map(var(T), imp_map(T)) = imp_map(T).

delete_var_from_imp_map(Var, IM0) =
	map__foldl(func(V, Vs, M) =
		( Vs `contains` Var ->
		    M ^ entry(V) := Vs `delete` Var
		;
		    M
		),
	    IM1, IM1) :-
	IM1 = IM0 `delete` Var.
