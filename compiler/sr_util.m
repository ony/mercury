%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_util.
% Main authors: nancy
% 
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_util.
:- interface.

:- import_module list.

:- pred sr_util__list_drop_det(int,list(T),list(T)).
:- mode sr_util__list_drop_det(in,in,out) is det.


:- pred sr_util__list_map3(pred(T, T1, T2, T3), list(T), list(T1), list(T2), 
			list(T3)).
:- mode sr_util__list_map3(pred(in, out, out, out) is det, in, 
			out, out, out) is det.

:- pred sr_util__list_map_foldl2(
		pred(T, T1, T2, T2, T3, T3), 
		list(T), 
		list(T1),
		T2, T2, T3, T3).
:- mode sr_util__list_map_foldl2(pred(in, out, in, out, in, out) is det,
			in, out, in, out, in, out) is det.

:- pred sr_util__list_map3_foldl(pred(T1, T2, T3, T4, T5, T5), 
			list(T1), list(T2), list(T3), list(T4),
			T5, T5).
:- mode sr_util__list_map3_foldl(pred(in, out, out, out, in, out) is det,
			in, out, out, out, in, out) is det.

:- pred sr_util__list_map_foldl3(pred(T1, T2, T3, T3, T4, T4, T5, T5), 
			list(T1), list(T2),
			T3, T3, T4, T4, T5, T5).
:- mode sr_util__list_map_foldl3(pred(in, out, in, out, in, out, in, out) is det,
			in, out, in, out, in, out, in, out) is det.

:- pred sr_util__list_ho_member(pred(T,T), T, list(T)).
:- mode sr_util__list_ho_member(pred(in, in) is semidet, in, in) is semidet.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module int.

list_drop_det(Len,List,End):-
        (
                list__drop(Len,List,End0)
        ->
                End = End0
        ;
                End = List
       ).
	

list_map3(P, L, A, B, C) :- 
	(
		L = [ L1 | LR ]
	->
		P(L1, A1, B1, C1),
		list_map3(P, LR, AR, BR, CR),
		A = [ A1 | AR ],
		B = [ B1 | BR ],
		C = [ C1 | CR ]
	;
		A = [],
		B = [],
		C = []
	).

list_map_foldl2(P, L0, L1, A0, A, B0, B) :- 
	(
		L0 = [ LE0 | LR0 ]
	->
		P(LE0, LE1, A0, A1, B0, B1), 
		list_map_foldl2(P, LR0, LR1, A1, A, B1, B),
		L1 = [ LE1 | LR1 ]
	;
		L1 = [],
		A = A0, 
		B = B0
	).

list_map3_foldl(P, L0, L1, L2, L3, A0, A) :- 
	(
		L0 = [ X | Xs ]
	->
		P(X, Y1, Y2, Y3, A0, A1),
		list_map3_foldl(P, Xs, Ys1, Ys2, Ys3, A1, A),
		L1 = [ Y1 | Ys1 ],
		L2 = [ Y2 | Ys2 ],
		L3 = [ Y3 | Ys3 ]
	;
		L1 = [],
		L2 = [], 
		L3 = [],
		A = A0
	).
		
list_map_foldl3(P, L1, L, A1, A, B1, B, C1, C) :-
	(
		L1 = [ X | Xs ]
	->
		P(X, Y, A1, A2, B1, B2, C1, C2),
		list_map_foldl3(P, Xs, Ys, A2, A, B2, B, C2, C),
		L = [ Y | Ys ]
	;
		L = [],
		A = A1, 
		B = B1, 
		C = C1
	).

list_ho_member(EQUALITY_TEST, ELEMENT, LIST) :- 
	LIST = [ HEAD | TAIL ],
	(
		EQUALITY_TEST(HEAD, ELEMENT)
	->
		true
	;	
		list_ho_member(EQUALITY_TEST, ELEMENT, TAIL)
	).
