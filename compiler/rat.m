%-----------------------------------------------------------------------------%
% Copyright (C) 1995-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% file: rat.m
% main authors: conway, vjteag 


:- module rat.

:- interface.

/* This section of the interface is for both Mercury and Prolog versions */

:- import_module float, int.

:- type rat.

:- pred rat:'<'(rat, rat).
:- mode rat:'<'(in, in) is semidet.

:- pred rat:'>'(rat, rat).
:- mode rat:'>'(in, in) is semidet.

:- pred rat:'=<'(rat, rat).
:- mode rat:'=<'(in, in) is semidet.

:- pred rat:'>='(rat, rat).
:- mode rat:'>='(in, in) is semidet.

:- pred rat:'='(rat, rat).
:- mode rat:'='(in, in) is semidet.

/* This part of the interface will not compile in Prolog. */

:- func rat(int, int) = rat.

:- func float(rat) = float.

:- func rat:'+'(rat) = rat.

:- func rat:'-'(rat) = rat.

:- func rat:'+'(rat, rat) = rat.

:- func rat:'-'(rat, rat) = rat.

:- func rat:'*'(rat, rat) = rat.

:- func rat:'/'(rat, rat) = rat.

:- func rat:numer(rat) = int.

:- func rat:denom(rat) = int.

:- func rat:abs(rat) = rat.

:- func one = rat.

:- func zero = rat.

/* Prolog version of the interface. Note: this doesn't work yet */
/*
:- type rat
        --->    r(int, int)
        ;       ( rat + rat )
        ;       ( rat - rat )
        ;       ( rat * rat )
        ;       ( rat / rat )
        ;       ( - rat )
	;	abs(rat)
        ;       zero
        ;       one
        .


:- pred float(rat, float).
:- mode float(in, out) is det.

:- pred eval(rat, float).
:- mode eval(in, out) is det.

:- pred iabs(int, int).
:- mode iabs(in, out) is det.

:- pred ratnorm(rat, rat).
:- mode ratnorm(in, out) is det.

:- pred gcd(int, int, int).
:- mode gcd(in, in, out) is det.
*/
:- implementation.

/* Mercury and Prolog section */

:- import_module require.

:- type rat	--->	r(int, int).

rat:'<'(r(An, Ad), r(Bn, Bd)) :-
	An*Bd < Bn*Ad.

rat:'>'(r(An, Ad), r(Bn, Bd)) :-
	An*Bd > Bn*Ad.

rat:'=<'(r(An, Ad), r(Bn, Bd)) :-
	An*Bd =< Bn*Ad.

rat:'>='(r(An, Ad), r(Bn, Bd)) :-
	An*Bd >= Bn*Ad.

/* Implementation section which doesn't compile in Prolog */

:- func ratnorm(rat) = rat.

rat(Num, Den) = ratnorm(r(Num, Den)).

rat:'='(r(An, Ad), r(Bn, Bd)) :-
	ratnorm(r(An, Ad)) = ratnorm(r(Bn, Bd)).

rat:float(r(Num, Den)) = float:'/'(float:float(Num), float:float(Den)).

one = r(1, 1).

zero = r(0, 1).

rat:'+'(Rat) = Rat.

rat:'-'(r(Num, Den)) = r(-Num, Den).

rat:'+'(r(An, Ad), r(Bn, Bd)) = ratnorm(r(int:'+'(An*Bd, Bn*Ad), Ad*Bd)).

rat:'-'(r(An, Ad), r(Bn, Bd)) = ratnorm(r(int:'-'(An*Bd, Bn*Ad), Ad*Bd)).

rat:'*'(r(An, Ad), r(Bn, Bd)) = ratnorm(r(An*Bn, Ad*Bd)).

rat:'/'(r(An, Ad), r(Bn, Bd)) = Rat :-
	( Bn \= 0 ->
		Rat = ratnorm(r(An*Bd, Ad*Bn))
	;
		error("divide by zero")
	).

rat:numer(r(Num, _)) = Num.

rat:denom(r(_, Den)) = Den.

rat:abs(Rat) = ( Rat < zero -> rat:'-'(Rat) ; Rat ).

ratnorm(r(Num, Den)) = r(Sgn*iabs(Num)//Gcd, iabs(Den)//Gcd) :-
	(
		Num > 0,
		Den > 0
	->
		Sgn = 1
	;
		Num > 0
	->
		Sgn = -1
	;
		Den > 0
	->
		Sgn = -1
	;
		Sgn = 1
	),
	( Den = 0 -> error("zero denominator!") ; true),
	Gcd0 = gcd(iabs(Num), iabs(Den)),
	( Gcd0 = 0 -> error("zero gcd!") ; Gcd = Gcd0 ).

:- func iabs(int) = int.

iabs(X) = ( X < 0 -> -X ; X ).

:- func gcd(int, int) = int.

gcd(A, B) = Res :-
	( A = 0 ->
		Res = B
	; A < 0 ->
		error("A < 0")
	; B =< 0 ->
		error("B =< 0")
	;
		Res = gcd0(A, B)
	).

:- func gcd0(int, int) = int.

gcd0(A, B) = (
		A = 1 -> 1
	;	B = 1 -> 1
	;	A = B -> A
	;	A > B -> gcd0(A - B, B)
	;	gcd0(B - A, A)
	).

/* Implementation section to work in Prolog. Note: this doesn't work yet */
/*
% rat(Num, Den) = ratnorm(r(Num, Den)).

rat:'='(Rat0, Rat) :-
	eval0(Rat0) = eval0(Rat).

float(r(Num, Den), Float) :-
	Float is float:'/'(float:float(Num), float:float(Den)).


eval(Expr, Value) :-
        eval0(Expr, RatValue),
        RatValue = rat(Num, Den),
        Value is Num / Den.

:- pred eval0(rat, rat).
:- mode eval0(in, out(bound(r(ground, ground)))) is det.

eval0(zero, r(0,1)).

eval0(one, r(1,1)).

eval0(r(Num, Den), r(Num, Den)).
eval0(A + B, r(Num, Den)) :-
        eval0(A, r(ANum, ADen)),
        eval0(B, r(BNum, BDen)),
	Num0 is int:'+'(ANum*BDen, BNum*ADen), 
	Den0 is Ad*Bd,
	ratnorm(r(Num0, Den0), r(Num, Den)).


eval0(A - B, r(Num, Den)) :-
        eval0(A, r(ANum, ADen)),
        eval0(B, r(BNum, BDen)),
	Num0 is int:'-'(ANum*BNum, BNum*ADen),
	Den0 is Ad*Bd,
	ratnorm(r(Num0, Den0), r(Num, Den)).


eval0(A * B, r(Num, Den)) :-
        eval0(A, r(ANum, ADen)),
        eval0(B, r(BNum, BDen)),
	Num0 is ANum*BNum,
	Den0 is ADen*Bden,
	ratnorm(r(Num0, Den0), r(Num, Den)).


eval0(A / B, r(Num, Den)) :-
        eval0(A, r(ANum, ADen)),
        eval0(B, r(BNum, BDen)),
        ( BNum \= 0 ->
		Num0 is ANum*BDen,
		Den0 is ADen*BNum,
                ratnorm(r(Num0, Den0), r(Num, Den))
        ;
                error("divide by zero")
        ).

eval0( - A, r(Num, Den)) :-
	eval0(A, r(ANum, Den)),
	Num is -ANum.

eval0(abs(r(Num0, Den0)), r(Num, Den)) :- 
	iabs(Num0, Num),
	iabs(Den0, Den).
		

iabs(Num, Abs) :-
	 ( Num < 0 -> Abs = -Num ; Abs = Num ).


ratnorm(r(Num0, Den0), r(Num, Den)) :-
	(
		Num > 0,
		Den > 0
	->
		Sgn = 1
	;
		Num > 0
	->
		Sgn = -1
	;
		Den > 0
	->
		Sgn = -1
	;
		Sgn = 1
	),
	( Den = 0 -> error("zero denominator!") ; true),
	iabs(Num, Num_abs),
	iabs(Den, Den_abs),
	gcd(Num_abs, Den_abs, Gcd0),
	( Gcd0 = 0 -> error("zero gcd!") ; Gcd = Gcd0 ),
	iabs(Num0, Num1),
	iabs(Den0, Den1),
	Num is Sgn*Num1//Gcd,
	Den is Den1//Gcd.

gcd(A, B, Res) :-
	( A = 0 ->
		Res = B
	; A < 0 ->
		error("A < 0")
	; B =< 0 ->
		error("B =< 0")
	;
		gcd0(A, B, Res)
	).

:- pred gcd0(int, int, int).
:- mode gcd0(in, in, out) is det.
gcd0(A, B, Res) :- 
	(	A = 1 -> Res = 1
	;	B = 1 -> Res = 1
	;	A = B -> Res = A
	;	A > B -> gcd0(A - B, B, Res)
	;	gcd0(B - A, A, Res)
	).
*/
