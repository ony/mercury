
:- module test30.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

:- import_module int.

main(Win, Wout) :- 
	apply(sqr, 2, X),
	Wout = Win.

:- pred apply( pred(int,int)::pred(in,out) is det, int::in, int::out) is det.
apply(F,X,FX) :-
	F(X,FX).
:- pred sqr(int::in, int::out) is det.
sqr(X,Sqr) :-
	Sqr = X * X.

