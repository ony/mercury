
:- module test07.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

:- import_module list.

main(W0, W1) :-
	app(X1,X2,[1,2,3]),
	W0 = W1.

:- pred app(list(T), list(T), list(T)).
:- mode app(out, out, in) is multi.

app([],Ys,Ys).
app([X|Xs], Ys, [X|App]) :-
	app(Xs,Ys,App).

