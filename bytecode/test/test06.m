
:- module test06.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

:- import_module list.

main(W0, W1) :-
	app([1,2],[3],L),
	W0 = W1.

:- pred app(list(T), list(T), list(T)).
:- mode app(in, in, out) is det.

app([],Ys,Ys).
app([X|Xs], Ys, [X|App]) :-
	app(Xs,Ys,App).

