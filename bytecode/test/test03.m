
:- module test03.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

main(W0, W1) :-
	some_pred(W0,W1).

:- pred some_pred(io__state::di, io__state::uo) is det.
some_pred(W0,W1) :-
	W0 = W1.
