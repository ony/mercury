
:- module test04.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

main(W0, W1) :-
	some_pred(X),	
	W0 = W1.

:- pred some_pred(int::out) is multi.
some_pred(1).
some_pred(2).

