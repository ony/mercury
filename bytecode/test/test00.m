
:- module test00.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

main(W0, W1) :-
	W0 = W1.
