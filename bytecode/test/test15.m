
:- module test03.
:- interface.

:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.
:- pred bozo_pred(int::out) is det.

:- implementation.

bozo_pred(1).

main(Win, Wout) :- Wout = Win.
