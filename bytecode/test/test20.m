
:- module test20.
:- interface.
:- import_module io, bool.

:- pred main(io__state::di, io__state::uo) is det.
:- pred some_pred(int::out) is det.
:- pred some_pred(int::out, int::out) is det.
:- func another_one(int) = int.
:- mode another_one(in) = out is semidet.
:- pred another_one(int::in, int::out) is semidet.

:- implementation.

main(W0, W1) :-
	W0 = W1.

some_pred(1).

some_pred(1,2).


another_one(1) = 1.

another_one(1,1).

% 
% :- pred ambiguous(bool::out) is det.
% ambiguous(true).
% 
% :- pred ambiguous(int::out) is det.
% ambiguous(0).
% 
