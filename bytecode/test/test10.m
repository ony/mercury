
:- module test10.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

:- import_module list.

main(W0, W1) :-
	% app([1,2],[3],L),
	W0 = W1.

:- pred app(list(T), list(T), list(T)).
:- mode app(in, in, in) is semidet.
:- mode app(in, in, out) is det.
:- mode app(in, out, in) is semidet.
% :- mode app(in, out, out) is multi.
:- mode app(out, in, in) is nondet.
% :- mode app(out, in, out) is multi.
:- mode app(out, out, in) is multi.
% :- mode app(out, out, out) is nondet.

app([],Ys,Ys).
app([X|Xs], Ys, [X|App]) :-
	app(Xs,Ys,App).

