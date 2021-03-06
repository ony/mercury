% from primes.m
%
% Uncaught Mercury exception:
% Software Error: instmap.m: Unexpected: merge_instmapping_delta_2: error
% merging var 9
%

:- module dep_par_21.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module int.
:- import_module list.

main(!IO) :-
    remove(3, 1..5, Res),
    io.print(Res, !IO),
    io.nl(!IO).

:- pred remove(int::in, list(int)::in, list(int)::out) is det.

remove(_P, [], []).
remove(P, [I | Is], Result) :-
    M is I mod P &
    ( M = 0 ->
	Result = Nis &
	remove(P, Is, Nis)
    ;
	Result = [I | Nis] &
	remove(P, Is, Nis)
    ).
