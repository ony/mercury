% A tricky situation for the direct argument type representation optimisation.

:- module direct_arg_intermod1.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module direct_arg_intermod2.

%-----------------------------------------------------------------------------%

main(!IO) :-
    M1 = mk_maybe_inline(one, 1),
    write_maybe_inline(M1, !IO),
    write_maybe_no_inline(M1, !IO),

    M2 = mk_maybe_no_inline(one, 2),
    write_maybe_inline(M2, !IO),
    write_maybe_no_inline(M2, !IO).

:- func one = int.
:- pragma no_inline(one/0).

one = 1.

%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sts=4 sw=4 et
