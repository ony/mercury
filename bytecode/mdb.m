%-----------------------------------------------------------------------------%
% Copyright (C) 1997 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module mdb.

:- interface.

:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

/*
**	XXX: We should pass mdb's command-line arguments through to
**	BC_call_mbi(), otherwise we have to load all modules from
**	the toplevel prompt.
**	Hmm... We could put commands in a .mdbrc file, I suppose.
**	Personally I think rc files are a fugly hack that act as
**	a poor substitute for a general user preferences database.
*/
main -->
	call_mbi.

:- pred call_mbi(io__state::di, io__state::uo) is det.

:- pragma c_header_code("#include \"mbi.h\"").

:- pragma c_code(call_mbi(IO_in::di, IO_out::uo),
	"BC_call_mbi(); IO_out = IO_in;").

