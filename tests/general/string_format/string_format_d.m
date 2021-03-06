%------------------------------------------------------------------------------%
% string_format_d.m
%
% Test the d,i specifiers of string__format.
%------------------------------------------------------------------------------%

:- module string_format_d.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module string_format_lib.
:- import_module int, list, string.

%------------------------------------------------------------------------------%

main -->
	{ Ints = [i(0), i(-1), i(1), i(10), i(-10),
			i(100), i(-100), i(min_int), i(max_int)] },
	list__foldl(output_list(Ints), format_strings("d")),
	list__foldl(output_list(Ints), format_strings("i")).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
