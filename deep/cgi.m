%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module cgi.

:- interface.

:- import_module io.

:- pred main(io__state, io__state).
:- mode main(di, uo) is det.

:- implementation.

:- import_module cgi_interface.
:- import_module char, string, int, list, set, require, std_util.

main -->
	io__get_environment_var("QUERY_STRING", MQStr),
	(
		{ MQStr = yes(QStr) },
		{ split(QStr, ('+'), Pieces) },
		(
			{
				Pieces = ["clique", NStr],
				string__to_int(NStr, N),
				Fields = default_fields
			;
				Pieces = ["clique", Fields, NStr],
				string__to_int(NStr, N),
				validate_fields(Fields)
			}
		->
			to("/var/tmp/toDeep", clique(N, Fields)),
			from("/var/tmp/fromDeep", html(Str)),
			write_string("Content-type: text/html\n\n"),
			write_string(Str)
		;
			{
				Pieces = ["proc", NStr],
				string__to_int(NStr, N),
				Fields = default_fields
			;
				Pieces = ["proc", Fields, NStr],
				string__to_int(NStr, N),
				validate_fields(Fields)
			}
		->
			to("/var/tmp/toDeep", proc(N, Fields)),
			from("/var/tmp/fromDeep", html(Str)),
			write_string("Content-type: text/html\n\n"),
			write_string(Str)
		;
			{
				Pieces = ["procs", SortStr,
					FirstStr, LastStr],
				Fields = default_fields
			;
				Pieces = ["procs", SortStr, Fields,
					FirstStr, LastStr],
				validate_fields(Fields)
			},
			{
				SortStr = "self",
				Sort = self
			;
				SortStr = "both",
				Sort = self_and_desc
			},
			{ string__to_int(FirstStr, First) },
			{ string__to_int(LastStr, Last) }
		->
			to("/var/tmp/toDeep",
				procs(Sort, Fields, First, Last)),
			from("/var/tmp/fromDeep", html(Str)),
			write_string("Content-type: text/html\n\n"),
			write_string(Str)
		;
			{
				Pieces = ["root"],
				Fields = default_fields
			;
				Pieces = ["root", Fields],
				validate_fields(Fields)
			}
		->
			to("/var/tmp/toDeep", root(Fields)),
			from("/var/tmp/fromDeep", html(Str)),
			write_string("Content-type: text/html\n\n"),
			write_string(Str)
		;
			{ Pieces = ["menu"] }
		->
			to("/var/tmp/toDeep", menu),
			from("/var/tmp/fromDeep", html(Str)),
			write_string("Content-type: text/html\n\n"),
			write_string(Str)
		;
			{ Pieces = ["quit"] }
		->
			to("/var/tmp/toDeep", quit),
			from("/var/tmp/fromDeep", html(Str)),
			write_string("Content-type: text/html\n\n"),
			write_string(Str)
		;
			[]
		)
	;
		{ MQStr = no }
	).

:- func default_fields = fields.

default_fields = "apqtw".

:- func all_fields = fields.

all_fields = "apqtw".

:- pred validate_fields(string::in) is semidet.

validate_fields(String) :-
	Chars = string__to_char_list(String),
	list__sort_and_remove_dups(Chars, Chars),
	validate_field_chars(Chars,
		set__list_to_set(string__to_char_list(all_fields))).

:- pred validate_field_chars(list(char)::in, set(char)::in) is semidet.

validate_field_chars([], _).
validate_field_chars([Char | Chars], AvailFields0) :-
	set__delete(AvailFields0, Char, AvailFields1),
	validate_field_chars(Chars, AvailFields1).

:- pred to(string, cmd, io__state, io__state).
:- mode to(in, in, di, uo) is det.

to(Where, Cmd) -->
	tell(Where, Res),
	( { Res = ok } ->
		write(Cmd),
		write_string(".\n"),
		told
	;
		{ error("to: couldn't open pipe") }
	).

:- pred from(string, resp, io__state, io__state).
:- mode from(in, out, di, uo) is det.

from(Where, Resp) -->
	see(Where, Res0),
	( { Res0 = ok } ->
		read(Res1),
		( { Res1 = ok(Resp0) } ->
			{ Resp = Resp0 }
		;
			{ error("from: read failed") }
		)
	;
		{ error("from: couldn't open pipe") }
	).

:- pred split(string, char, list(string)).
:- mode split(in, in, out) is det.

split(Str0, SChar, Strs) :-
	string__to_char_list(Str0, Chars0),
	split(Chars0, SChar, [], [], Strs0),
	reverse(Strs0, Strs).

:- pred split(list(char), char, list(char), list(string), list(string)).
:- mode split(in, in, in, in, out) is det.

split([], _SChar, Chars0, Strs0, Strs) :-
	(
		Chars0 = [],
		Strs = Strs0
	;
		Chars0 = [_|_],
		reverse(Chars0, Chars),
		string__from_char_list(Chars, Str),
		Strs = [Str|Strs0]
	).
split([C|Cs], SChar, Chars0, Strs0, Strs) :-
	( C = SChar ->
		(
			Chars0 = [],
			Strs1 = Strs0
		;
			Chars0 = [_|_],
			reverse(Chars0, Chars),
			string__from_char_list(Chars, Str),
			Strs1 = [Str|Strs0]
		),
		split(Cs, SChar, [], Strs1, Strs)
	;
		split(Cs, SChar, [C|Chars0], Strs0, Strs)
	).
