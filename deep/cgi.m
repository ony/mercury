%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% XXX The cgi executable should be copied to /usr/lib/cgi-bin/deep.

:- module cgi.

:- interface.

:- import_module io.

:- pred main(io__state, io__state).
:- mode main(di, uo) is det.

:- implementation.

:- import_module cgi_interface.
:- import_module char, string, int, list, set, require, std_util.

main -->
	io__get_environment_var("QUERY_STRING", MaybeQueryString),
	(
		{ MaybeQueryString = yes(QueryString0) },
		init_query(QueryString0, QueryString, ToServer, FromServer),
		handle_query(QueryString, ToServer, FromServer)
	;
		{ MaybeQueryString = no }
	).

:- pred handle_query(string::in, string::in, string::in,
	io__state::di, io__state::uo) is det.

handle_query(QueryString, ToServer, FromServer) -->
	{ split(QueryString, ('+'), Pieces) },
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
		to(ToServer, clique(N, Fields)),
		from(FromServer, html(Str)),
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
		to(ToServer, proc(N, Fields)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{
			Pieces = ["procs", SortStr, InclDescStr,
				LimitStr],
			Fields = default_fields
		;
			Pieces = ["procs", SortStr, InclDescStr,
				LimitStr, Fields],
			validate_fields(Fields)
		},
		{ translate_criteria(SortStr, Sort,
			InclDescStr, InclDesc, LimitStr, Limit) }
	->
		to(ToServer, top_procs(Sort, InclDesc, Limit, Fields)),
		from(FromServer, html(Str)),
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
		to(ToServer, root(Fields)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["menu"] }
	->
		to(ToServer, menu),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["proc_static", NStr] },
		{ string__to_int(NStr, N) }
	->
		to(ToServer, proc_static(N)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["proc_dynamic", NStr] },
		{ string__to_int(NStr, N) }
	->
		to(ToServer, proc_dynamic(N)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["call_site_static", NStr] },
		{ string__to_int(NStr, N) }
	->
		to(ToServer, call_site_static(N)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["call_site_dynamic", NStr] },
		{ string__to_int(NStr, N) }
	->
		to(ToServer, call_site_dynamic(N)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["raw_clique", NStr] },
		{ string__to_int(NStr, N) }
	->
		to(ToServer, raw_clique(N)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["num_proc_statics"] }
	->
		to(ToServer, num_proc_statics),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["num_call_site_statics"] }
	->
		to(ToServer, num_call_site_statics),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["num_proc_dynamics"] }
	->
		to(ToServer, num_proc_dynamics),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["num_call_site_dynamics"] }
	->
		to(ToServer, num_call_site_dynamics),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["timeout", TStr] },
		{ string__to_int(TStr, TimeOut) }
	->
		to(ToServer, timeout(TimeOut)),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		{ Pieces = ["quit"] }
	->
		to(ToServer, quit),
		from(FromServer, html(Str)),
		write_string("Content-type: text/html\n\n"),
		write_string(Str)
	;
		[]
	).

:- pred init_query(string::in, string::out, string::out, string::out,
	io__state::di, io__state::uo) is det.

init_query(QueryString0, QueryString, ToServer, FromServer) -->
	{ extract_base_name(QueryString0, QueryString, BaseName) },
	{ string__append(BaseName, "_to_server", ToServer) },
	{ string__append(BaseName, "_from_server", FromServer) }.

:- pred extract_base_name(string::in, string::out, string::out) is det.

extract_base_name(QueryString, QueryString, "/var/tmp/pipes").

:- pred translate_criteria(string::in, sort_measurement::out,
	string::in, include_descendants::out, string::in, display_limit::out)
	is semidet.

translate_criteria(SortStr, Sort, InclDescStr, InclDesc, LimitStr, Limit) :-
	(
		SortStr = "calls",
		Sort = calls
	;
		SortStr = "time",
		Sort = time
	;
		SortStr = "allocs",
		Sort = allocs
	;
		SortStr = "words",
		Sort = words
	),
	(
		InclDescStr = "self",
		InclDesc = self
	;
		InclDescStr = "both",
		InclDesc = self_and_desc
	),
	(
		split(LimitStr, '-', Pieces),
		Pieces = [FirstStr, LastStr],
		string__to_int(FirstStr, First),
		string__to_int(LastStr, Last)
	->
		Limit = rank_range(First, Last)
	;
		string__to_float(LimitStr, Threshold)
	->
		Limit = threshold(Threshold)
	;
		fail
	).

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
