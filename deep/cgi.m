%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% XXX The cgi executable should be copied to /usr/lib/cgi-bin/mdprof.

:- module cgi.

:- interface.

:- import_module io.

:- pred main(io__state, io__state).
:- mode main(di, uo) is det.

:- implementation.

:- import_module interface, util.
:- import_module char, string, int, list, set, require, std_util.

main -->
	io__get_environment_var("QUERY_STRING", MaybeQueryString),
	(
		{ MaybeQueryString = yes(QueryString0) },
		{ split(QueryString0, ('$'), Pieces) },
		( { Pieces = [ActualQuery, MangledFileName] } ->
			process_query(ActualQuery, MangledFileName)
		; { Pieces = [MangledFileName] } ->
			process_query("menu", MangledFileName)
		;
			io__write_string(
				"Bad URL; expected query$:full:path:name")
		)
	;
		{ MaybeQueryString = no }
	).

:- pred process_query(string::in, string::in,
	io__state::di, io__state::uo) is det.

process_query(ActualQuery, MangledFileName) -->
	{ string__replace_all(MangledFileName, ":", "/", DataFileName) },
	{ ToServer = to_server_pipe_name(DataFileName) },
	{ FromServer = from_server_pipe_name(DataFileName) },
	{ TestCmd = string__format("test -p %s -a -p %s",
		[s(ToServer), s(FromServer)]) },
	io__call_system(TestCmd, TestRes),
	io__write_string("Content-type: text/html\n\n"),
	(
		{ TestRes = ok(ExitStatus) },
		( { ExitStatus = 0 } ->
			{ MaybeError = no }
		;
			create_server(DataFileName, MaybeError)
		),
		(
			{ MaybeError = no },
			handle_query(ActualQuery, ToServer, FromServer)
		;
			{ MaybeError = yes(Error) },
			io__write_string(Error)
		)
	;
		{ TestRes = error(Err) },
		{ io__error_message(Err, Msg) },
		io__write_string(Msg)
	).

:- pred create_server(string::in, maybe(string)::out,
	io__state::di, io__state::uo) is det.

create_server(DataFileName, MaybeError) -->
	{ ServerCmd = string__format(
		"%s -C -S %s -f %s < /dev/null > /dev/null 2> %s",
		[s(server_path_name), s(machine_name), s(DataFileName),
			s(server_startup_name(DataFileName))]) },
	io__call_system(ServerCmd, Res),
	(
		{ Res = ok(ExitStatus) },
		( { ExitStatus = 0 } ->
			{ MaybeError = no }
		;
			{ MaybeError = yes("Command to start server failed") }
		)
	;
		{ Res = error(Err) },
		{ io__error_message(Err, Msg) },
		{ MaybeError = yes(Msg) }
	).

:- func server_path_name = string.

% Eventually, this should just return "deep", and leave it up to a wrapper
% shell script that calls this executable to set up the path appropriately.
server_path_name = "/home/zs/mer/ws59/deep/deep".

:- func machine_name = string.

% Eventually, this should call the hostname library function.
machine_name = "miles".

:- pred handle_query(string::in, string::in, string::in,
	io__state::di, io__state::uo) is det.

handle_query(QueryString, ToServer, FromServer) -->
	{ query_to_cmd(QueryString, MaybeCmd) },
	(
		{ MaybeCmd = yes(Cmd) },
		to(ToServer, Cmd),
		from(FromServer, html(Str)),
		io__write_string(Str)
	;
		{ MaybeCmd = no }
	).
