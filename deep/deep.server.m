:- module deep:server.

:- interface.

:- pred server(globals, deep, io__state, io__state).
:- mode server(in, in, di, uo) is det.

:- implementation.

:- import_module float.

server(Globals, Deep) -->
	io__see("/var/tmp/toDeep", _),
	read(Res0),
	io__seen,
	(
		{ Res0 = eof },
		stderr_stream(StdErr),
		write_string(StdErr, "eof.\n"),
		server(Globals, Deep)
	;
		{ Res0 = error(Msg, Line) },
		stderr_stream(StdErr),
		format(StdErr, "error reading input line %d: %s\n",
			[i(Line), s(Msg)]),
		server(Globals, Deep)
	;
		{ Res0 = ok(Cmd) },
		exec(Cmd, Globals, Deep)
	).

:- type cmd
	--->	quit
	;	root
	;	clique(int)
	;	procs(sort, int, int)
	.

:- type sort
	--->	self
	;	self_and_desc
	.

:- type resp
	--->	html(string)
	.

:- pred exec(cmd, globals, deep, io__state, io__state).
:- mode exec(in, in, in, di, uo) is det.

exec(quit, _, _) -->
	tell("/var/tmp/fromDeep", _),
	write(html(
"<HTML>\n" ++
"<TITLE>The University of Melbourne Mercury Deep Profiler.</TITLE>\n" ++
"<H1>Shutting down deep profiler.</H1>\n" ++
"</HTML>\n")),
	write_string(".\n"),
	told.

exec(root, Globs, Deep) -->
	{ RootQuanta = rootTime(Deep) },
	{ RQ = float(RootQuanta) },
	{ URL = "http://www.mercury.cs.mu.oz.au/cgi-bin/deep" },
	{ HTML =
		"<HTML>\n" ++
		banner ++
		"<TABLE>\n" ++
		clique_table_header ++
		pred_name("Call graph root", RQ, RootQuanta) ++
		callsite2html(URL, Deep, clique(-1), Deep^root) ++
		"</TABLE>\n" ++
		footer(Deep) },
	tell("/var/tmp/fromDeep", _),
	write(html(HTML)),
	write_string(".\n"),
	told,
	server(Globs, Deep).

:- func rootTime(deep) = int.
rootTime(Deep) = RootQuanta :-
	Deep^root = call_site_dynamic_ptr(RootI),
	lookup(Deep^csd_desc, RootI, RootQuanta).

exec(clique(N), Globs, Deep) -->
	( { N > 0 } ->
		{ URL = "http://www.mercury.cs.mu.oz.au/cgi-bin/deep" },
		{ HTML =
			"<HTML>\n" ++
			banner ++
			"<TABLE>\n" ++
			clique_table_header ++
			clique2html(URL, Deep, clique(N)) ++
			"</TABLE>\n" ++
			footer(Deep) }
	;
		{ HTML = "<HTML>\n" ++
			banner ++
			"<H1>Node not found.</H1>\n" ++
			"</HTML>\n" }
	),
	tell("/var/tmp/fromDeep", _),
	write(html(HTML)),
	write_string(".\n"),
	told,
	server(Globs, Deep).

exec(procs(Sort, First, Last), Globs, Deep) -->
	{ URL = "http://www.mercury.cs.mu.oz.au/cgi-bin/deep" },
	{ HTML =
		"<HTML>\n" ++
		banner ++
		"<TABLE>\n" ++
		clique_table_header ++
		procs2html(URL, Deep, Sort, First, Last) ++
		"</TABLE>\n" ++
		footer(Deep) },
	tell("/var/tmp/fromDeep", _),
	write(html(HTML)),
	write_string(".\n"),
	told,
	server(Globs, Deep).

:- func banner = string.
banner =
    "<TITLE>The University of Melbourne Mercury Deep Profiler.</TITLE>\n".

:- func clique_table_header = string.
clique_table_header =
	"<TR>\n" ++
	"<TD>Kind</TD>\n" ++
	"<TD>Procedure</TD>\n" ++
	"<TD ALIGN=RIGHT>Calls</TD>\n" ++
	"<TD ALIGN=RIGHT>Exits</TD>\n" ++
	"<TD ALIGN=RIGHT>Fails</TD>\n" ++
	"<TD ALIGN=RIGHT>Redos</TD>\n" ++
	"<TD ALIGN=RIGHT>Self</TD>\n" ++
	"<TD ALIGN=RIGHT>% of root</TD>\n" ++
	"<TD ALIGN=RIGHT>Self + Descendants</TD>\n" ++
	"<TD ALIGN=RIGHT>% of root</TD>\n" ++
	"</TR>\n".

:- func pred_name(string, float, int) = string.
pred_name(Name, RQ, Total) =
		"<TR>\n" ++
		format("<TD COLSPAN=8><B>%s</B></TD>\n", [s(Name)]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Total))]) ++
		format("<TD ALIGN=RIGHT>%2.2f</TD>\n", [f(Prop)]) ++
		"</TR>\n" ++
		"<TR><TD>.</TD></TR>\n" :-
	Prop = 100.0 * float(Total) / RQ.

:- func footer(deep) = string.
footer(_Deep) =
	% Link back to root,
	% Search, etc, etc.
	"</HTML>\n".

:- func clique2html(string, deep, clique) = string.
clique2html(URL, Deep, Clique) = HTML :-
	Clique = clique(CliqueN),
	HTML =
		SummaryLine ++
		CliqueHTML,

	lookup(Deep^clique_members, CliqueN, PDPtrs),
	lookup(Deep^clique_parents, CliqueN, CallerCSDPtr),

	RootQuanta = rootTime(Deep),
	RQ = float(RootQuanta),

	SummaryLine = callsite2html(URL, Deep, Clique, CallerCSDPtr),

	map((pred(PDPtr::in, PDStr::out) is det :-
		PDPtr = proc_dynamic_ptr(PDI),
		( PDI > 0 ->
			lookup(Deep^proc_dynamics, PDI, PD),
			PD = proc_dynamic(PSPtr, _),
			PSPtr = proc_static_ptr(PSI),
			lookup(Deep^proc_statics, PSI, PS),
			PS = proc_static(Id, _),
			call_sites(Deep, PDPtr, CSDPtrs),
			CSDStrs = map(callsite2html(URL, Deep, Clique),
				CSDPtrs),
			append_list(CSDStrs, Rows),
			lookup(Deep^pd_desc, PDI, SubTotal0),
			lookup(Deep^pd_own, PDI, SubTotal1),
			SubTotal = SubTotal0 + SubTotal1,
			PDStr = pred_name(Id, RQ, SubTotal) ++ Rows ++
				"<TR><TD COLSPAN=8>.</TD></TR>\n"
		;
			PDStr = ""
		)
	), PDPtrs, PDStrs),
	append_list(PDStrs, CliqueHTML).
		
:- pred addTime(proc_dynamic_ptr, int,
		(proc_dynamic_ptr -> int), (proc_dynamic_ptr -> int)).
:- mode addTime(in, in, in, out) is det.

addTime(P, T0, SM0, SM) :-
	( search(SM0, P, T1) ->
		T = T0 + T1
	;
		T = T0
	),
	set(SM0, P, T, SM).


:- func callsite2html(string, deep, clique, call_site_dynamic_ptr) = string.
callsite2html(URL, Deep, ThisClique, CSDPtr) = Row :-
	RootQuanta = rootTime(Deep),
	RQ = float(RootQuanta),
	label(CSDPtr, Deep) = CalleeName,
	CSDPtr = call_site_dynamic_ptr(CSDI),
	lookup(Deep^call_site_dynamics, CSDI, CSD),
	CSD = call_site_dynamic(ToPtr, PI),
	ToPtr = proc_dynamic_ptr(ToInd),
	lookup(Deep^clique_index, ToInd, clique(To)),

		% We don't link recursive calls
	( clique(To) = ThisClique ->
		ProcName = CalleeName
	;
		ProcName = 
		format("<A HREF=""%s?clique+%d"">%s</A>\n",
			[s(URL), i(To), s(CalleeName)])
	),
	Calls = calls(PI), Exits = exits(PI),
	Fails = fails(PI), Redos = redos(PI),
	Quanta0 = quanta(PI),
	lookup(Deep^csd_desc, CSDI, Quanta1),
	Quanta = Quanta0 + Quanta1,
	Q0 = float(Quanta0),
	Q = float(Quanta),
	Prop0 = 100.0 * Q0 / RQ,
	Prop = 100.0 * Q / RQ,
	Row = "<TR>\n" ++
		"<TD> </TD>\n" ++
		format("<TD>%s</TD>\n", [s(ProcName)]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Calls))]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Exits))]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Fails))]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Redos))]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Quanta0))]) ++
		format("<TD ALIGN=RIGHT>%0.2f</TD>\n", [f(Prop0)]) ++
		format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Quanta))]) ++
		format("<TD ALIGN=RIGHT>%0.2f</TD>\n", [f(Prop)]) ++
		"</TR>\n".

:- func procs2html(string, deep, sort, int, int) = string.
procs2html(_URL, Deep, Sort, First, Last) = HTML :-
	foldl((pred(PSI::in, PS::in, Xs0::in, Xs::out) is det :-
		(
			PSI >= First,
			PSI =< Last
		->
			lookup(Deep^ps_own, PSI, PI),
			PS = proc_static(Id, _),
			Cs = calls(PI), Es = exits(PI),
			Fs = fails(PI), Rs = redos(PI),
			Qs0 = quanta(PI),
			lookup(Deep^ps_desc, PSI, Qs1),
			Qs = Qs0 + Qs1,
			Q0 = float(Qs0),
			Q = float(Qs),
			Prop0 = 100.0 * Q0 / RQ,
			Prop = 100.0 * Q / RQ,
			RootQuanta = rootTime(Deep),
			RQ = float(RootQuanta),
			Row = "<TR>\n" ++
			 "<TD> </TD>\n" ++
			 format("<TD>%s</TD>\n", [s(Id)]) ++
			 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Cs))]) ++
			 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Es))]) ++
			 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Fs))]) ++
			 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Rs))]) ++
			 format("<TD ALIGN=RIGHT>%s</TD>\n",[s(commas(Qs0))]) ++
			 format("<TD ALIGN=RIGHT>%0.2f</TD>\n", [f(Prop0)]) ++
			 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Qs))]) ++
			 format("<TD ALIGN=RIGHT>%0.2f</TD>\n", [f(Prop)]) ++
				"</TR>\n",
			(
				Sort = self,
				K = Qs0
			;
				Sort = self_and_desc,
				K = Qs
			),
			X = {K, Row},
			Xs = [X|Xs0]
		;
			Xs = Xs0
		)
	), Deep^proc_statics, [], KeyedRows0),
	sort(KeyedRows0, KeyedRows),
	foldl((pred({_, RStr}::in, Strs1::in, Strs2::out) is det :-
		Strs2 = [RStr|Strs1]
	), KeyedRows, [], RowStrs),
	append_list(RowStrs, HTML).

:- func label(call_site_dynamic_ptr, deep) = string.

label(CSDPtr, Deep) = Name :-
	(
		CSDPtr = call_site_dynamic_ptr(CSDI), CSDI > 0,
		lookup(Deep^call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(PDPtr, _),
		PDPtr = proc_dynamic_ptr(PDI), PDI > 0,
		lookup(Deep^proc_dynamics, PDI, PD),
		PD = proc_dynamic(PSPtr, _),
		PSPtr = proc_static_ptr(PSI), PSI > 0,
		lookup(Deep^proc_statics, PSI, PS),
		PS = proc_static(Id, _)
	->
		Name = Id
	;
		Name = "-"
	).

:- func refs(call_site_dynamic_ptr, deep) = array(call_site_ref).

refs(CSDPtr, Deep) = Refs :-
	(
		CSDPtr = call_site_dynamic_ptr(CSDI), CSDI > 0,
		lookup(Deep^call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(PDPtr, _),
		PDPtr = proc_dynamic_ptr(PDI), PDI > 0,
		lookup(Deep^proc_dynamics, PDI, PD),
		PD = proc_dynamic(_, Refs0)
	->
		Refs = Refs0
	;
		Refs = array([])
	).

:- func commas(int) = string.

commas(Num) = Str :-
	format("%d", [i(Num)], Str0),
	string__to_char_list(Str0, Chars0),
	reverse(Chars0, Chars1),
	string__from_char_list(reverse(commas1(Chars1)), Str).

:- func commas1([char]) = [char].
commas1([]) = [].
commas1([C]) = [C].
commas1([C,D]) = [C,D].
commas1([C,D,E]) = [C,D,E].
commas1([C,D,E,F|R]) = [C,D,E,(',')|commas1([F|R])].

