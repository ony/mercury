%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module deep:server.

:- interface.

:- pred server(string::in, string::in, int::in, string::in, deep::in,
	io__state::di, io__state::uo) is det.

:- implementation.

:- import_module cgi_interface.
:- import_module float.

:- type call_site_line_number
	--->	call_site_line_number
	;	no_call_site_line_number.

server(InputFileName, OutputFileName, Wait, Machine, Deep) -->
	{ string__append_list(["http://www.", Machine,
		".cs.mu.oz.au/cgi-bin/deep"], URLprefix) },
	server_loop(InputFileName, OutputFileName, Wait, URLprefix, Deep).

:- pred server_loop(string::in, string::in, int::in, string::in, deep::in,
	io__state::di, io__state::uo) is det.

server_loop(InputFileName, OutputFileName, Wait, URLprefix, Deep) -->
	io__see(InputFileName, _),
	read(Res0),
	stderr_stream(StdErr),
	write(StdErr, Res0), nl(StdErr),
	io__seen,
	(
		{ Res0 = eof },
		write_string(StdErr, "eof.\n"),
		server_loop(InputFileName, OutputFileName, Wait,
			URLprefix, Deep)
	;
		{ Res0 = error(Msg, Line) },
		format(StdErr, "error reading input line %d: %s\n",
			[i(Line), s(Msg)]),
		server_loop(InputFileName, OutputFileName, Wait,
			URLprefix, Deep)
	;
		{ Res0 = ok(Cmd) },
		{ exec(Cmd, URLprefix, Deep, HTML, Continue) },
		( { Wait > 0 } ->
			io__tell(OutputFileName, _),
			io__write_string(HTML),
			io__write_string(".\n"),
			io__told,
			{ wait(Wait) }
		;
			io__tell(OutputFileName, _),
			io__write(html(HTML)),
			io__write_string(".\n"),
			io__told
		),
		(
			{ Continue = yes },
			server_loop(InputFileName, OutputFileName, Wait,
				URLprefix, Deep)
		;
			{ Continue = no }
		)
	).

:- pred wait(int::in) is det.

:- pragma foreign_code("C", wait(Seconds::in), [will_not_call_mercury], "
	#include <unistd.h>
	sleep(Seconds);
").

%-----------------------------------------------------------------------------%

:- pred exec(cmd::in, string::in, deep::in, string::out, bool::out) is det.

exec(Cmd, URLprefix, Deep, HTML, no) :-
	Cmd = quit,
	HTML =
		banner ++
		"<H1>Shutting down deep profiler.</H1>\n" ++
		footer(URLprefix, Cmd, Deep).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = menu,
	HTML =
		banner ++
		"<p>\n" ++
		menu_text ++
		"<ul>\n" ++
		"<li>\n" ++
		menu_item(URLprefix, "root",
			"Exploring the call graph.") ++
		"<li>\n" ++
		menu_item(URLprefix, "procs+self+1+100",
			"Most expensive procedures: time, self.") ++
		"<li>\n" ++
		menu_item(URLprefix, "procs+both+1+100",
			"Most expensive procedures: time, self+desc.") ++
		"</ul>\n" ++
		"<p>\n" ++
		footer(URLprefix, Cmd, Deep).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = root(Fields), 
	RootOwn = root_own_info(Deep),
	RootInherit = root_inherit_info(Deep),
	HTML =
		banner ++
		"<TABLE>\n" ++
		fields_header(Fields) ++
		proc_total_in_clique(main_parent_proc_id, Deep, Fields,
			RootOwn, RootInherit) ++
		call_site_to_html(URLprefix, Deep, Fields,
			no_call_site_line_number, clique_ptr(-1), Deep ^ root)
			++
		"</TABLE>\n" ++
		footer(URLprefix, Cmd, Deep).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = clique(CliqueNum, Fields),
	( valid_clique_ptr(Deep, clique_ptr(CliqueNum)) ->
		HTML =
			banner ++
			"<TABLE>\n" ++
			fields_header(Fields) ++
			clique_to_html(URLprefix, clique_ptr(CliqueNum),
				Deep, Fields) ++
			"</TABLE>\n" ++
			footer(URLprefix, Cmd, Deep)
	;
		HTML =
			banner ++
			"<H1>There is no clique with that number.</H1>\n" ++
			footer(URLprefix, Cmd, Deep)
	).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = procs(Sort, Fields, First, Last),
	HTML =
		banner ++
		"<TABLE>\n" ++
		fields_header(Fields) ++
		procs2html(URLprefix, Deep, Sort, Fields, First, Last) ++
		"</TABLE>\n" ++
		footer(URLprefix, Cmd, Deep).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = proc(PSI, Fields),
	HTML =
		"<HTML>\n" ++
		banner ++
		"<TABLE>\n" ++
		fields_header(Fields) ++
		proc_summary_to_html(URLprefix, Deep, Fields, PSI) ++
		"</TABLE>\n" ++
		footer(URLprefix, Cmd, Deep).

%-----------------------------------------------------------------------------%

:- func banner = string.

banner =
	"<HTML>\n" ++
	"<TITLE>The University of Melbourne Mercury Deep Profiler.</TITLE>\n".

:- func footer(string, cmd, deep) = string.

footer(_URLprefix, _Cmd, _Deep) =
	% Link back to root,
	% Search, etc, etc.
	"</HTML>\n".

:- func menu_text = string.

menu_text =
	"You can start exploring the deep profile at the following points.".

:- func menu_item(string, string, string) = string.

menu_item(URLprefix, URLsuffix, Text) = 
	format("<A HREF=""%s?%s"">%s</A>\n",
		[s(URLprefix), s(URLsuffix), s(Text)]).

%-----------------------------------------------------------------------------%

:- func root_total_info(deep) = inherit_prof_info.

root_total_info(Deep) = RootTotal :-
	Deep ^ root = call_site_dynamic_ptr(RootI),
	lookup(Deep ^ csd_desc, RootI, RootInherit),
	lookup(Deep ^ call_site_dynamics, RootI, RootCsd),
	RootCsd = call_site_dynamic(_, RootOwn),
	add_own_to_inherit(RootOwn, RootInherit) = RootTotal.

:- func root_inherit_info(deep) = inherit_prof_info.

root_inherit_info(Deep) = RootInherit :-
	Deep ^ root = call_site_dynamic_ptr(RootI),
	lookup(Deep ^ csd_desc, RootI, RootInherit).

:- func root_own_info(deep) = own_prof_info.

root_own_info(Deep) = RootOwn :-
	Deep ^ root = call_site_dynamic_ptr(RootI),
	lookup(Deep ^ call_site_dynamics, RootI, RootCsd),
	RootCsd = call_site_dynamic(_, RootOwn).

%-----------------------------------------------------------------------------%

:- func fields_header(fields) = string.

fields_header(Fields) =
	"<TR>\n" ++
	"<TD>Kind</TD>\n" ++
	"<TD>Procedure</TD>\n" ++
	( show_port_counts(Fields) ->
		"<TD ALIGN=RIGHT>Calls</TD>\n" ++
		"<TD ALIGN=RIGHT>Exits</TD>\n" ++
		"<TD ALIGN=RIGHT>Fails</TD>\n" ++
		"<TD ALIGN=RIGHT>Redos</TD>\n"
	;
		""
	) ++
	( show_quanta(Fields) ->
		"<TD ALIGN=RIGHT>Self quanta</TD>\n"
	;
		""
	) ++
	( show_times(Fields) ->
		"<TD ALIGN=RIGHT>Self time</TD>\n"
	;
		""
	) ++
	( (show_quanta(Fields) ; show_times(Fields)) ->
		"<TD ALIGN=RIGHT>% of root</TD>\n"
	;
		""
	) ++
	( show_quanta(Fields) ->
		"<TD ALIGN=RIGHT>Total quanta</TD>\n"
	;
		""
	) ++
	( show_times(Fields) ->
		"<TD ALIGN=RIGHT>Total time</TD>\n"
	;
		""
	) ++
	( (show_quanta(Fields) ; show_times(Fields)) ->
		"<TD ALIGN=RIGHT>% of root</TD>\n"
	;
		""
	) ++
	( show_allocs(Fields) ->
		"<TD ALIGN=RIGHT>Self allocs</TD>\n" ++
		"<TD ALIGN=RIGHT>% of root</TD>\n" ++
		"<TD ALIGN=RIGHT>Total allocs</TD>\n" ++
		"<TD ALIGN=RIGHT>% of root</TD>\n"
	;
		""
	) ++
	( show_words(Fields) ->
		"<TD ALIGN=RIGHT>Self words</TD>\n" ++
		"<TD ALIGN=RIGHT>% of root</TD>\n" ++
		"<TD ALIGN=RIGHT>Total words</TD>\n" ++
		"<TD ALIGN=RIGHT>% of root</TD>\n"
	;
		""
	) ++
	"</TR>\n".

:- func separator_row(fields) = string.

separator_row(Fields) = Separator :-
	Fixed = 2,	% Kind, Procedure
	( show_port_counts(Fields) ->
		Port = 4
	;
		Port = 4
	),
	( show_quanta(Fields) ->
		Quanta = 2
	;
		Quanta = 0
	),
	( show_times(Fields) ->
		Times = 2
	;
		Times = 0
	),
	( (show_quanta(Fields) ; show_times(Fields)) ->
		Percentage = 2
	;
		Percentage = 0
	),
	( show_allocs(Fields) ->
		Allocs = 4
	;
		Allocs = 0
	),
	( show_words(Fields) ->
		Words = 4
	;
		Words = 0
	),
	Count = Fixed + Port + Quanta + Times + Percentage + Allocs + Words,
	Separator = string__format("<TR><TD COLSPAN=%d>&nbsp;</TD></TR>\n",
		[i(Count)]).

%-----------------------------------------------------------------------------%

:- func clique_to_html(string, clique_ptr, deep, fields) = string.

clique_to_html(URLprefix, CliquePtr, Deep, Fields) = HTML :-
	CliquePtr = clique_ptr(CliqueNum),
	array__lookup(Deep ^ clique_members, CliqueNum, PDPtrs),
	array__lookup(Deep ^ clique_parents, CliqueNum, CallerCSDPtr),
	EntryCallSite = call_site_to_html(URLprefix, Deep, Fields,
		call_site_line_number, CliquePtr, CallerCSDPtr),
	PDStrs = list__map(proc_in_clique_to_html(URLprefix, CliquePtr,
		Deep, Fields), PDPtrs),
	string__append_list(PDStrs, ProcGroups),
	HTML =
		EntryCallSite ++
		ProcGroups.

:- func proc_in_clique_to_html(string, clique_ptr, deep, fields,
	proc_dynamic_ptr) = string.

proc_in_clique_to_html(URLprefix, CliquePtr, Deep, Fields, PDPtr) = HTML :-
	( valid_proc_dynamic_ptr(Deep, PDPtr) ->
		PDPtr = proc_dynamic_ptr(PDI),
		InitialSeparator = separator_row(Fields),
		array__lookup(Deep ^ pd_own, PDI, ProcOwn),
		array__lookup(Deep ^ pd_desc, PDI, ProcDesc),
		array__lookup(Deep ^ proc_dynamics, PDI, PD),
		PD = proc_dynamic(PSPtr, _),
		PSPtr = proc_static_ptr(PSI),
		array__lookup(Deep ^ proc_statics, PSI, PS),
		PS = proc_static(Id, _, _),
		ProcTotal = proc_total_in_clique(Id, Deep, Fields,
			ProcOwn, ProcDesc),
		child_call_sites(Deep ^ proc_dynamics, Deep ^ proc_statics,
			PDPtr, GroupPairs),
		GroupStrs = list__map(call_site_group_to_html(URLprefix,
			Deep, Fields, CliquePtr), GroupPairs),
		string__append_list(GroupStrs, GroupStr0),
		( GroupStrs = [] ->
			GroupStr = GroupStr0
		;
			GroupStr = separator_row(Fields) ++ GroupStr0
		),
		HTML =
			InitialSeparator ++
			ProcTotal ++
			GroupStr
	;
		HTML = ""
	).

:- func proc_total_in_clique(proc_id, deep, fields,
	own_prof_info, inherit_prof_info) = string.

proc_total_in_clique(ProcId, Deep, Fields, Own, Desc) = HTML :-
	ProcName = proc_id_to_string(ProcId),
	HTML = 
		"<TR>\n" ++
		format("<TD COLSPAN=2><B>%s</B></TD>\n", [s(ProcName)]) ++
		own_and_desc_to_html(Own, Desc, Deep, Fields) ++
		"</TR>\n".

:- func call_site_group_to_html(string, deep, fields, clique_ptr,
	pair(call_site_static_ptr, call_site_array_slot)) = string.

call_site_group_to_html(URLprefix, Deep, Fields, ThisCliquePtr, Pair) = HTML :-
	Pair = CSSPtr - CallSiteArray,
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(Deep ^ call_site_statics, CSSI, CSS),
	CSS = call_site_static(Kind, LineNumber, _GoalPath),
	( Kind = normal_call ->
		( CallSiteArray = normal(CSDPtr0) ->
			CSDPtr = CSDPtr0
		;
			error("call_site_group_to_html: normal_call error")
		),
		HTML = call_site_to_html(URLprefix, Deep, Fields,
			call_site_line_number, ThisCliquePtr, CSDPtr)
	;
		( CallSiteArray = multi(CSDPtrs0) ->
			array__to_list(CSDPtrs0, CSDPtrs)
		;
			error("call_site_group_to_html: non-normal_call error")
		),
		Tuple0 = { "", zero_own_prof_info, zero_inherit_prof_info },
		Tuple = list__foldl(call_site_array_to_html(URLprefix,
			Deep, Fields, no_call_site_line_number, ThisCliquePtr),
			CSDPtrs, Tuple0),
		Tuple = { GroupHTML, SumOwn, SumDesc },
		CallSiteName0 = call_site_kind_to_html(Kind),
		( GroupHTML = "" ->
			CallSiteName = CallSiteName0 ++ " (no calls made)"
		;
			CallSiteName = CallSiteName0
		),
		HTML = "<TR>\n" ++
			format("<TD>%d</TD>\n", [i(LineNumber)]) ++
			format("<TD>%s</TD>\n", [s(CallSiteName)]) ++
			own_and_desc_to_html(SumOwn, SumDesc, Deep, Fields) ++
			"</TR>\n" ++
			GroupHTML
	).

:- func call_site_array_to_html(string, deep, fields, call_site_line_number,
	clique_ptr, call_site_dynamic_ptr,
	{string, own_prof_info, inherit_prof_info}) =
	{string, own_prof_info, inherit_prof_info}.

call_site_array_to_html(URLprefix, Deep, Fields, PrintCallSiteLineNmber,
		ThisCliquePtr, CSDPtr, Tuple0) = Tuple :-
	( valid_call_site_dynamic_ptr(Deep, CSDPtr) ->
		CSDPtr = call_site_dynamic_ptr(CSDI),
		Tuple0 = { HTML0, Own0, Desc0 },
		HTML1 = call_site_to_html(URLprefix, Deep, Fields,
			PrintCallSiteLineNmber, ThisCliquePtr, CSDPtr),
		string__append(HTML0, HTML1, HTML),
		array__lookup(Deep ^ call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(_, CallSiteOwn),
		array__lookup(Deep ^ csd_desc, CSDI, CallSiteDesc),
		Own = add_own_to_own(Own0, CallSiteOwn),
		Desc = add_inherit_to_inherit(Desc0, CallSiteDesc),
		Tuple = { HTML, Own, Desc }
	;
		Tuple = Tuple0
	).

:- func call_site_to_html(string, deep, fields, call_site_line_number,
	clique_ptr, call_site_dynamic_ptr) = string.

call_site_to_html(URLprefix, Deep, Fields, PrintCallSiteLineNmber,
		ThisCliquePtr, CSDPtr) = HTML :-
	( valid_call_site_dynamic_ptr(Deep, CSDPtr) ->
		CSDPtr = call_site_dynamic_ptr(CSDI),
		array__lookup(Deep ^ call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(ToPtr, CallSiteOwn),
		array__lookup(Deep ^ csd_desc, CSDI, CallSiteDesc),
		ToPtr = proc_dynamic_ptr(ToInd),
		lookup(Deep ^ clique_index, ToInd, ToCliquePtr),
		CalleeName = label(CSDPtr, Deep),
		( ThisCliquePtr = ToCliquePtr ->
			% We don't link recursive calls
			ProcName = CalleeName
		;
			ToCliquePtr = clique_ptr(ToCliqueNum),
			ProcName =
				format("<A HREF=""%s?clique+%s+%d"">%s</A>\n",
					[s(URLprefix), s(Fields),
					i(ToCliqueNum), s(CalleeName)])
		),
		(
			PrintCallSiteLineNmber = call_site_line_number,
			array__lookup(Deep ^ call_site_caller, CSDI,
				CallSiteCaller),
			CallSiteCaller = call_site_caller(_, _, CSSPtr),
			CSSPtr = call_site_static_ptr(CSSI),
			array__in_bounds(Deep ^ call_site_statics, CSSI),
			array__lookup(Deep ^ call_site_statics, CSSI, CSS),
			CSS = call_site_static(_, LineNumber, _)
		->
			LineNumberField =
				format("<TD>%d</TD>\n", [i(LineNumber)])
		;
			LineNumberField = "<TD> </TD>\n"
		),
		HTML = "<TR>\n" ++
			LineNumberField ++
			format("<TD>%s</TD>\n", [s(ProcName)]) ++
			own_and_desc_to_html(CallSiteOwn, CallSiteDesc,
				Deep, Fields) ++
			"</TR>\n"
	;
		HTML = ""
	).

:- func own_and_desc_to_html(own_prof_info, inherit_prof_info,
	deep, fields) = string.

own_and_desc_to_html(Own, Desc, Deep, Fields) = HTML :-
	add_own_to_inherit(Own, Desc) = OwnPlusDesc,
	Root = root_total_info(Deep),
	Calls = calls(Own),
	Exits = exits(Own),
	Fails = fails(Own),
	Redos = redos(Own),

	OwnQuanta = quanta(Own),
	TotalQuanta = inherit_quanta(OwnPlusDesc),
	RootQuanta = inherit_quanta(Root),
	OwnQuantaProp = 100.0 * float(OwnQuanta) / float(RootQuanta),
	TotalQuantaProp = 100.0 * float(TotalQuanta) / float(RootQuanta),

	OwnAllocs = mallocs(Own),
	TotalAllocs = inherit_mallocs(OwnPlusDesc),
	RootAllocs = inherit_mallocs(Root),
	OwnAllocProp = 100.0 * float(OwnAllocs) / float(RootAllocs),
	TotalAllocProp = 100.0 * float(TotalAllocs) / float(RootAllocs),

	OwnWords = words(Own),
	TotalWords = inherit_words(OwnPlusDesc),
	RootWords = inherit_words(Root),
	OwnWordProp = 100.0 * float(OwnWords) / float(RootWords),
	TotalWordProp = 100.0 * float(TotalWords) / float(RootWords),

	HTML =
		( show_port_counts(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(Calls))]) ++
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(Exits))]) ++
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(Fails))]) ++
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(Redos))])
		;
			""
		) ++
		( show_quanta(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(OwnQuanta))])
		;
			""
		) ++
		( show_times(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(quantum_time(OwnQuanta))])
		;
			""
		) ++
		( (show_quanta(Fields) ; show_times(Fields)) ->
			format("<TD ALIGN=RIGHT>%2.2f</TD>\n",
				[f(OwnQuantaProp)])
		;
			""
		) ++
		( show_quanta(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(TotalQuanta))])
		;
			""
		) ++
		( show_times(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(quantum_time(TotalQuanta))])
		;
			""
		) ++
		( (show_quanta(Fields) ; show_times(Fields)) ->
			format("<TD ALIGN=RIGHT>%2.2f</TD>\n",
				[f(TotalQuantaProp)])
		;
			""
		) ++
		( show_allocs(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(OwnAllocs))]) ++
			format("<TD ALIGN=RIGHT>%2.2f</TD>\n",
				[f(OwnAllocProp)]) ++
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(TotalAllocs))]) ++
			format("<TD ALIGN=RIGHT>%2.2f</TD>\n",
				[f(TotalAllocProp)])
		;
			""
		) ++
		( show_words(Fields) ->
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(OwnWords))]) ++
			format("<TD ALIGN=RIGHT>%2.2f</TD>\n",
				[f(OwnWordProp)]) ++
			format("<TD ALIGN=RIGHT>%s</TD>\n",
				[s(commas(TotalWords))]) ++
			format("<TD ALIGN=RIGHT>%2.2f</TD>\n",
				[f(TotalWordProp)])
		;
			""
		).

%-----------------------------------------------------------------------------%

:- func procs2html(string, deep, sort, fields, int, int) = string.

procs2html(URLprefix, Deep, Sort, _Fields, First, Last) = HTML :-
	array_foldl((pred(PSI::in, _PS::in, Xs0::in, Xs::out) is det :-
	(
		PSI >= First,
		PSI =< Last
	->
		Row = proc2html(URLprefix, Deep, PSI, OwnQuanta, Quanta),
		(
			Sort = self,
			K = OwnQuanta
		;
			Sort = self_and_desc,
			K = Quanta
		),
		X = {K, Row},
		Xs = [X|Xs0]
	;
		Xs = Xs0
	)), Deep ^ proc_statics, [], KeyedRows0),
	sort(KeyedRows0, KeyedRows),
	foldl((pred({_, RStr}::in, Strs1::in, Strs2::out) is det :-
		Strs2 = [RStr|Strs1]
	), KeyedRows, [], RowStrs),
	append_list(RowStrs, HTML).

:- type boldness
	--->	normal
	;	bold.

:- func proc_summary_to_html(string, deep, fields, int) = string.

proc_summary_to_html(URLprefix, Deep, Fields, PSI) = HTML :-
	lookup(Deep ^ proc_statics, PSI, PS),
	PS = proc_static(_, _, CSSPtrsArray),
	array__to_list(CSSPtrsArray, CSSPtrs),
	map((pred(CSSPtr::in, CSSStr::out) is det :-
		CSSPtr = call_site_static_ptr(CSSI),
		( CSSI > 0 ->
			CSSStr = call_site_summary_to_html(Deep, Fields, CSSPtr)
		;
			CSSStr = ""
		)
	), CSSPtrs, CallSiteSummaryList),
	string__append_list(CallSiteSummaryList, CallSiteSummaries),
	HTML =
		proc2html(bold, URLprefix, Deep, PSI, _, _) ++
		CallSiteSummaries.

:- func proc2html(string, deep, int, int, int) = string.
:- mode (proc2html(in, in, in, out, out) = out) is det.

proc2html(URLprefix, Deep, PSI, OwnQuanta, Quanta) =
	proc2html(normal, URLprefix, Deep, PSI, OwnQuanta, Quanta).

:- func proc2html(boldness, string, deep, int, int, int) = string.
:- mode (proc2html(in, in, in, in, out, out) = out) is det.

proc2html(Boldness, _URLprefix, Deep, PSI, OwnQuanta, Quanta) = HTML :-
	lookup(Deep ^ proc_statics, PSI, PS),
	PS = proc_static(Id, _, _),
	lookup(Deep ^ ps_own, PSI, PI),
	Calls = calls(PI), Exits = exits(PI),
	Fails = fails(PI), Redos = redos(PI),
	OwnQuanta = quanta(PI),
	lookup(Deep ^ ps_desc, PSI, PSIDesc),
	DescQuanta = inherit_quanta(PSIDesc),
	Quanta = OwnQuanta + DescQuanta,
	OwnQ = float(OwnQuanta),
	Q = float(Quanta),
	RootQuanta = inherit_quanta(RootTotal),
	RQ = float(RootQuanta),
	OwnProp = 100.0 * OwnQ / RQ,
	Prop = 100.0 * Q / RQ,
	RootTotal = root_total_info(Deep),
	(
		Boldness = normal,
		BS = "",
		BE = ""
	;
		Boldness = bold,
		BS = "<B>",
		BE = "</B>"
	),
	HTML = "<TR>\n" ++
	 "<TD> </TD>\n" ++
	 format("<TD>%s%s%s</TD>\n",
	 	[s(BS), s(proc_id_to_string(Id)), s(BE)]) ++
	 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Calls))]) ++
	 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Exits))]) ++
	 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Fails))]) ++
	 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Redos))]) ++
	 format("<TD ALIGN=RIGHT>%s</TD>\n",[s(commas(OwnQuanta))]) ++
	 format("<TD ALIGN=RIGHT>%0.2f</TD>\n", [f(OwnProp)]) ++
	 format("<TD ALIGN=RIGHT>%s</TD>\n", [s(commas(Quanta))]) ++
	 format("<TD ALIGN=RIGHT>%0.2f</TD>\n", [f(Prop)]) ++
		"</TR>\n".

%-----------------------------------------------------------------------------%

:- func call_site_summary_to_html(deep, string, call_site_static_ptr) = string.

call_site_summary_to_html(Deep, Fields, CSSPtr) = HTML :-
	CSSPtr = call_site_static_ptr(CSSI),
	array__lookup(Deep ^ css_own, CSSI, Own),
	array__lookup(Deep ^ css_desc, CSSI, Desc),
	array__lookup(Deep ^ call_site_statics, CSSI, CSS),
	CSS = call_site_static(Kind, LineNumber, _GoalPath),
	array__lookup(Deep ^ call_site_calls, CSSI, CallSiteCallMap),
	map__to_assoc_list(CallSiteCallMap, CallSiteCallList),
	( Kind = normal_call ->
		( CallSiteCallList = [CallSiteCall] ->
			CallSiteCall = PSPtr - _CallSet,
			PSPtr = proc_static_ptr(PSI),
			array__lookup(Deep ^ proc_statics, PSI, PS),
			PS = proc_static(ProcId, _, _)
		;
			error("normal call site calls more than one procedure")
		),
		MainLineRest =
			format("<TD>%s</TD>\n",
				[s(proc_id_to_string(ProcId))]) ++
			own_and_desc_to_html(Own, Desc, Deep, Fields),
		AdditionalLines = ""
	;
		CallSiteName0 = call_site_kind_to_html(Kind),
		( CallSiteCallList = [] ->
			CallSiteName = CallSiteName0 ++ " (no calls made)"
		;
			CallSiteName = CallSiteName0
		),
		MainLineRest =
			format("<TD>%s</TD>\n",
				[s(CallSiteName)]) ++
			own_and_desc_to_html(Own, Desc, Deep, Fields),
		CallSiteCallLines = list__map(
			call_site_summary_group_to_html(Deep, Fields),
			CallSiteCallList),
		string__append_list(CallSiteCallLines, AdditionalLines)
	),
	HTML =
		"<TR>\n" ++
		format("<TD>%d</TD>\n", [i(LineNumber)]) ++
		MainLineRest ++
		"</TR>\n" ++
		AdditionalLines.

:- func call_site_kind_to_html(call_site_kind) = string.

call_site_kind_to_html(normal_call) =       "normal_call".
call_site_kind_to_html(special_call) =      "special_call".
call_site_kind_to_html(higher_order_call) = "higher_order_call".
call_site_kind_to_html(method_call) =       "method_call".
call_site_kind_to_html(callback) =          "callback".

:- func call_site_summary_group_to_html(deep, string,
	pair(proc_static_ptr, set(call_site_dynamic_ptr))) = string.

call_site_summary_group_to_html(Deep, Fields, PSPtr - CSDPtrSet) = HTML :-
	PSPtr = proc_static_ptr(PSI),
	array__lookup(Deep ^ proc_statics, PSI, PS),
	PS = proc_static(ProcId, _, _),
	set__to_sorted_list(CSDPtrSet, CSDPtrs),
	CallSiteDynamics = Deep ^ call_site_dynamics,
	CallSiteDescs = Deep ^ csd_desc,
	list__foldl2(accumulate_csd_prof_info(CallSiteDynamics, CallSiteDescs),
		CSDPtrs, zero_own_prof_info, Own,
		zero_inherit_prof_info, Desc),
	HTML =
		"<TR>\n" ++
		format("<TD>%s</TD>\n", [s(proc_id_to_string(ProcId))]) ++
		own_and_desc_to_html(Own, Desc, Deep, Fields) ++
		"</TR>\n".

:- pred accumulate_csd_prof_info(
	call_site_dynamics::in, array(inherit_prof_info)::in,
	call_site_dynamic_ptr::in,
	own_prof_info::in, own_prof_info::out,
	inherit_prof_info::in, inherit_prof_info::out) is det.

accumulate_csd_prof_info(CallSiteDynamics, CSDDescs, CSDPtr,
		Own0, Own, Desc0, Desc) :-
	CSDPtr = call_site_dynamic_ptr(CSDI),
	array__lookup(CallSiteDynamics, CSDI, CSD),
	CSD = call_site_dynamic(_, CSDOwn),
	array__lookup(CSDDescs, CSDI, CSDDesc),

	add_own_to_own(Own0, CSDOwn) = Own,
	add_inherit_to_inherit(Desc0, CSDDesc) = Desc.

%-----------------------------------------------------------------------------%

:- func label(call_site_dynamic_ptr, deep) = string.

label(CSDPtr, Deep) = Name :-
	(
		CSDPtr = call_site_dynamic_ptr(CSDI), CSDI > 0,
		lookup(Deep ^ call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(PDPtr, _),
		PDPtr = proc_dynamic_ptr(PDI), PDI > 0,
		lookup(Deep ^ proc_dynamics, PDI, PD),
		PD = proc_dynamic(PSPtr, _),
		PSPtr = proc_static_ptr(PSI), PSI > 0,
		lookup(Deep ^ proc_statics, PSI, PS),
		PS = proc_static(Id, _, _)
	->
		Name = proc_id_to_string(Id)
	;
		Name = "-"
	).

:- func refs(call_site_dynamic_ptr, deep) = array(call_site_array_slot).

refs(CSDPtr, Deep) = CallSiteArraySlots :-
	(
		CSDPtr = call_site_dynamic_ptr(CSDI), CSDI > 0,
		lookup(Deep ^ call_site_dynamics, CSDI, CSD),
		CSD = call_site_dynamic(PDPtr, _),
		PDPtr = proc_dynamic_ptr(PDI), PDI > 0,
		lookup(Deep ^ proc_dynamics, PDI, PD),
		PD = proc_dynamic(_, CallSiteArraySlots0)
	->
		CallSiteArraySlots = CallSiteArraySlots0
	;
		CallSiteArraySlots = array([])
	).

%-----------------------------------------------------------------------------%

:- pred valid_clique_ptr(deep::in, clique_ptr::in) is semidet.

valid_clique_ptr(Deep, clique_ptr(CliqueNum)) :-
	CliqueNum > 0,
	array__in_bounds(Deep ^ clique_members, CliqueNum).

:- pred valid_proc_dynamic_ptr(deep::in, proc_dynamic_ptr::in) is semidet.

valid_proc_dynamic_ptr(Deep, proc_dynamic_ptr(PDI)) :-
	PDI > 0,
	array__in_bounds(Deep ^ proc_dynamics, PDI).

:- pred valid_proc_static_ptr(deep::in, proc_static_ptr::in) is semidet.

valid_proc_static_ptr(Deep, proc_static_ptr(PSI)) :-
	PSI > 0,
	array__in_bounds(Deep ^ proc_statics, PSI).

:- pred valid_call_site_dynamic_ptr(deep::in, call_site_dynamic_ptr::in)
	is semidet.

valid_call_site_dynamic_ptr(Deep, call_site_dynamic_ptr(CSDI)) :-
	CSDI > 0,
	array__in_bounds(Deep ^ call_site_dynamics, CSDI).

:- pred valid_call_site_static_ptr(deep::in, call_site_static_ptr::in)
	is semidet.

valid_call_site_static_ptr(Deep, call_site_static_ptr(CSSI)) :-
	CSSI > 0,
	array__in_bounds(Deep ^ call_site_statics, CSSI).

%-----------------------------------------------------------------------------%

:- func quantum_time(int) = string.

quantum_time(Quanta) = TimeStr :-
	Time = Quanta * 10,	% a quantum is 10 milliseconds on our machines
	format("%d", [i(Time)], Str0),
	string__to_char_list(Str0, Chars0),
	reverse(Chars0, RevChars0),
	string__from_char_list(reverse(
		milliseconds_to_seconds(RevChars0)), TimeStr).

:- func commas(int) = string.

commas(Num) = Str :-
	format("%d", [i(Num)], Str0),
	string__to_char_list(Str0, Chars0),
	reverse(Chars0, RevChars0),
	string__from_char_list(reverse(add_commas(RevChars0)), Str).

:- func milliseconds_to_seconds([char]) = [char].

milliseconds_to_seconds([]) = ['0', '0', '.', '0'].
milliseconds_to_seconds([_C]) = ['0', '0', '.', '0'].
milliseconds_to_seconds([_C, D]) = [D, '0', '.', '0'].
milliseconds_to_seconds([_C, D, E]) = [D, E, '.', '0'].
milliseconds_to_seconds([_C, D, E, F | R]) = [D, E, '.' | add_commas([F | R])].

:- func add_commas([char]) = [char].

add_commas([]) = [].
add_commas([C]) = [C].
add_commas([C, D]) = [C, D].
add_commas([C, D, E]) = [C, D, E].
add_commas([C, D, E, F | R]) = [C, D, E, (',') | add_commas([F | R])].

%-----------------------------------------------------------------------------%

:- pred show_port_counts(fields::in) is semidet.

show_port_counts(Fields) :-
	string__contains_char(Fields, 'p').

:- pred show_quanta(fields::in) is semidet.

show_quanta(Fields) :-
	string__contains_char(Fields, 'q').

:- pred show_times(fields::in) is semidet.

show_times(Fields) :-
	string__contains_char(Fields, 't').

:- pred show_allocs(fields::in) is semidet.

show_allocs(Fields) :-
	string__contains_char(Fields, 'a').

:- pred show_words(fields::in) is semidet.

show_words(Fields) :-
	string__contains_char(Fields, 'w').
