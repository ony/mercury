%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module deep:server.

:- interface.

:- pred test_server(string::in, string::in, deep::in, string::in,
	io__state::di, io__state::uo) is det.

:- pred server_loop(string::in, string::in, int::in, string::in, deep::in,
	io__state::di, io__state::uo) is det.

:- implementation.

:- import_module cgi_interface, measurements, deep:util.
:- import_module int, string, float, require.

:- type call_site_line_number
	--->	call_site_line_number
	;	no_call_site_line_number.

%-----------------------------------------------------------------------------%

test_server(DirName, URLprefix, Deep, Fields) -->
	{ array__max(Deep ^ clique_members, NumCliques) },
	test_cliques(1, NumCliques, DirName, URLprefix, Deep, Fields),
	{ array__max(Deep ^ proc_statics, NumProcStatics) },
	test_procs(1, NumProcStatics, DirName, URLprefix, Deep, Fields).

:- pred test_cliques(int::in, int::in, string::in, string::in, deep::in,
	string::in, io__state::di, io__state::uo) is det.

test_cliques(Cur, Max, DirName, URLprefix, Deep, Fields) -->
	( { Cur =< Max } ->
		{ exec(clique(Cur, Fields), URLprefix, Deep, HTML, _) },
		write_html(DirName, "clique", Cur, HTML),
		test_cliques(Cur + 1, Max, DirName, URLprefix, Deep, Fields)
	;
		[]
	).

:- pred test_procs(int::in, int::in, string::in, string::in, deep::in,
	string::in, io__state::di, io__state::uo) is det.

test_procs(Cur, Max, DirName, URLprefix, Deep, Fields) -->
	( { Cur =< Max } ->
		{ exec(proc(Cur, Fields), URLprefix, Deep, HTML, _) },
		write_html(DirName, "proc", Cur, HTML),
		test_procs(Cur + 1, Max, DirName, URLprefix, Deep, Fields)
	;
		[]
	).

:- pred write_html(string::in, string::in, int::in, string::in,
	io__state::di, io__state::uo) is det.

write_html(DirName, BaseName, Num, HTML) -->
	{ string__format("%s/%s_%d.html", [s(DirName), s(BaseName), i(Num)],
		FileName) },
	io__tell(FileName, _),
	io__write_string(HTML),
	io__told.

%-----------------------------------------------------------------------------%

server_loop(InputFileName, OutputFileName, Wait, URLprefix, Deep) -->
	io__see(InputFileName, _),
	read(Res0),
	% stderr_stream(StdErr),
	% write(StdErr, Res0), nl(StdErr),
	io__seen,
	(
		{ Res0 = eof },
		% write_string(StdErr, "eof.\n"),
		server_loop(InputFileName, OutputFileName, Wait,
			URLprefix, Deep)
	;
		{ Res0 = error(Msg, Line) },
		stderr_stream(StdErr),
		format(StdErr, "error reading input line %d: %s\n",
			[i(Line), s(Msg)]),
		server_loop(InputFileName, OutputFileName, Wait,
			URLprefix, Deep)
	;
		{ Res0 = ok(Cmd) },
		{ exec(Cmd, URLprefix, Deep, HTML, Continue) },
		io__tell(OutputFileName, _),
		io__write(html(HTML)),
		io__write_string(".\n"),
		io__told,
		% ( { Wait > 0 } ->
		% 	{ wait(Wait) }
		% ;
		% 	[]
		% ),
		(
			{ Continue = yes },
			server_loop(InputFileName, OutputFileName, Wait,
				URLprefix, Deep)
		;
			{ Continue = no }
		)
	).

% :- pred wait(int::in) is det.
% 
% :- pragma foreign_code("C", wait(Seconds::in), [will_not_call_mercury], "
% 	#include <unistd.h>
% 	sleep(Seconds);
% ").

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
		menu_item(URLprefix,
			add_default_fields("root"),
			"Exploring the call graph.") ++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+time+self+1-100"),
			"Top 100 most expensive procedures: time, self.") ++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+time+both+1-100"),
			"Top 100 most expensive procedures: time, self+desc.")
			++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+words+self+1-100"),
			"Top 100 most expensive procedures: words, self.") ++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+words+both+1-100"),
			"Top 100 most expensive procedures: words, self+desc.")
			++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+time+self+0.1"),
			"Procedures above 0.1% threshold: time, self.") ++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+time+both+1"),
			"Procedures above 1% threshold: time, self+desc.")
			++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+words+self+0.1"),
			"Procedures above 0.1% threshold: words, self.") ++
		"<li>\n" ++
		menu_item(URLprefix,
			add_default_fields("procs+words+both+1"),
			"Procedures above 1% threshold: words, self+desc.")
			++
		"</ul>\n" ++
		"<p>\n" ++
		present_stats(Deep ^ profile_stats) ++
		"<p>\n" ++
		footer(URLprefix, Cmd, Deep).

exec(Cmd, URLprefix, Deep, HTML, Continue) :-
	Cmd = root(Fields),
	deep_lookup_clique_index(Deep, Deep ^ root, RootCliquePtr),
	RootCliquePtr = clique_ptr(RootCliqueNum),
	exec(clique(RootCliqueNum, Fields), URLprefix, Deep, HTML, Continue).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = clique(CliqueNum, Fields),
	( valid_clique_ptr(Deep, clique_ptr(CliqueNum)) ->
		HTML =
			banner ++
			"<TABLE>\n" ++
			fields_header(Fields) ++
			clique_to_html(URLprefix, Deep, Fields,
				clique_ptr(CliqueNum)) ++
			"</TABLE>\n" ++
			footer(URLprefix, Cmd, Deep)
	;
		HTML =
			banner ++
			"There is no clique with that number.\n" ++
			footer(URLprefix, Cmd, Deep)
	).

exec(Cmd, URLprefix, Deep, HTML, yes) :-
	Cmd = top_procs(Sort, InclDesc, Limit, Fields),
	find_top_procs(Sort, InclDesc, Limit, Deep, MaybeTopPSIs),
	(
		MaybeTopPSIs = error(ErrorMessage),
		HTML =
			banner ++
			ErrorMessage ++ "\n" ++
			footer(URLprefix, Cmd, Deep)
	;
		MaybeTopPSIs = ok(TopPSIs),
		( TopPSIs = [] ->
			HTML =
				banner ++
				"No procedures match the specification.\n" ++
				footer(URLprefix, Cmd, Deep)
		;
			TopProcSummaries = list__map(
				proc_total_summary_to_html(URLprefix,
					Deep, Fields),
				TopPSIs),
			HTML =
				banner ++
				"<TABLE>\n" ++
				fields_header(Fields) ++
				string__append_list(TopProcSummaries) ++
				"</TABLE>\n" ++
				footer(URLprefix, Cmd, Deep)
		)
	).

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

exec(Cmd, _URLprefix, Deep, HTML, yes) :-
	Cmd = proc_static(PSI),
	PSPtr = proc_static_ptr(PSI),
	( valid_proc_static_ptr(Deep, PSPtr) ->
		deep_lookup_proc_statics(Deep, PSPtr, PS),
		Refined = PS ^ ps_refined_id,
		Raw = PS ^ ps_raw_id,
		FileName = PS ^ ps_filename,
		HTML =
			"<HTML>\n" ++
			Refined ++ " " ++ Raw ++ " " ++ FileName ++ " " ++
			string__int_to_string(array__max(PS ^ ps_sites)) ++
			"</HTML>\n"
	;
		HTML =
			"<HTML>\n" ++
			"Invalid proc_static_ptr" ++
			"</HTML>\n"
	).

exec(Cmd, _URLprefix, Deep, HTML, yes) :-
	Cmd = call_site_static(CSSI),
	CSSPtr = call_site_static_ptr(CSSI),
	( valid_call_site_static_ptr(Deep, CSSPtr) ->
		deep_lookup_call_site_statics(Deep, CSSPtr, CSS),
		ContainerPtr = CSS ^ css_container,
		ContainerPtr = proc_static_ptr(Container),
		HTML =
			"<HTML>\n" ++
			string__int_to_string(Container) ++ " " ++
			string__int_to_string(CSS ^ css_slot_num) ++ " " ++
			string__int_to_string(CSS ^ css_line_num) ++ " " ++
			kind_and_callee_to_string(CSS ^ css_kind) ++ " " ++
			CSS ^ css_goal_path ++
			"</HTML>\n"
	;
		HTML =
			"<HTML>\n" ++
			"Invalid call_site_static_ptr" ++
			"</HTML>\n"
	).

exec(Cmd, _URLprefix, Deep, HTML, yes) :-
	Cmd = num_proc_dynamics,
	HTML =
		"<HTML>\n" ++
		string__int_to_string(Deep ^ profile_stats ^ num_pds) ++
		"</HTML>\n".

exec(Cmd, _URLprefix, Deep, HTML, yes) :-
	Cmd = num_call_site_dynamics,
	HTML =
		"<HTML>\n" ++
		string__int_to_string(Deep ^ profile_stats ^ num_csds) ++
		"</HTML>\n".

exec(Cmd, _URLprefix, Deep, HTML, yes) :-
	Cmd = num_proc_statics,
	HTML =
		"<HTML>\n" ++
		string__int_to_string(Deep ^ profile_stats ^ num_pss) ++
		"</HTML>\n".

exec(Cmd, _URLprefix, Deep, HTML, yes) :-
	Cmd = num_call_site_statics,
	HTML =
		"<HTML>\n" ++
		string__int_to_string(Deep ^ profile_stats ^ num_csss) ++
		"</HTML>\n".

%-----------------------------------------------------------------------------%

:- func kind_and_callee_to_string(call_site_kind_and_callee) = string.

kind_and_callee_to_string(normal_call(proc_static_ptr(PSI), TypeSpec)) =
	"normal " ++ string__int_to_string(PSI) ++ " " ++ TypeSpec.
kind_and_callee_to_string(special_call) = "special_call".
kind_and_callee_to_string(higher_order_call) = "higher_order_call".
kind_and_callee_to_string(method_call) = "method_call".
kind_and_callee_to_string(callback) = "callback".

:- func present_stats(profile_stats) = string.

present_stats(Stats) = HTML :-
	HTML =
		"<TABLE>\n" ++
		"<TR><TD ALIGN=left>Quanta in user code:</TD>\n" ++
		format("<TD ALIGN=right>%d</TD></TR>\n",
			[i(Stats ^ user_quanta)]) ++
		"<TR><TD ALIGN=left>Quanta in instrumentation:</TD>\n" ++
		format("<TD ALIGN=right>%d</TD></TR>\n",
			[i(Stats ^ instrument_quanta)]) ++
		"<TR><TD ALIGN=left>CallSiteDynamic structures:</TD>\n" ++
		format("<TD ALIGN=right>%d</TD></TR>\n",
			[i(Stats ^ num_csds)]) ++
		"<TR><TD ALIGN=left>ProcDynamic structures:</TD>\n" ++
		format("<TD ALIGN=right>%d</TD></TR>\n",
			[i(Stats ^ num_pds)]) ++
		"<TR><TD ALIGN=left>CallSiteStatic structures:</TD>\n" ++
		format("<TD ALIGN=right>%d</TD></TR>\n",
			[i(Stats ^ num_csss)]) ++
		"<TR><TD ALIGN=left>ProcStatic structures:</TD>\n" ++
		format("<TD ALIGN=right>%d</TD></TR>\n",
			[i(Stats ^ num_pss)]) ++
		"</TABLE>\n".

%-----------------------------------------------------------------------------%

:- func clique_to_html(string, deep, fields, clique_ptr) = string.

clique_to_html(URLprefix, Deep, Fields, CliquePtr) = HTML :-
	Ancestors = clique_ancestors_to_html(URLprefix, Deep, Fields,
		CliquePtr),
	deep_lookup_clique_members(Deep, CliquePtr, PDPtrs),
	list__foldl(group_proc_dynamics_by_proc_static(Deep), PDPtrs,
		map__init, PStoPDsMap),
	map__to_assoc_list(PStoPDsMap, PStoPDsList0),

	deep_lookup_clique_parents(Deep, CliquePtr, EntryCSDPtr),
	( valid_call_site_dynamic_ptr(Deep, EntryCSDPtr) ->
		deep_lookup_call_site_dynamics(Deep, EntryCSDPtr, EntryCSD),
		EntryPDPtr = EntryCSD ^ csd_callee,
		list__filter(proc_group_contains(EntryPDPtr), PStoPDsList0,
			EntryGroup, RestGroup),
		list__append(EntryGroup, RestGroup, PStoPDsList)
	;
		PStoPDsList = PStoPDsList0
	),

	PDsStrs = list__map(
		procs_in_clique_to_html(URLprefix, Deep, Fields, CliquePtr),
		PStoPDsList),
	string__append_list(PDsStrs, ProcGroups),
	HTML =
		Ancestors ++
		ProcGroups.

:- pred proc_group_contains(proc_dynamic_ptr::in,
	pair(proc_static_ptr, list(proc_dynamic_ptr))::in) is semidet.

proc_group_contains(EntryPDPtr, _ - PDPtrs) :-
	list__member(EntryPDPtr, PDPtrs).

:- func clique_ancestors_to_html(string, deep, fields, clique_ptr) = string.

clique_ancestors_to_html(URLprefix, Deep, Fields, CliquePtr) = HTML :-
	deep_lookup_clique_index(Deep, Deep ^ root, RootCliquePtr),
	( CliquePtr = RootCliquePtr ->
		HTML = ""
	;
		deep_lookup_clique_parents(Deep, CliquePtr, EntryCSDPtr),
		ThisHTML = call_site_dynamic_to_html(URLprefix, Deep, Fields,
			call_site_line_number, no, EntryCSDPtr),
		deep_lookup_call_site_dynamics(Deep, EntryCSDPtr, EntryCSD),
		EntryCSD = call_site_dynamic(EntryPDPtr, _, _),
		require(valid_proc_dynamic_ptr(Deep, EntryPDPtr),
			"clique_ancestors_to_html: invalid proc_dynamic"),
		deep_lookup_clique_index(Deep, EntryPDPtr, EntryCliquePtr),
		AncestorHTML = clique_ancestors_to_html(URLprefix,
			Deep, Fields, EntryCliquePtr),
		HTML =
			AncestorHTML ++
			ThisHTML
	).

:- pred group_proc_dynamics_by_proc_static(deep::in, proc_dynamic_ptr::in,
	map(proc_static_ptr, list(proc_dynamic_ptr))::in,
	map(proc_static_ptr, list(proc_dynamic_ptr))::out) is det.

group_proc_dynamics_by_proc_static(Deep, PDPtr, PStoPDsMap0, PStoPDsMap) :-
	require(valid_proc_dynamic_ptr(Deep, PDPtr),
		"group_proc_dynamics_by_proc_static: invalid PDPtr"),
	deep_lookup_proc_dynamics(Deep, PDPtr, PD),
	PSPtr = PD ^ pd_proc_static,
	( map__search(PStoPDsMap0, PSPtr, PSPDs0) ->
		PSPDs = [PDPtr | PSPDs0],
		map__det_update(PStoPDsMap0, PSPtr, PSPDs, PStoPDsMap)
	;
		map__det_insert(PStoPDsMap0, PSPtr, [PDPtr], PStoPDsMap)
	).

:- func procs_in_clique_to_html(string, deep, fields,
	clique_ptr, pair(proc_static_ptr, list(proc_dynamic_ptr))) = string.

procs_in_clique_to_html(URLprefix, Deep, Fields, CliquePtr, PSPtr - PDPtrs)
		= HTML :-
	InitialSeparator = separator_row(Fields),
	list__map(deep_lookup_pd_own(Deep), PDPtrs, ProcOwns),
	list__map(deep_lookup_pd_desc(Deep), PDPtrs, ProcDescs),
	ProcOwn = sum_own_infos(ProcOwns),
	ProcDesc = sum_inherit_infos(ProcDescs),
	ProcTotal = proc_total_in_clique(URLprefix, Deep, Fields,
		PSPtr, ProcOwn, ProcDesc),
	deep_lookup_proc_statics(Deep, PSPtr, PS),
	CSSPtrs = PS ^ ps_sites,
	array__max(CSSPtrs, CSSMax),
	list__map(deep_lookup_proc_dynamic_sites(Deep), PDPtrs, PDSites),
	Group0 = call_site_groups_to_html(URLprefix, Deep, Fields,
		CliquePtr, 0, CSSMax, CSSPtrs, PDSites),
	( Group0 = "" ->
		Group = Group0
	;
		Group = separator_row(Fields) ++ Group0
	),
	HTML =
		InitialSeparator ++
		ProcTotal ++
		Group.

:- func proc_total_in_clique(string, deep, fields,
	proc_static_ptr, own_prof_info, inherit_prof_info) = string.

proc_total_in_clique(URLprefix, Deep, Fields, PSPtr, Own, Desc) = HTML :-
	ProcName = proc_static_to_html_ref(URLprefix, Deep, Fields, PSPtr),
	HTML = 
		"<TR>\n" ++
		format("<TD COLSPAN=2><B>%s</B></TD>\n", [s(ProcName)]) ++
		own_and_desc_to_html(Own, Desc, Deep, Fields) ++
		"</TR>\n".

:- func lookup_pd_site(int, array(call_site_array_slot))
	= call_site_array_slot.

lookup_pd_site(SlotNum, SlotArray) = Slot :-
	array__lookup(SlotArray, SlotNum, Slot).

:- func extract_normal_slot(call_site_array_slot) = call_site_dynamic_ptr.

extract_normal_slot(normal(CSDPtr)) = CSDPtr.
extract_normal_slot(multi(_)) = _ :-
	error("extract_normal_slot: found multi").

:- func extract_multi_slot(call_site_array_slot) = list(call_site_dynamic_ptr).

extract_multi_slot(normal(_)) = _ :-
	error("extract_multi_slot: found normal").
extract_multi_slot(multi(CSDPtrArray)) = CSDPtrs :-
	array__to_list(CSDPtrArray, CSDPtrs).

:- pred compare_csd_pd_ptrs(deep::in,
	call_site_dynamic_ptr::in, call_site_dynamic_ptr::in,
	comparison_result::out) is det.

compare_csd_pd_ptrs(Deep, CSDPtr1, CSDPtr2, Res) :-
	deep_lookup_call_site_dynamics(Deep, CSDPtr1, CSD1),
	deep_lookup_call_site_dynamics(Deep, CSDPtr2, CSD2),
	PDPtr1 = CSD1 ^ csd_callee,
	PDPtr2 = CSD2 ^ csd_callee,
	PDPtr1 = proc_dynamic_ptr(PDI1),
	PDPtr2 = proc_dynamic_ptr(PDI2),
	compare(Res, PDI1, PDI2).

:- pred group_call_site_dynamics_by_proc_static(deep::in,
	call_site_dynamic_ptr::in,
	map(proc_static_ptr, list(call_site_dynamic_ptr))::in,
	map(proc_static_ptr, list(call_site_dynamic_ptr))::out) is det.

group_call_site_dynamics_by_proc_static(Deep, CSDPtr,
		PStoCSDsMap0, PStoCSDsMap) :-
	( valid_call_site_dynamic_ptr(Deep, CSDPtr) ->
		deep_lookup_call_site_dynamics(Deep, CSDPtr, CSD),
		PDPtr = CSD ^ csd_callee,
		( valid_proc_dynamic_ptr(Deep, PDPtr) ->
			deep_lookup_proc_dynamics(Deep, PDPtr, PD),
			PSPtr = PD ^ pd_proc_static
		;
			PSPtr = proc_static_ptr(-1)
		),
		( map__search(PStoCSDsMap0, PSPtr, PSCSDs0) ->
			PSCSDs = [CSDPtr | PSCSDs0],
			map__det_update(PStoCSDsMap0, PSPtr, PSCSDs,
				PStoCSDsMap)
		;
			map__det_insert(PStoCSDsMap0, PSPtr, [CSDPtr],
				PStoCSDsMap)
		)
	;
		PStoCSDsMap = PStoCSDsMap0
	).

:- func call_site_groups_to_html(string, deep, fields, clique_ptr, int, int,
	array(call_site_static_ptr), list(array(call_site_array_slot)))
	= string.

call_site_groups_to_html(URLprefix, Deep, Fields, ThisCliquePtr, Cur, Max,
		CSSs, PDSiteArrays) = HTML :-
	( Cur > Max ->
		HTML = ""
	;
		ThisHTML = call_site_group_to_html(URLprefix, Deep, Fields,
			ThisCliquePtr, Cur, CSSs, PDSiteArrays),
		RestHTML = call_site_groups_to_html(URLprefix, Deep, Fields,
			ThisCliquePtr, Cur + 1, Max, CSSs, PDSiteArrays),
		HTML = ThisHTML ++ RestHTML
	).

:- func call_site_group_to_html(string, deep, fields, clique_ptr, int,
	array(call_site_static_ptr), list(array(call_site_array_slot)))
	= string.

call_site_group_to_html(URLprefix, Deep, Fields, ThisCliquePtr, Cur,
		CSSPtrs, PDSiteArrays) = HTML :-
	array__lookup(CSSPtrs, Cur, CSSPtr),
	PDSites = list__map(lookup_pd_site(Cur), PDSiteArrays),
	deep_lookup_call_site_statics(Deep, CSSPtr, CSS),
	PSPtr = CSS ^ css_container,
	deep_lookup_proc_statics(Deep, PSPtr, PS),
	FileName = PS ^ ps_filename,
	LineNumber = CSS ^ css_line_num,
	Kind = CSS ^ css_kind,
	( Kind = normal_call(CalleePSPtr, _) ->
		CSDPtrs0 = list__map(extract_normal_slot, PDSites),
		list__filter(valid_call_site_dynamic_ptr(Deep),
			CSDPtrs0, CSDPtrs),
		process_call_site_dynamics_group(CSDPtrs, Deep, CalleePSPtr,
			no, MaybeToCliquePtr, zero_own_prof_info, Own,
			zero_inherit_prof_info, Desc),
		(
			MaybeToCliquePtr = no,
			HTML = ""
		;
			MaybeToCliquePtr = yes(ToCliquePtr),
			HTML = call_site_dynamics_to_html(URLprefix,
				Deep, Fields, yes(FileName - LineNumber),
				ThisCliquePtr, ToCliquePtr, CalleePSPtr,
				Own, Desc)
		)
	;
		CSDPtrLists = list__map(extract_multi_slot, PDSites),
		list__condense(CSDPtrLists, CSDPtrs0),
		list__filter(valid_call_site_dynamic_ptr(Deep),
			CSDPtrs0, CSDPtrs1),
		list__foldl(group_call_site_dynamics_by_proc_static(Deep),
			CSDPtrs1, map__init, PStoCSDsMap),
		map__to_assoc_list(PStoCSDsMap, PStoCSDsList),
		Tuple0 = { "", zero_own_prof_info, zero_inherit_prof_info },
		Tuple = list__foldl(call_site_array_to_html(URLprefix,
			Deep, Fields, ThisCliquePtr), PStoCSDsList, Tuple0),
		Tuple = { GroupHTML, SumOwn, SumDesc },
		( GroupHTML = "" ->
			HTML = ""
		;
			CallSiteName = call_site_kind_and_callee_to_html(Kind),
			HTML =
				"<TR>\n" ++
				format("<TD>%s:%d</TD>\n",
					[s(FileName), i(LineNumber)]) ++
				format("<TD>%s</TD>\n", [s(CallSiteName)]) ++
				own_and_desc_to_html(SumOwn, SumDesc,
					Deep, Fields) ++
				"</TR>\n" ++
				GroupHTML
		)
	).

:- func call_site_array_to_html(string, deep, fields, clique_ptr,
	pair(proc_static_ptr, list(call_site_dynamic_ptr)),
	{string, own_prof_info, inherit_prof_info}) =
	{string, own_prof_info, inherit_prof_info}.

call_site_array_to_html(URLprefix, Deep, Fields, ThisCliquePtr,
		PSPtr - CSDPtrs, Tuple0) = Tuple :-
	Tuple0 = { HTML0, GroupOwn0, GroupDesc0 },
	process_call_site_dynamics_group(CSDPtrs, Deep, PSPtr,
		no, MaybeToCliquePtr, zero_own_prof_info, Own,
		zero_inherit_prof_info, Desc),
	(
		MaybeToCliquePtr = yes(ToCliquePtr),
		HTML1 = call_site_dynamics_to_html(URLprefix, Deep, Fields, no,
			ThisCliquePtr, ToCliquePtr, PSPtr, Own, Desc),
		HTML = HTML0 ++ HTML1,
		GroupOwn = add_own_to_own(GroupOwn0, Own),
		GroupDesc = add_inherit_to_inherit(GroupDesc0, Desc)
	;
		MaybeToCliquePtr = no,
		HTML = HTML0,
		GroupOwn = GroupOwn0,
		GroupDesc = GroupDesc0
	),
	Tuple = { HTML, GroupOwn, GroupDesc }.

:- pred process_call_site_dynamics_group(list(call_site_dynamic_ptr)::in,
	deep::in, proc_static_ptr::in,
	maybe(clique_ptr)::in, maybe(clique_ptr)::out,
	own_prof_info::in, own_prof_info::out,
	inherit_prof_info::in, inherit_prof_info::out) is det.

process_call_site_dynamics_group([], _, _, MaybeToCliquePtr, MaybeToCliquePtr,
		Own, Own, Desc, Desc).
process_call_site_dynamics_group([CSDPtr | CSDPtrs], Deep, CalleePSPtr,
		MaybeToCliquePtr0, MaybeToCliquePtr, Own0, Own, Desc0, Desc) :-
	deep_lookup_call_site_dynamics(Deep, CSDPtr, CSD),
	PDPtr = CSD ^ csd_callee,
	deep_lookup_proc_dynamics(Deep, PDPtr, PD),
	PSPtr = PD ^ pd_proc_static,
	require(unify(CalleePSPtr, PSPtr),
		"process_call_site_dynamics_group: callee mismatch"),
	deep_lookup_clique_index(Deep, PDPtr, ToCliquePtr),
	(
		MaybeToCliquePtr0 = no,
		MaybeToCliquePtr1 = yes(ToCliquePtr)
	;
		MaybeToCliquePtr0 = yes(PrevToCliquePtr),
		MaybeToCliquePtr1 = MaybeToCliquePtr0,
		require(unify(PrevToCliquePtr, ToCliquePtr),
			"process_call_site_dynamics_group: clique mismatch")
	),
	deep_lookup_csd_own(Deep, CSDPtr, CSDOwn),
	deep_lookup_csd_desc(Deep, CSDPtr, CSDDesc),
	Own1 = add_own_to_own(Own0, CSDOwn),
	Desc1 = add_inherit_to_inherit(Desc0, CSDDesc),
	process_call_site_dynamics_group(CSDPtrs, Deep, CalleePSPtr,
		MaybeToCliquePtr1, MaybeToCliquePtr, Own1, Own, Desc1, Desc).

:- func call_site_dynamics_to_html(string, deep, fields,
	maybe(pair(string, int)), clique_ptr, clique_ptr,
	proc_static_ptr, own_prof_info, inherit_prof_info) = string.

call_site_dynamics_to_html(URLprefix, Deep, Fields, MaybeFileNameLineNumber,
		ThisCliquePtr, ToCliquePtr, PSPtr, Own, Desc)
		= HTML :-
	deep_lookup_proc_statics(Deep, PSPtr, PS),
	CalleeName = PS ^ ps_refined_id,
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
	( MaybeFileNameLineNumber = yes(FileName - LineNumber) ->
		SourceField =
			format("<TD>%s:%d</TD>\n",
				[s(FileName), i(LineNumber)])
	;
		SourceField = "<TD> </TD>\n"
	),
	HTML =
		"<TR>\n" ++
		SourceField ++
		format("<TD>%s</TD>\n", [s(ProcName)]) ++
		own_and_desc_to_html(Own, Desc, Deep, Fields) ++
		"</TR>\n".

:- func maybe_call_site_dynamic_to_html(string, deep, fields,
	call_site_line_number, clique_ptr, call_site_dynamic_ptr) = string.

maybe_call_site_dynamic_to_html(URLprefix, Deep, Fields,
		PrintCallSiteLineNmber, ThisCliquePtr, CSDPtr) = HTML :-
	( valid_call_site_dynamic_ptr(Deep, CSDPtr) ->
		HTML = call_site_dynamic_to_html(URLprefix, Deep, Fields,
			PrintCallSiteLineNmber, yes(ThisCliquePtr), CSDPtr)
	;
		HTML = ""
	).

:- func call_site_dynamic_to_html(string, deep, fields, call_site_line_number,
	maybe(clique_ptr), call_site_dynamic_ptr) = string.

call_site_dynamic_to_html(URLprefix, Deep, Fields, PrintCallSiteLineNmber,
		MaybeThisCliquePtr, CSDPtr) = HTML :-
	require(valid_call_site_dynamic_ptr(Deep, CSDPtr),
		"call_site_dynamic_to_html: invalid call_site_dynamic_ptr"),
	deep_lookup_call_site_dynamics(Deep, CSDPtr, CSD),
	CSD = call_site_dynamic(_FromPtr, ToProcPtr, CallSiteOwn),
	deep_lookup_csd_desc(Deep, CSDPtr, CallSiteDesc),
	deep_lookup_clique_index(Deep, ToProcPtr, ToCliquePtr),
	CalleeName = call_site_dynamic_label(Deep, CSDPtr),
	(
		MaybeThisCliquePtr = yes(ThisCliquePtr),
		ThisCliquePtr = ToCliquePtr
	->
		% We don't link recursive calls
		ProcName = CalleeName
	;
		ToCliquePtr = clique_ptr(ToCliqueNum),
		ProcName =
			format("<A HREF=""%s?clique+%s+%d"">%s</A>\n",
				[s(URLprefix), s(Fields),
				i(ToCliqueNum), s(CalleeName)])
	),
	( PrintCallSiteLineNmber = call_site_line_number ->
		deep_lookup_call_site_static_map(Deep, CSDPtr, CSSPtr),
		deep_lookup_call_site_statics(Deep, CSSPtr, CSS),
		CSS = call_site_static(PSPtr, _, _, LineNumber, _),
		deep_lookup_proc_statics(Deep, PSPtr, PS),
		SourceField =
			format("<TD>%s:%d</TD>\n",
				[s(PS ^ ps_filename), i(LineNumber)])
	;
		SourceField = "<TD> </TD>\n"
	),
	HTML =
		"<TR>\n" ++
		SourceField ++
		format("<TD>%s</TD>\n", [s(ProcName)]) ++
		own_and_desc_to_html(CallSiteOwn, CallSiteDesc,
			Deep, Fields) ++
		"</TR>\n".

%-----------------------------------------------------------------------------%

:- func proc_summary_to_html(string, deep, string, int) = string.

proc_summary_to_html(URLprefix, Deep, Fields, PSI) = HTML :-
	deep_lookup_proc_statics(Deep, proc_static_ptr(PSI), PS),
	CSSPtrsArray = PS ^ ps_sites,
	array__to_list(CSSPtrsArray, CSSPtrs),
	CallSiteSummaryList =
		list__map(call_site_summary_to_html(URLprefix, Deep, Fields),
			CSSPtrs),
	string__append_list(CallSiteSummaryList, CallSiteSummaries),
	HTML =
		proc_total_summary_to_html(URLprefix, Deep, Fields, PSI) ++
		CallSiteSummaries.

:- func proc_total_summary_to_html(string, deep, string, int) = string.

proc_total_summary_to_html(URLprefix, Deep, Fields, PSI) = HTML :-
	PSPtr = proc_static_ptr(PSI),
	deep_lookup_ps_own(Deep, PSPtr, Own),
	deep_lookup_ps_desc(Deep, PSPtr, Desc),
	HTML =
		"<TR>\n" ++
		format("<TD COLSPAN=2>%s</TD>\n",
			[s(proc_static_to_html_ref(URLprefix,
				Deep, Fields, proc_static_ptr(PSI)))]) ++
		own_and_desc_to_html(Own, Desc, Deep, Fields) ++
		"</TR>\n".

%-----------------------------------------------------------------------------%

:- func call_site_summary_to_html(string, deep, string, call_site_static_ptr)
	= string.

call_site_summary_to_html(URLprefix, Deep, Fields, CSSPtr) = HTML :-
	deep_lookup_css_own(Deep, CSSPtr, Own),
	deep_lookup_css_desc(Deep, CSSPtr, Desc),
	deep_lookup_call_site_statics(Deep, CSSPtr, CSS),
	CSS = call_site_static(PSPtr, _, Kind, LineNumber, _GoalPath),
	deep_lookup_proc_statics(Deep, PSPtr, PS),
	FileName = PS ^ ps_filename,
	deep_lookup_call_site_calls(Deep, CSSPtr, CallSiteCallMap),
	map__to_assoc_list(CallSiteCallMap, CallSiteCallList),
	( Kind = normal_call(CalleePSPtr, _) ->
		( CallSiteCallList = [] ->
			deep_lookup_proc_statics(Deep, CalleePSPtr, CalleePS)
		; CallSiteCallList = [CallSiteCall] ->
			CallSiteCall = CalleePSPtr2 - _CallSet,
			require(unify(CalleePSPtr, CalleePSPtr2),
				"call_site_summary_to_html: callee mismatch"),
			deep_lookup_proc_statics(Deep, CalleePSPtr, CalleePS)
		;
			error("normal call site calls more than one procedure")
		),
		MainLineRest =
			format("<TD>%s</TD>\n",
				[s(CalleePS ^ ps_refined_id)]) ++
			own_and_desc_to_html(Own, Desc, Deep, Fields),
		AdditionalLines = ""
	;
		CallSiteName0 = call_site_kind_and_callee_to_html(Kind),
		( CallSiteCallList = [] ->
			CallSiteName = CallSiteName0 ++
				" (no&nbps;calls&nbps;made)"
		;
			CallSiteName = CallSiteName0
		),
		MainLineRest =
			format("<TD>%s</TD>\n",
				[s(CallSiteName)]) ++
			own_and_desc_to_html(Own, Desc, Deep, Fields),
		CallSiteCallLines = list__map(
			call_site_summary_group_to_html(URLprefix,
				Deep, Fields),
			CallSiteCallList),
		string__append_list(CallSiteCallLines, AdditionalLines)
	),
	HTML =
		"<TR>\n" ++
		format("<TD>%s:%d</TD>\n", [s(FileName), i(LineNumber)]) ++
		MainLineRest ++
		"</TR>\n" ++
		AdditionalLines.

:- func call_site_kind_and_callee_to_html(call_site_kind_and_callee) = string.

call_site_kind_and_callee_to_html(normal_call(_, _)) = "normal_call".
call_site_kind_and_callee_to_html(special_call) =      "special_call".
call_site_kind_and_callee_to_html(higher_order_call) = "higher_order_call".
call_site_kind_and_callee_to_html(method_call) =       "method_call".
call_site_kind_and_callee_to_html(callback) =          "callback".

:- func call_site_summary_group_to_html(string, deep, string,
	pair(proc_static_ptr, list(call_site_dynamic_ptr))) = string.

call_site_summary_group_to_html(URLprefix, Deep, Fields, PSPtr - CSDPtrs)
		= HTML :-
	list__foldl2(accumulate_csd_prof_info(Deep), CSDPtrs,
		zero_own_prof_info, Own, zero_inherit_prof_info, Desc),
	HTML =
		"<TR>\n" ++
		format("<TD>%s</TD>\n",
			[s(proc_static_to_html_ref(URLprefix,
				Deep, Fields, PSPtr))]) ++
		own_and_desc_to_html(Own, Desc, Deep, Fields) ++
		"</TR>\n".

:- pred accumulate_csd_prof_info(deep::in, call_site_dynamic_ptr::in,
	own_prof_info::in, own_prof_info::out,
	inherit_prof_info::in, inherit_prof_info::out) is det.

accumulate_csd_prof_info(Deep, CSDPtr, Own0, Own, Desc0, Desc) :-
	deep_lookup_csd_own(Deep, CSDPtr, CSDOwn),
	deep_lookup_csd_desc(Deep, CSDPtr, CSDDesc),

	add_own_to_own(Own0, CSDOwn) = Own,
	add_inherit_to_inherit(Desc0, CSDDesc) = Desc.

%-----------------------------------------------------------------------------%

:- func call_site_dynamic_label(deep, call_site_dynamic_ptr) = string.

call_site_dynamic_label(Deep, CSDPtr) = Name :-
	(
		valid_call_site_dynamic_ptr(Deep, CSDPtr),
		deep_lookup_call_site_dynamics(Deep, CSDPtr, CSD),
		CSD = call_site_dynamic(_, PDPtr, _),
		valid_proc_dynamic_ptr(Deep, PDPtr),
		deep_lookup_proc_dynamics(Deep, PDPtr, PD),
		PD = proc_dynamic(PSPtr, _),
		valid_proc_static_ptr(Deep, PSPtr),
		deep_lookup_proc_statics(Deep, PSPtr, PS)
	->
		Name = PS ^ ps_refined_id
	;
		Name = "unknown procedure"
	).

:- func proc_static_to_html_ref(string, deep, string, proc_static_ptr) = string.

proc_static_to_html_ref(URLprefix, Deep, Fields, PSPtr) = HTML :-
	( valid_proc_static_ptr(Deep, PSPtr) ->
		deep_lookup_proc_statics(Deep, PSPtr, PS),
		PSPtr = proc_static_ptr(PSI),
		HTML =
			format("<A HREF=""%s?proc+%s+%d"">%s</A>\n",
				[s(URLprefix), s(Fields), i(PSI),
				s(PS ^ ps_refined_id)])
	;
		HTML =
			"mercury_runtime"
	).

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

%-----------------------------------------------------------------------------%

:- pred find_top_procs(sort_measurement::in, include_descendants::in,
	display_limit::in, deep::in, maybe_error(list(int))::out) is det.

find_top_procs(Sort, InclDesc, Limit, Deep, MaybeTopPSIs) :-
	find_top_sort_predicate(Sort, InclDesc, SortCompatible, RawSortPred),
	(
		SortCompatible = no,
		MaybeTopPSIs = error("bad sort specification")
	;
		SortCompatible = yes,
		ProcStatics = Deep ^ proc_statics,
		array__max(ProcStatics, MaxProcStatic),
		PSIs = int_list_from_to(1, MaxProcStatic),
		SortPred = (pred(PSI1::in, PSI2::in, ComparisonResult::out)
				is det :-
			call(RawSortPred, Deep, PSI1, PSI2, ComparisonResult)
		),
		list__sort(SortPred, PSIs, AscendingPSIs),
		list__reverse(AscendingPSIs, DescendingPSIs),
		(
			Limit = rank_range(First, Last),
			(
				list__drop(First - 1, DescendingPSIs,
					RemainingPSIs)
			->
				list__take_upto(Last - First + 1,
					RemainingPSIs, TopPSIs),
				MaybeTopPSIs = ok(TopPSIs)
			;
				MaybeTopPSIs = ok([])
			)
		;
			Limit = threshold(Threshold),
			find_threshold_predicate(Sort, InclDesc,
				ThresholdCompatible, RawThresholdPred),
			(
				ThresholdCompatible = no,
				MaybeTopPSIs =
					error("bad threshold specification")
			;
				ThresholdCompatible = yes,
				ThresholdPred = (pred(PSI::in) is semidet :-
					call(RawThresholdPred, Deep, Threshold,
						PSI)
				),
				list__takewhile(ThresholdPred, DescendingPSIs,
					TopPSIs, _),
				MaybeTopPSIs = ok(TopPSIs)
			)
		)
	).

:- func int_list_from_to(int, int) = list(int).

int_list_from_to(From, To) = List :-
	( From > To ->
		List = []
	;
		List = [From | int_list_from_to(From + 1, To)]
	).

:- pred find_top_sort_predicate(sort_measurement, include_descendants,
	bool, pred(deep, int, int, comparison_result)).
:- mode find_top_sort_predicate(in, in, out, out(pred(in, in, in, out) is det))
	is det.

find_top_sort_predicate(calls,  self,          yes, compare_ps_calls_self).
find_top_sort_predicate(calls,  self_and_desc, no,  compare_ps_calls_self).
find_top_sort_predicate(time,   self,          yes, compare_ps_time_self).
find_top_sort_predicate(time,   self_and_desc, yes, compare_ps_time_both).
find_top_sort_predicate(allocs, self,          yes, compare_ps_allocs_self).
find_top_sort_predicate(allocs, self_and_desc, yes, compare_ps_allocs_both).
find_top_sort_predicate(words,  self,          yes, compare_ps_words_self).
find_top_sort_predicate(words,  self_and_desc, yes, compare_ps_words_both).

:- pred find_threshold_predicate(sort_measurement, include_descendants,
	bool, pred(deep, float, int)).
:- mode find_threshold_predicate(in, in, out, out(pred(in, in, in) is semidet))
	is det.

find_threshold_predicate(calls,  self,          no,  threshold_ps_time_self).
find_threshold_predicate(calls,  self_and_desc, no,  threshold_ps_time_self).
find_threshold_predicate(time,   self,          yes, threshold_ps_time_self).
find_threshold_predicate(time,   self_and_desc, yes, threshold_ps_time_both).
find_threshold_predicate(allocs, self,          yes, threshold_ps_allocs_self).
find_threshold_predicate(allocs, self_and_desc, yes, threshold_ps_allocs_both).
find_threshold_predicate(words,  self,          yes, threshold_ps_words_self).
find_threshold_predicate(words,  self_and_desc, yes, threshold_ps_words_both).

:- pred compare_ps_calls_self(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_calls_self(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	OwnCalls1 = calls(Own1),
	OwnCalls2 = calls(Own2),
	compare(Result, OwnCalls1, OwnCalls2).

:- pred compare_ps_time_self(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_time_self(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	OwnQuanta1 = quanta(Own1),
	OwnQuanta2 = quanta(Own2),
	compare(Result, OwnQuanta1, OwnQuanta2).

:- pred compare_ps_time_both(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_time_both(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	PSDesc = Deep ^ ps_desc,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	array__lookup(PSDesc, PSI1, Desc1),
	array__lookup(PSDesc, PSI2, Desc2),
	OwnQuanta1 = quanta(Own1),
	OwnQuanta2 = quanta(Own2),
	DescQuanta1 = inherit_quanta(Desc1),
	DescQuanta2 = inherit_quanta(Desc2),
	TotalQuanta1 = OwnQuanta1 + DescQuanta1,
	TotalQuanta2 = OwnQuanta2 + DescQuanta2,
	compare(Result, TotalQuanta1, TotalQuanta2).

:- pred compare_ps_allocs_self(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_allocs_self(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	OwnAllocs1 = mallocs(Own1),
	OwnAllocs2 = mallocs(Own2),
	compare(Result, OwnAllocs1, OwnAllocs2).

:- pred compare_ps_allocs_both(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_allocs_both(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	PSDesc = Deep ^ ps_desc,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	array__lookup(PSDesc, PSI1, Desc1),
	array__lookup(PSDesc, PSI2, Desc2),
	OwnAllocs1 = mallocs(Own1),
	OwnAllocs2 = mallocs(Own2),
	DescAllocs1 = inherit_mallocs(Desc1),
	DescAllocs2 = inherit_mallocs(Desc2),
	TotalAllocs1 = OwnAllocs1 + DescAllocs1,
	TotalAllocs2 = OwnAllocs2 + DescAllocs2,
	compare(Result, TotalAllocs1, TotalAllocs2).

:- pred compare_ps_words_self(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_words_self(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	OwnWords1 = words(Own1),
	OwnWords2 = words(Own2),
	compare(Result, OwnWords1, OwnWords2).

:- pred compare_ps_words_both(deep::in, int::in, int::in,
	comparison_result::out) is det.

compare_ps_words_both(Deep, PSI1, PSI2, Result) :-
	PSOwn = Deep ^ ps_own,
	PSDesc = Deep ^ ps_desc,
	array__lookup(PSOwn, PSI1, Own1),
	array__lookup(PSOwn, PSI2, Own2),
	array__lookup(PSDesc, PSI1, Desc1),
	array__lookup(PSDesc, PSI2, Desc2),
	OwnWords1 = words(Own1),
	OwnWords2 = words(Own2),
	DescWords1 = inherit_words(Desc1),
	DescWords2 = inherit_words(Desc2),
	TotalWords1 = OwnWords1 + DescWords1,
	TotalWords2 = OwnWords2 + DescWords2,
	compare(Result, TotalWords1, TotalWords2).

:- pred threshold_ps_time_self(deep::in, float::in, int::in) is semidet.

threshold_ps_time_self(Deep, Threshold, PSI) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI, Own),
	RootOwn = root_own_info(Deep),
	RootDesc = root_desc_info(Deep),
	OwnQuanta = quanta(Own),
	RootOwnQuanta = quanta(RootOwn),
	RootDescQuanta = inherit_quanta(RootDesc),
	RootTotalQuanta = RootOwnQuanta + RootDescQuanta,
	100.0 * float(OwnQuanta) > Threshold * float(RootTotalQuanta).

:- pred threshold_ps_time_both(deep::in, float::in, int::in) is semidet.

threshold_ps_time_both(Deep, Threshold, PSI) :-
	PSOwn = Deep ^ ps_own,
	PSDesc = Deep ^ ps_desc,
	array__lookup(PSOwn, PSI, Own),
	array__lookup(PSDesc, PSI, Desc),
	RootOwn = root_own_info(Deep),
	RootDesc = root_desc_info(Deep),
	OwnQuanta = quanta(Own),
	RootOwnQuanta = quanta(RootOwn),
	DescQuanta = inherit_quanta(Desc),
	RootDescQuanta = inherit_quanta(RootDesc),
	TotalQuanta = OwnQuanta + DescQuanta,
	RootTotalQuanta = RootOwnQuanta + RootDescQuanta,
	100.0 * float(TotalQuanta) > Threshold * float(RootTotalQuanta).

:- pred threshold_ps_allocs_self(deep::in, float::in, int::in) is semidet.

threshold_ps_allocs_self(Deep, Threshold, PSI) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI, Own),
	RootOwn = root_own_info(Deep),
	RootDesc = root_desc_info(Deep),
	OwnAllocs = mallocs(Own),
	RootOwnAllocs = mallocs(RootOwn),
	RootDescAllocs = inherit_mallocs(RootDesc),
	RootTotalAllocs = RootOwnAllocs + RootDescAllocs,
	100.0 * float(OwnAllocs) > Threshold * float(RootTotalAllocs).

:- pred threshold_ps_allocs_both(deep::in, float::in, int::in) is semidet.

threshold_ps_allocs_both(Deep, Threshold, PSI) :-
	PSOwn = Deep ^ ps_own,
	PSDesc = Deep ^ ps_desc,
	array__lookup(PSOwn, PSI, Own),
	array__lookup(PSDesc, PSI, Desc),
	RootOwn = root_own_info(Deep),
	RootDesc = root_desc_info(Deep),
	OwnAllocs = mallocs(Own),
	RootOwnAllocs = mallocs(RootOwn),
	DescAllocs = inherit_mallocs(Desc),
	RootDescAllocs = inherit_mallocs(RootDesc),
	TotalAllocs = OwnAllocs + DescAllocs,
	RootTotalAllocs = RootOwnAllocs + RootDescAllocs,
	100.0 * float(TotalAllocs) > Threshold * float(RootTotalAllocs).

:- pred threshold_ps_words_self(deep::in, float::in, int::in) is semidet.

threshold_ps_words_self(Deep, Threshold, PSI) :-
	PSOwn = Deep ^ ps_own,
	array__lookup(PSOwn, PSI, Own),
	RootOwn = root_own_info(Deep),
	RootDesc = root_desc_info(Deep),
	OwnWords = words(Own),
	RootOwnWords = words(RootOwn),
	RootDescWords = inherit_words(RootDesc),
	RootTotalWords = RootOwnWords + RootDescWords,
	100.0 * float(OwnWords) > Threshold * float(RootTotalWords).

:- pred threshold_ps_words_both(deep::in, float::in, int::in) is semidet.

threshold_ps_words_both(Deep, Threshold, PSI) :-
	PSOwn = Deep ^ ps_own,
	PSDesc = Deep ^ ps_desc,
	array__lookup(PSOwn, PSI, Own),
	array__lookup(PSDesc, PSI, Desc),
	RootOwn = root_own_info(Deep),
	RootDesc = root_desc_info(Deep),
	OwnWords = words(Own),
	RootOwnWords = words(RootOwn),
	DescWords = inherit_words(Desc),
	RootDescWords = inherit_words(RootDesc),
	TotalWords = OwnWords + DescWords,
	RootTotalWords = RootOwnWords + RootDescWords,
	100.0 * float(TotalWords) > Threshold * float(RootTotalWords).

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
	deep_lookup_pd_own(Deep, Deep ^ root, RootOwn),
	deep_lookup_pd_desc(Deep, Deep ^ root, RootDesc),
	add_own_to_inherit(RootOwn, RootDesc) = RootTotal.

:- func root_desc_info(deep) = inherit_prof_info.

root_desc_info(Deep) = RootDesc :-
	deep_lookup_pd_desc(Deep, Deep ^ root, RootDesc).

:- func root_own_info(deep) = own_prof_info.

root_own_info(Deep) = RootOwn :-
	deep_lookup_pd_own(Deep, Deep ^ root, RootOwn).

%-----------------------------------------------------------------------------%

:- func add_default_fields(string) = string.

add_default_fields(Str0) = string__append_list([Str0, "+", default_fields]).

:- func fields_header(fields) = string.

fields_header(Fields) =
	"<TR>\n" ++
	"<TD>Source</TD>\n" ++
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
	Fixed = 2,	% Source, Procedure
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
