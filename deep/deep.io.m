%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module deep:io.

:- interface.

:- import_module io.

:- type deep_result(T)
	--->	ok(T)
	;	error(string)
	.

:- pred read_call_graph(string, deep_result(deep), io__state, io__state).
:- mode read_call_graph(in, out, di, uo) is det.

:- pred dump_graph(deep, io__state, io__state).
:- mode dump_graph(in, di, uo) is det.

%:- pred deep2dot(string, int, deep, io__state, io__state).
%:- mode deep2dot(in, in, in, di, uo) is det.

%:- pred node2html(string, deep, call_site_dynamic_ptr, call_site_dynamic,
%		io__state, io__state).
%:- mode node2html(in, in, in, in, di, uo) is det.

:- func cons_profile([int]) = own_prof_info.

:- func u(T) = T.
:- mode (u(in) = array_uo) is det.

:- implementation.

:- import_module hash.
:- import_module char, std_util.

:- type ptr_info --->
		ptr_info(
			ps	:: {hashtable(int), int},
			css	:: {hashtable(int), int},
			pd	:: {hashtable(int), int},
			csd	:: {hashtable(int), int}
		).

:- type ptr_kind
	--->	ps
	;	pd
	;	css
	;	csd
	.

read_call_graph(FileName, Res) -->
	io__see_binary(FileName, Res0),
	(
		{ Res0 = ok },
		{ Deep0 = deep(call_site_dynamic_ptr(-1),
			init(1, call_site_dynamic(
					proc_dynamic_ptr(-1),
					cons_profile([0,0,0,0,0,0])
				)),
			init(1, proc_dynamic(proc_static_ptr(-1), array([]))),
			init(1, call_site_static(normal, "")),
			init(1, proc_static("", array([]))),
			array([]),
			array([]),
			array([]),
			array([]),
			array([]),
			array([]),
			array([]),
			array([])
		) },
		{ PI0 = ptr_info(
				{ init(10007), 1 },
				{ init(10007), 1 },
				{ init(10007), 1 },
				{ init(10007), 1 }
			) },
		read_call_graph2(Deep0, Res1, PI0, PI),
		io__seen_binary,
		{ resize_arrays(Res1, PI, Res) }
	;
		{ Res0 = error(Err) },
		{ io__error_message(Err, Msg) },
		{ Res = error(Msg) }
	).

:- pred read_call_graph2(deep, deep_result(deep), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_call_graph2(in, out, in, out, di, uo) is det.

read_call_graph2(Deep0, Res, PtrInfo0, PtrInfo) -->
	read_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = call_site_static } ->
			read_call_site_static(Deep0, Res, PtrInfo0, PtrInfo)
		; { Byte = proc_static } ->
			read_proc_static(Deep0, Res, PtrInfo0, PtrInfo)
		; { Byte = call_site_dynamic } ->
			read_call_site_dynamic(Deep0, Res, PtrInfo0, PtrInfo)
		; { Byte = proc_dynamic } ->
			read_proc_dynamic(Deep0, Res, PtrInfo0, PtrInfo)
		; { Byte = root } ->
			read_root(Deep0, Res, PtrInfo0, PtrInfo)
		;
			{ format("unexpected token %d", [i(Byte)], Msg) },
			{ Res = error(Msg) },
			{ PtrInfo = PtrInfo0 }
		)
	;
		{ Res0 = eof },
		{ Res = ok(Deep0) },
		{ PtrInfo = PtrInfo0 }
	;
		{ Res0 = error(Err) },
		{ io__error_message(Err, Msg) },
		{ Res = error(Msg) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_root(deep, deep_result(deep), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_root(in, out, in, out, di, uo) is det.

read_root(Deep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading root.\n", []),
	read_ptr(csd, Res0, PtrInfo0, PtrInfo1),
	(
		{ Res0 = ok(Ptr) },
		{ Deep1 = Deep0^root := call_site_dynamic_ptr(Ptr) },
		read_call_graph2(Deep1, Res, PtrInfo1, PtrInfo)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo1 }
	).

:- pred read_call_site_static(deep, deep_result(deep), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_call_site_static(in, out, in, out, di, uo) is det.

read_call_site_static(Deep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading call_site_static.\n", []),
	read_sequence3(
		read_ptr(css),
		read_call_site_kind,
		read_string,
		(pred(Ptr::in, Kind::in, Str::in, Res0::out)
				is det :-
			CSS = call_site_static(Kind, Str),
			insert(Deep0^call_site_statics, Ptr, CSS, CSSs),
			Deep = Deep0^call_site_statics := CSSs,
			Res0 = ok(Deep)
		),
		Res1, PtrInfo0, PtrInfo1),
	(
		{ Res1 = ok(Deep1) },
		read_call_graph2(Deep1, Res, PtrInfo1, PtrInfo)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo1 }
	).


:- pred read_proc_static(deep, deep_result(deep), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_proc_static(in, out, in, out, di, uo) is det.

read_proc_static(Deep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading proc_static.\n", []),
	read_sequence3(
		read_ptr(ps),
		read_string,
		read_num,
		(pred(Ptr0::in, Id0::in, N0::in, Stuff0::out) is det :-
			Stuff0 = ok({Ptr0, Id0, N0})
		),
		Res1, PtrInfo0, PtrInfo1),
	(
		{ Res1 = ok({Ptr, Id, N}) },
		read_n_things(N, read_ptr(css), Res2, PtrInfo1, PtrInfo2),
		(
			{ Res2 = ok(Ptrs0) },
			{ map((pred(Ptr1::in, Ptr2::out) is det :-
				Ptr2 = call_site_static_ptr(Ptr1)
			), Ptrs0, Ptrs) },
			{ ProcStatic = proc_static(Id, array(Ptrs)) },
			{ insert(Deep0^proc_statics, Ptr, ProcStatic, PSs) },
			{ Deep1 = Deep0^proc_statics := PSs },
			read_call_graph2(Deep1, Res, PtrInfo2, PtrInfo)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo2 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo1 }
	).

:- pred read_proc_dynamic(deep, deep_result(deep), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_proc_dynamic(in, out, in, out, di, uo) is det.

read_proc_dynamic(Deep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading proc_dynamic.\n", []),
	read_sequence3(
		read_ptr(pd),
		read_ptr(ps),
		read_num,
		(pred(Ptr0::in, Ptr1::in, N0::in, Stuff0::out) is det :-
			Stuff0 = ok({Ptr0, Ptr1, N0})
		),
		Res1, PtrInfo0, PtrInfo1),
	(
		{ Res1 = ok({Ptr, SPtr, N}) },
		read_n_things(N, read_call_site_ref, Res2, PtrInfo1, PtrInfo2),
		(
			{ Res2 = ok(Refs) },
			{ PSPtr = proc_static_ptr(SPtr) },
			{ PD = proc_dynamic(PSPtr, array(Refs)) },
			{ insert(Deep0^proc_dynamics, Ptr, PD, PDs) },
			{ Deep1 = Deep0^proc_dynamics := PDs },
			read_call_graph2(Deep1, Res, PtrInfo2, PtrInfo)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo2 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo1 }
	).

:- pred read_call_site_dynamic(deep, deep_result(deep),
		ptr_info, ptr_info, io__state, io__state).
:- mode read_call_site_dynamic(in, out, in, out, di, uo) is det.

read_call_site_dynamic(Deep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading call_site_dynamic.\n", []),
	read_ptr(csd, Res1, PtrInfo0, PtrInfo1),
	(
		{ Res1 = ok(Ptr1) },
		read_ptr(pd, Res2, PtrInfo1, PtrInfo2),
		(
			{ Res2 = ok(Ptr2) },
			read_profile(Res3),
			(
				{ Res3 = ok(Profile) },
				{ PDPtr = proc_dynamic_ptr(Ptr2) },
				{ CD = call_site_dynamic(PDPtr, Profile) },
				{ insert(Deep0^call_site_dynamics, Ptr1,
						CD, CDs) },
				{ Deep1 = Deep0^call_site_dynamics := CDs },
				read_call_graph2(Deep1, Res, PtrInfo2, PtrInfo)
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) },
				{ PtrInfo = PtrInfo2 }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo2 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo1 }
	).

:- pred read_profile(deep_result(own_prof_info), io__state, io__state).
:- mode read_profile(out, di, uo) is det.

read_profile(Res) -->
	read_num(Res0),
	(
		{ Res0 = ok(Mask) },
		( { Mask /\ 0x0001 \= 0 } ->
			{ GetCalls = yes }
		;
			{ GetCalls = no }
		),
		( { Mask /\ 0x0002 \= 0 } ->
			{ GetExits = yes }
		;
			{ GetExits = no }
		),
		( { Mask /\ 0x0004 \= 0 } ->
			{ GetFails = yes }
		;
			{ GetFails = no }
		),
		( { Mask /\ 0x0008 \= 0 } ->
			{ GetRedos = yes }
		;
			{ GetRedos = no }
		),
		( { Mask /\ 0x0010 \= 0 } ->
			{ GetQuant = yes }
		;
			{ GetQuant = no }
		),
		( { Mask /\ 0x0020 \= 0 } ->
			{ GetMems = yes }
		;
			{ GetMems = no }
		),
		read_profile2([GetCalls, GetExits,
			GetFails, GetRedos, GetQuant, GetMems], [], Res1),
		(
			{ Res1 = ok(Values) },
			{ Res = ok(cons_profile(Values)) }
		;
			{ Res1 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_profile2([bool], [int], deep_result([int]), io__state, io__state).
:- mode read_profile2(in, in, out, di, uo) is det.

read_profile2([], Values, ok(reverse(Values))) --> [].
read_profile2([B|Bs], Values0, Res) -->
	(
		{ B = yes },
		read_num(Res0),
		(
			{ Res0 = ok(Val) },
			read_profile2(Bs, [Val|Values0], Res)
		;
			{ Res0 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ B = no },
		read_profile2(Bs, [0|Values0], Res)
	).

cons_profile(Values) = PI :-
	( Values = [Calls, Exits, Fails, Redos, Quanta, Mem] ->
		(
			Calls = Exits,
			Fails = 0,
			Redos = 0,
			Quanta = 0,
			Mem = 0
		->
			PI = zdet(Calls)
		;
			Calls = Exits,
			Fails = 0,
			Redos = 0,
			Mem = 0
		->
			PI = det(Calls, Quanta)
		;
			PI = all(Calls, Exits, Fails, Redos, Quanta, Mem)
		)
	;
		error("cons_profile: missing values")
	).

:- pred read_call_site_ref(deep_result(call_site_ref), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_call_site_ref(out, in, out, di, uo) is det.

read_call_site_ref(Res, PtrInfo0, PtrInfo) -->
	%format("reading call_site_ref.\n", []),
	read_call_site_kind(Res1),
	(
		{ Res1 = ok(Kind) },
		( { Kind = normal } ->
			read_ptr(csd, Res2, PtrInfo0, PtrInfo),
			(
				{ Res2 = ok(Ptr) },
				{ CDPtr = call_site_dynamic_ptr(Ptr) },
				{ Res = ok(normal(CDPtr)) }
			;
				{ Res2 = error(Err) },
				{ Res = error(Err) }
			)
		;
			read_things(read_ptr(csd), Res2, PtrInfo0, PtrInfo),
			(
				{ Res2 = ok(Ptrs0) },
				{ map((pred(PtrX::in, PtrY::out) is det :-
					PtrY = call_site_dynamic_ptr(PtrX)
				), Ptrs0, Ptrs) },
				{ Res = ok(multi(array(Ptrs))) }
			;
				{ Res2 = error(Err) },
				{ Res = error(Err) }
			)
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_call_site_kind(deep_result(call_site_kind), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_call_site_kind(out, in, out, di, uo) is det.

read_call_site_kind(Res, PtrInfo, PtrInfo) -->
	read_call_site_kind(Res).

:- pred read_call_site_kind(deep_result(call_site_kind),
		io__state, io__state).
:- mode read_call_site_kind(out, di, uo) is det.

read_call_site_kind(Res) -->
	read_deep_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = normal } ->
			{ Res = ok(normal) }
		; { Byte = higher_order } ->
			{ Res = ok(higher_order) }
		; { Byte = typeclass_method } ->
			{ Res = ok(typeclass_method) }
		; { Byte = callback } ->
			{ Res = ok(callback) }
		;
			{ format("unexpected call_site_kind %d",
				[i(Byte)], Msg) },
			{ Res = error(Msg) }
		)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_n_things(int, pred(deep_result(T), ptr_info, ptr_info,
		io__state, io__state),
		deep_result(list(T)), ptr_info, ptr_info, io__state, io__state).
:- mode read_n_things(in, pred(out, in, out, di, uo) is det, out, in, out,
		di, uo) is det.

read_n_things(N, ThingReader, Res, PtrInfo0, PtrInfo) -->
	read_n_things(N, ThingReader, [], Res0, PtrInfo0, PtrInfo),
	(
		{ Res0 = ok(Things0) },
		{ reverse(Things0, Things) },
		{ Res = ok(Things) }
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_n_things(int, pred(deep_result(T), ptr_info, ptr_info,
		io__state, io__state),
		list(T), deep_result(list(T)), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_n_things(in, pred(out, in, out, di, uo) is det, in, out, in, out,
		di, uo) is det.

read_n_things(N, ThingReader, Things0, Res, PtrInfo0, PtrInfo) -->
	( { N =< 0 } ->
		{ Res = ok(Things0) },
		{ PtrInfo = PtrInfo0 }
	;
		call(ThingReader, Res1, PtrInfo0, PtrInfo1),
		(
			{ Res1 = ok(Thing) },
			read_n_things(N - 1, ThingReader, [Thing|Things0], Res,
				PtrInfo1, PtrInfo)
		;
			{ Res1 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo1 }
		)
	).

:- pred read_things(pred(deep_result(T), ptr_info, ptr_info,
		io__state, io__state),
		deep_result(list(T)), ptr_info, ptr_info, io__state, io__state).
:- mode read_things(pred(out, in, out, di, uo) is det, out, in,
		out, di, uo) is det.

read_things(ThingReader, Res, PtrInfo0, PtrInfo) -->
	read_things(ThingReader, [], Res0, PtrInfo0, PtrInfo),
	(
		{ Res0 = ok(Things0) },
		{ reverse(Things0, Things) },
		{ Res = ok(Things) }
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_things(pred(deep_result(T), ptr_info, ptr_info,
		io__state, io__state),
		list(T), deep_result(list(T)), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_things(pred(out, in, out, di, uo) is det, in, out, in, out,
		di, uo) is det.

read_things(ThingReader, Things0, Res, PtrInfo0, PtrInfo) -->
	read_deep_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = 0 } ->
			{ Res = ok(Things0) },
			{ PtrInfo = PtrInfo0 }
		;
			putback_byte(Byte),
			call(ThingReader, Res1, PtrInfo0, PtrInfo1),
			(
				{ Res1 = ok(Thing) },
				read_things(ThingReader, [Thing|Things0], Res,
					PtrInfo1, PtrInfo)
			;
				{ Res1 = error(Err) },
				{ Res = error(Err) },
				{ PtrInfo = PtrInfo1 }
			)
		)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_sequence3(
		pred(deep_result(T1), ptr_info, ptr_info, io__state, io__state),
		pred(deep_result(T2), ptr_info, ptr_info, io__state, io__state),
		pred(deep_result(T3), ptr_info, ptr_info, io__state, io__state),
		pred(T1, T2, T3, deep_result(T4)),
		deep_result(T4), ptr_info, ptr_info, io__state, io__state).
:- mode read_sequence3(
		pred(out, in, out, di, uo) is det,
		pred(out, in, out, di, uo) is det,
		pred(out, in, out, di, uo) is det,
		pred(in, in, in, out) is det,
		out, in, out, di, uo) is det.

read_sequence3(P1, P2, P3, Combine, Res, PtrInfo0, PtrInfo) -->
	call(P1, Res1, PtrInfo0, PtrInfo1),
	(
		{ Res1 = ok(T1) },
		call(P2, Res2, PtrInfo1, PtrInfo2),
		(
			{ Res2 = ok(T2) },
			call(P3, Res3, PtrInfo2, PtrInfo),
			(
				{ Res3 = ok(T3) },
				{ call(Combine, T1, T2, T3, Res) }
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo2 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo1 }
	).

:- pred read_string(deep_result(string), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_string(out, in, out, di, uo) is det.

read_string(Res, PtrInfo, PtrInfo) -->
	read_string(Res).

:- pred read_string(deep_result(string), io__state, io__state).
:- mode read_string(out, di, uo) is det.

read_string(Res) -->
	read_num(Res0),
	(
		{ Res0 = ok(Length) },
		read_n_bytes(Length, Res1),
		(
			{ Res1 = ok(Bytes) },
			(
				{ map((pred(I::in, C::out) is semidet :-
					char__to_int(C, I)
				), Bytes, Chars) }
			->
				{ string__from_char_list(Chars, Str) },
				{ Res = ok(Str) }
			;
				{ Res = error("string contained bad char") }
			)
		;
			{ Res1 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_ptr(ptr_kind, deep_result(int), ptr_info, ptr_info,
		io__state, io__state).
:- mode read_ptr(in, out, in, out, di, uo) is det.

read_ptr(Kind, Res, PtrInfo0, PtrInfo) -->
	read_num(Res0),
	%write(Res0), nl,
	(
		{ Res0 = ok(Ptr0) },
		{ map_pointer(Kind, Ptr0, Ptr, PtrInfo0, PtrInfo) },
		{ Res = ok(Ptr) }
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred map_pointer(ptr_kind, int, int, ptr_info, ptr_info).
:- mode map_pointer(in, in, out, in, out) is det.

map_pointer(Kind, Ptr0, Ptr, PI0, PI) :-
	( Ptr0 = 0 ->
		Ptr = Ptr0,
		PI = PI0
	;
		( Kind = ps,	Ptrs0 = PI0^ps
		; Kind = css,	Ptrs0 = PI0^css
		; Kind = pd,	Ptrs0 = PI0^pd
		; Kind = csd,	Ptrs0 = PI0^csd
		),
		Ptrs0 = { PMap0a, Next0 },
		PMap0 = u(PMap0a),
		( search(PMap0, Ptr0) = Ptr1 ->
			Ptr = Ptr1,
			PI = PI0
		;
			Ptr = Next0,
			Next = Next0 + 1,
			PMap = insert(PMap0, Ptr0, Ptr),
			Ptrs = { PMap, Next },
			( Kind = ps,	PI = PI0^ps := Ptrs
			; Kind = css,	PI = PI0^css := Ptrs
			; Kind = pd,	PI = PI0^pd := Ptrs
			; Kind = csd,	PI = PI0^csd := Ptrs
			)
		)
	).

:- pred read_num(deep_result(int), ptr_info, ptr_info, io__state, io__state).
:- mode read_num(out, in, out, di, uo) is det.

read_num(Res, PtrInfo, PtrInfo) -->
	read_num(Res).

:- pred read_num(deep_result(int), io__state, io__state).
:- mode read_num(out, di, uo) is det.

read_num(Res) -->
	read_num1(0, Res).

:- pred read_num1(int, deep_result(int), io__state, io__state).
:- mode read_num1(in, out, di, uo) is det.

read_num1(Num0, Res) -->
	read_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		{ Num1 = (Num0 << 7) \/ (Byte /\ 0x7F) },
		( { Byte /\ 0x80 \= 0 } ->
			read_num1(Num1, Res)
		;
			{ Res = ok(Num1) }
		)
	;
		{ Res0 = eof },
		{ Res = error("unexpected end of file") }
	;
		{ Res0 = error(Err) },
		{ io__error_message(Err, Msg) },
		{ Res = error(Msg) }
	).

:- pred read_n_bytes(int, deep_result(list(int)), io__state, io__state).
:- mode read_n_bytes(in, out, di, uo) is det.

read_n_bytes(N, Res) -->
	read_n_bytes(N, [], Res0),
	(
		{ Res0 = ok(Bytes0) },
		{ reverse(Bytes0, Bytes) },
		{ Res = ok(Bytes) }
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_n_bytes(int, [int], deep_result(list(int)),
		io__state, io__state).
:- mode read_n_bytes(in, in, out, di, uo) is det.

read_n_bytes(N, Bytes0, Res) -->
	( { N =< 0 } ->
		{ Res = ok(Bytes0) }
	;
		read_deep_byte(Res0),
		(
			{ Res0 = ok(Byte) },
			read_n_bytes(N - 1, [Byte|Bytes0], Res)
		;
			{ Res0 = error(Err) },
			{ Res = error(Err) }
		)
	).

:- pred read_deep_byte(deep_result(int), io__state, io__state).
:- mode read_deep_byte(out, di, uo) is det.

read_deep_byte(Res) -->
	read_byte(Res0),
	%write(Res0), nl,
	(
		{ Res0 = ok(Byte) },
		{ Res = ok(Byte) }
	;
		{ Res0 = eof },
		{ Res = error("unexpected end of file") }
	;
		{ Res0 = error(Err) },
		{ io__error_message(Err, Msg) },
		{ Res = error(Msg) }
	).

%------------------------------------------------------------------------------%

:- pred insert(array(T), int, T, array(T)).
:- mode insert(in, in, in, out) is det.

insert(A0, Ind, Thing, A) :-
	array__max(A0, Max),
	( Ind > Max ->
		lookup(A0, 0, X),
		resize(u(A0), 2 * (Max + 1), X, A1),
		insert(A1, Ind, Thing, A)
	;
		set(u(A0), Ind, Thing, A)
	).

:- pragma c_code(u(A::in) = (B::array_uo),
		[will_not_call_mercury, thread_safe], "B = A;").

%------------------------------------------------------------------------------%

:- pragma c_header_code("
#include ""mercury_deep_profiling.h""
").

:- func root = int.
:- pragma c_code(root = (X::out),
		[will_not_call_mercury, thread_safe], "X = root;").

:- func call_site_static = int.
:- pragma c_code(call_site_static = (X::out),
		[will_not_call_mercury, thread_safe], "X = callsite_static;").

:- func call_site_dynamic = int.
:- pragma c_code(call_site_dynamic = (X::out),
		[will_not_call_mercury, thread_safe], "X = callsite_dynamic;").

:- func proc_static = int.
:- pragma c_code(proc_static = (X::out),
		[will_not_call_mercury, thread_safe], "X = proc_static;").

:- func proc_dynamic = int.
:- pragma c_code(proc_dynamic = (X::out),
		[will_not_call_mercury, thread_safe], "X = proc_dynamic;").

:- func normal = int.
:- pragma c_code(normal = (X::out),
		[will_not_call_mercury, thread_safe], "X = normal;").

:- func higher_order = int.
:- pragma c_code(higher_order = (X::out),
		[will_not_call_mercury, thread_safe], "X = higher_order;").

:- func typeclass_method = int.
:- pragma c_code(typeclass_method = (X::out),
		[will_not_call_mercury, thread_safe], "X = typeclass_method;").

:- func callback = int.
:- pragma c_code(callback = (X::out),
		[will_not_call_mercury, thread_safe], "X = callback;").

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

/*
deep2dot(FileName, Depth, Deep) -->
	io__tell(FileName, Res),
	(
		{ Res = ok },
		format("digraph L0 {\n", []),
		format("size =""8,11"";\n", []),
		{ Deep^root = call_site_dynamic_ptr(Root) },
		{ lookup(Deep^clique_index, Root, RootClique) },
		deep2dot2(Deep, Depth, RootClique),
		format("};\n", [])
	;
		{ Res = error(Err) },
		{ io__error_message(Err, Msg) },
		io__stderr_stream(StdErr),
		format(StdErr, "%s\n", [s(Msg)])
	).

:- pred deep2dot2(deep, int, clique, io__state, io__state).
:- mode deep2dot2(in, in, in, di, uo) is det.

deep2dot2(Deep, Depth, Clique) -->
	( { Depth > 0 } ->
		{ Clique = clique(CliqueN) },
		{ lookup(Deep^clique_tree, CliqueN, Children0) },
		{ lookup(Deep^clique_members, CliqueN, Members) },
		(
			{ Members = [call_site_dynamic_ptr(CSDI)|_] },
			{ CSDI > 0 },
			{ lookup(Deep^call_site_dynamics, CSDI, CSD) },
			{ CSD = call_site_dynamic(PDPtr, _) },
			{ PDPtr = proc_dynamic_ptr(PDI), PDI > 0 },
			{ lookup(Deep^proc_dynamics, PDI, PD) },
			{ PD = proc_dynamic(PSPtr, _) },
			{ PSPtr = proc_static_ptr(PSI), PSI > 0 },
			{ lookup(Deep^proc_statics, PSI, PS) },
			{ PS = proc_static(Id, _) }
		->
			{ Clique = clique(Z) },
			format("n%x [label=""%s""];\n", [i(Z), s(Id)])
		;
			[]
		),
		foldl((pred(CCliqueN::in, di, uo) is det -->
			{ Clique = clique(X) },
			{ CCliqueN = clique(Y) },
			format("n%x -> { n%x };\n", [i(X), i(Y)])
		), Children0),
		{ list__delete_all(Children0, Clique, Children) },
		foldl(deep2dot2(Deep, Depth - 1), Children)
	;
		[]
	).

:- pred children(array(call_site_ref), (call_site_dynamic_ptr -> clique), [clique]).
:- mode children(in, in, out) is det.

children(Refs, Index, Kids) :-
	solutions((pred(Kid::out) is nondet :-
		array__to_list(Refs, RefList),
		member(Ref, RefList),
		(
			Ref = normal(CSDPtr1),
			CSDPtr1 \= call_site_dynamic_ptr(0),
			lookup(Index, CSDPtr1, Kid)
		;
			Ref = multi(PtrArray),
			array__to_list(PtrArray, PtrList),
			member(CSDPtr1, PtrList),
			CSDPtr1 \= call_site_dynamic_ptr(0),
			lookup(Index, CSDPtr1, Kid)
		)
	), Kids).
*/

dump_graph(Deep) -->
	format("digraph L0 {\n", []),
	format("size=""8,11"";\n", []),
	foldl((pred(CSDI::in, CSD::in, di, uo) is det -->
		{ CSDI = From },
		{ CSD = call_site_dynamic(proc_dynamic_ptr(To), _) },
		format("n%x -> { n%x };\n", [i(From), i(To)])
	), Deep^call_site_dynamics),
	foldl((pred(PDI::in, PD::in, di, uo) is det -->
		{ PDI = From },
		{ PD = proc_dynamic(PSPtr, Refs) },
		{ PSPtr = proc_static_ptr(PSI) },
		{ lookup(Deep^proc_statics, PSI, PS) },
		{ PS = proc_static(Id, _) },
		format("n%x [label=""%s""];\n", [i(From), s(Id)]),
		{ array__to_list(Refs, RefList) },
		foldl((pred(Ref::in, di, uo) is det -->
			(
				{ Ref = normal(call_site_dynamic_ptr(To)) },
				format("n%x -> { n%x };\n", [i(From), i(To)])
			;
				{ Ref = multi(CSDPtrs) },
				{ array__to_list(CSDPtrs, CSDPtrList) },
				foldl((pred(CSDPtr::in, di, uo) is det -->
					{ CSDPtr = call_site_dynamic_ptr(To) },
					format("n%x -> { n%x };\n",
						[i(From), i(To)])
				), CSDPtrList)
			)
		), RefList)
	), Deep^proc_dynamics),
	format("};\n", []).

/*
node2html(URL, Deep, CSDPtr, _CSD) -->
	format("<HTML>\n", []),
	format("<TITLE>The University of Melbourne Mercury Deep Profiler.</TITLE>\n", []),
	{ ThisName = label(CSDPtr, Deep) },
	format("<H2>%s</H2>\n", [s(ThisName)]),
	format("<TABLE>\n", []),
	format("<TR>\n", []),
	format("<TD>Kind</TD>\n", []),
	format("<TD>Procedure                     </TD>\n", []),
	format("<TD>Calls</TD>\n", []),
	format("<TD>Exits</TD>\n", []),
	format("<TD>Fails</TD>\n", []),
	format("<TD>Redos</TD>\n", []),
	format("<TD>Quanta</TD>\n", []),
	format("<TD>Memory</TD>\n", []),
	format("</TR>\n", []),

	{ array__to_list(refs(CSDPtr, Deep), RefList0) },
	{ list__delete_all(RefList0,
		normal(call_site_dynamic_ptr(0)), RefList) },
	foldl((pred(Ref::in, di, uo) is det -->
		(
			{ Ref = normal(ToPtr) },
			{ label(ToPtr, Deep) = CalleeName },
			{ ToPtr = call_site_dynamic_ptr(To) },
			{ lookup(Deep^call_site_dynamics, To, CSD) },
			{ CSD = call_site_dynamic(_, PI) },
			{ Calls = calls(PI) }, { Exits = exits(PI) },
			{ Fails = fails(PI) }, { Redos = redos(PI) },
			{ Quanta = quanta(PI) }, { Mems = memory(PI) },
			format("<TR>\n", []),
			format("<TD> </TD>\n", []),
			format("<TD><A HREF=""%s?%d"">%s</A></TD>\n",
				[s(URL), i(To), s(CalleeName)]),
			format("<TD>%d</TD>\n", [i(Calls)]),
			format("<TD>%d</TD>\n", [i(Exits)]),
			format("<TD>%d</TD>\n", [i(Fails)]),
			format("<TD>%d</TD>\n", [i(Redos)]),
			format("<TD>%d</TD>\n", [i(Quanta)]),
			format("<TD>%d</TD>\n", [i(Mems)]),
			format("</TR>\n", [])
		;
			{ Ref = multi(CSDPtrs) },
			{ array__to_list(CSDPtrs, CSDPtrList) },
			foldl((pred(ToPtr::in, di, uo) is det -->
				{ label(ToPtr, Deep) = CalleeName },
				{ ToPtr = call_site_dynamic_ptr(To) },
				{ lookup(Deep^call_site_dynamics, To, CSD) },
				{ CSD = call_site_dynamic(_, PI) },
				{ Calls = calls(PI) }, { Exits = exits(PI) },
				{ Fails = fails(PI) }, { Redos = redos(PI) },
				{ Quanta = quanta(PI) }, { Mems = memory(PI) },
				format("<TR>\n", []),
				format("<TD>^</TD>\n", []),
				format("<TD><A HREF=""%s?%d"">%s</A></TD>\n",
					[s(URL), i(To), s(CalleeName)]),
				format("<TD>%d</TD>\n", [i(Calls)]),
				format("<TD>%d</TD>\n", [i(Exits)]),
				format("<TD>%d</TD>\n", [i(Fails)]),
				format("<TD>%d</TD>\n", [i(Redos)]),
				format("<TD>%d</TD>\n", [i(Quanta)]),
				format("<TD>%d</TD>\n", [i(Mems)]),
				format("</TR>\n", [])
			), CSDPtrList)
		)
	), RefList),
	format("</TABLE>\n", []),
	format("</HTML>\n", []).

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
*/

:- pred resize_arrays(deep_result(deep), ptr_info, deep_result(deep)).
:- mode resize_arrays(in, in, out) is det.

resize_arrays(error(Err), _, error(Err)).
resize_arrays(ok(Deep0), PI, ok(Deep)) :-
	PI^csd = CSDInfo,
	CSDInfo = { _, CSDSize },
	CSDs0 = Deep0^call_site_dynamics,
	lookup(CSDs0, 0, CSDx),
	resize(u(CSDs0), CSDSize, CSDx, CSDs),
	Deep1 = Deep0^call_site_dynamics := CSDs,

	PI^pd = PDInfo,
	PDInfo = { _, PDSize },
	PDs0 = Deep1^proc_dynamics,
	lookup(PDs0, 0, PDx),
	resize(u(PDs0), PDSize, PDx, PDs),
	Deep2 = Deep1^proc_dynamics := PDs,

	PI^css = CSSInfo,
	CSSInfo = { _, CSSSize },
	CSSs0 = Deep2^call_site_statics,
	lookup(CSSs0, 0, CSSx),
	resize(u(CSSs0), CSSSize, CSSx, CSSs),
	Deep3 = Deep2^call_site_statics := CSSs,

	PI^ps = PSInfo,
	PSInfo = { _, PSSize },
	PSs0 = Deep3^proc_statics,
	lookup(PSs0, 0, PSx),
	resize(u(PSs0), PSSize, PSx, PSs),
	Deep = Deep3^proc_statics := PSs.

