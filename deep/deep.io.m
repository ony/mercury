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
	;	error(string).

:- pred read_call_graph(string::in, deep_result(initial_deep)::out,
	io__state::di, io__state::uo) is det.

:- pred dump_graph(deep::in, io__state::di, io__state::uo) is det.

%:- pred deep2dot(string, int, deep, io__state, io__state).
%:- mode deep2dot(in, in, in, di, uo) is det.

%:- pred node2html(string, deep, call_site_dynamic_ptr, call_site_dynamic,
%		io__state, io__state).
%:- mode node2html(in, in, in, in, di, uo) is det.

:- func compress_profile(int, int, int, int, int, int, int) = own_prof_info.
:- func compress_profile(own_prof_info) = own_prof_info.

:- func u(T) = T.
:- mode (u(in) = array_uo) is det.

:- implementation.

:- import_module char, std_util.

:- type ptr_info --->
		ptr_info(
			ps	:: int,
			css	:: int,
			pd	:: int,
			csd	:: int
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
		{ InitDeep = initial_deep(
			call_site_dynamic_ptr(-1),
			init(1, call_site_dynamic(
					proc_dynamic_ptr(-1),
					% should be zero_own_profile
					zdet(0, 0, 0)
				)),
			init(1, proc_dynamic(proc_static_ptr(-1), array([]))),
			init(1, call_site_static(normal_call, -1, "")),
			init(1, proc_static(dummy_proc_id, "", array([])))
		) },
		{ PI0 = ptr_info(0, 0, 0, 0) },
		read_call_graph2(InitDeep, Res1, PI0, PI),
		io__seen_binary,
		{ resize_arrays(Res1, PI, Res) }
	;
		{ Res0 = error(Err) },
		{ io__error_message(Err, Msg) },
		{ Res = error(Msg) }
	).

:- pred read_call_graph2(initial_deep::in, deep_result(initial_deep)::out,
	ptr_info::in, ptr_info::out, io__state::di, io__state::uo) is det.

read_call_graph2(InitDeep0, Res, PtrInfo0, PtrInfo) -->
	read_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = token_call_site_static } ->
			read_call_site_static(InitDeep0, Res,
				PtrInfo0, PtrInfo)
		; { Byte = token_proc_static } ->
			read_proc_static(InitDeep0, Res,
				PtrInfo0, PtrInfo)
		; { Byte = token_call_site_dynamic } ->
			read_call_site_dynamic(InitDeep0, Res,
				PtrInfo0, PtrInfo)
		; { Byte = token_proc_dynamic } ->
			read_proc_dynamic(InitDeep0, Res,
				PtrInfo0, PtrInfo)
		; { Byte = token_root } ->
			read_root(InitDeep0, Res, PtrInfo0, PtrInfo)
		;
			{ format("unexpected token %d", [i(Byte)], Msg) },
			{ Res = error(Msg) },
			{ PtrInfo = PtrInfo0 }
		)
	;
		{ Res0 = eof },
		{ Res = ok(InitDeep0) },
		{ PtrInfo = PtrInfo0 }
	;
		{ Res0 = error(Err) },
		{ io__error_message(Err, Msg) },
		{ Res = error(Msg) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_root(initial_deep::in, deep_result(initial_deep)::out,
	ptr_info::in, ptr_info::out, io__state::di, io__state::uo) is det.

read_root(InitDeep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading root.\n", []),
	read_ptr(csd, Res0),
	(
		{ Res0 = ok(Ptr) },
		{ InitDeep1 = InitDeep0 ^ init_root
			:= call_site_dynamic_ptr(Ptr) },
		read_call_graph2(InitDeep1, Res, PtrInfo0, PtrInfo)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_call_site_static(initial_deep::in, deep_result(initial_deep)::out,
	ptr_info::in, ptr_info::out, io__state::di, io__state::uo) is det.

read_call_site_static(InitDeep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading call_site_static.\n", []),
	read_sequence4(
		read_ptr(css),
		read_call_site_kind,
		read_num,
		read_string,
		(pred(Ptr::in, Kind::in, LineNumber::in, Str::in, Res0::out)
				is det :-
			CSS = call_site_static(Kind, LineNumber, Str),
			insert(InitDeep0 ^ init_call_site_statics,
				Ptr, CSS, CSSs),
			InitDeep = InitDeep0 ^ init_call_site_statics := CSSs,
			Res0 = ok({InitDeep, Ptr})
		),
		Res1),
	(
		{ Res1 = ok({InitDeep1, NewPtr}) },
		{ PtrInfo1 = PtrInfo0 ^ css := max(PtrInfo0 ^ css, NewPtr) },
		read_call_graph2(InitDeep1, Res, PtrInfo1, PtrInfo)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).


:- pred read_proc_static(initial_deep::in, deep_result(initial_deep)::out,
	ptr_info::in, ptr_info::out, io__state::di, io__state::uo) is det.

read_proc_static(InitDeep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading proc_static.\n", []),
	read_sequence4(
		read_ptr(ps),
		read_proc_id,
		read_string,
		read_num,
		(pred(Ptr0::in, Id0::in, F0::in, N0::in, Stuff0::out) is det :-
			Stuff0 = ok({Ptr0, Id0, F0, N0})
		),
		Res1),
	(
		{ Res1 = ok({Ptr, Id, FileName, N}) },
		read_n_things(N, read_ptr(css), Res2),
		(
			{ Res2 = ok(Ptrs0) },
			{ map((pred(Ptr1::in, Ptr2::out) is det :-
				Ptr2 = call_site_static_ptr(Ptr1)
			), Ptrs0, Ptrs) },
			{ ProcStatic =
				proc_static(Id, FileName, array(Ptrs)) },
			{ insert(InitDeep0 ^ init_proc_statics,
				Ptr, ProcStatic, PSs) },
			{ InitDeep1 = InitDeep0 ^ init_proc_statics := PSs },
			{ PtrInfo1 = PtrInfo0 ^ ps :=
				max(PtrInfo0 ^ ps, Ptr) },
			read_call_graph2(InitDeep1, Res, PtrInfo1, PtrInfo)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo0 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_proc_id(deep_result(proc_id)::out,
	io__state::di, io__state::uo) is det.

read_proc_id(Res) -->
	read_deep_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = token_isa_compiler_generated } ->
			read_proc_id_compiler_generated(Res)
		; { Byte = token_isa_predicate } ->
			read_proc_id_user_defined(predicate, Res)
		; { Byte = token_isa_function } ->
			read_proc_id_user_defined(function, Res)
		;
			{ format("unexpected call_site_kind %d",
				[i(Byte)], Msg) },
			{ Res = error(Msg) }
		)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_proc_id_compiler_generated(deep_result(proc_id)::out,
	io__state::di, io__state::uo) is det.

read_proc_id_compiler_generated(Res) -->
	read_sequence6(
		read_string,
		read_string,
		read_string,
		read_string,
		read_num,
		read_num,
		(pred(TypeName::in, TypeModule::in, DefModule::in,
			PredName::in, Arity::in, Mode::in, ProcId::out)
			is det :-
			ProcId = ok(compiler_generated(TypeName, TypeModule,
				DefModule, PredName, Arity, Mode))
		),
		Res).

:- pred read_proc_id_user_defined(pred_or_func::in, deep_result(proc_id)::out,
	io__state::di, io__state::uo) is det.

read_proc_id_user_defined(PredOrFunc, Res) -->
	read_sequence5(
		read_string,
		read_string,
		read_string,
		read_num,
		read_num,
		(pred(DeclModule::in, DefModule::in, Name::in,
			Arity::in, Mode::in, ProcId::out)
			is det :-
			ProcId = ok(user_defined(PredOrFunc, DeclModule,
				DefModule, Name, Arity, Mode))
		),
		Res).

:- pred read_proc_dynamic(initial_deep::in, deep_result(initial_deep)::out,
	ptr_info::in, ptr_info::out, io__state::di, io__state::uo) is det.

read_proc_dynamic(InitDeep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading proc_dynamic.\n", []),
	read_sequence3(
		read_ptr(pd),
		read_ptr(ps),
		read_num,
		(pred(Ptr0::in, Ptr1::in, N0::in, Stuff0::out) is det :-
			Stuff0 = ok({Ptr0, Ptr1, N0})
		),
		Res1),
	(
		{ Res1 = ok({Ptr, SPtr, N}) },
		read_n_things(N, read_call_site_ref, Res2),
		(
			{ Res2 = ok(Refs) },
			{ PSPtr = proc_static_ptr(SPtr) },
			{ PD = proc_dynamic(PSPtr, array(Refs)) },
			{ insert(InitDeep0 ^ init_proc_dynamics, Ptr, PD, PDs) },
			{ InitDeep1 = InitDeep0 ^ init_proc_dynamics := PDs },
			{ PtrInfo1 = PtrInfo0 ^ pd := max(PtrInfo0 ^ pd, Ptr) },
			read_call_graph2(InitDeep1, Res, PtrInfo1, PtrInfo)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo0 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_call_site_dynamic(initial_deep::in,
	deep_result(initial_deep)::out, ptr_info::in, ptr_info::out,
	io__state::di, io__state::uo) is det.

read_call_site_dynamic(InitDeep0, Res, PtrInfo0, PtrInfo) -->
	%format("reading call_site_dynamic.\n", []),
	read_ptr(csd, Res1),
	(
		{ Res1 = ok(Ptr1) },
		read_ptr(pd, Res2),
		(
			{ Res2 = ok(Ptr2) },
			read_profile(Res3),
			(
				{ Res3 = ok(Profile) },
				{ PDPtr = proc_dynamic_ptr(Ptr2) },
				{ CD = call_site_dynamic(PDPtr, Profile) },
				{ insert(InitDeep0 ^ init_call_site_dynamics, Ptr1,
						CD, CDs) },
				{ InitDeep1 = InitDeep0 ^ init_call_site_dynamics := CDs },
				{ PtrInfo1 = PtrInfo0 ^ csd :=
						max(PtrInfo0 ^ csd, Ptr1) },
				read_call_graph2(InitDeep1, Res, PtrInfo1, PtrInfo)
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) },
				{ PtrInfo = PtrInfo0 }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) },
			{ PtrInfo = PtrInfo0 }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) },
		{ PtrInfo = PtrInfo0 }
	).

:- pred read_profile(deep_result(own_prof_info)::out,
	io__state::di, io__state::uo) is det.

read_profile(Res) -->
	read_num(Res0),
	(
		{ Res0 = ok(Mask) },
		{ MaybeError0 = no },
		( { Mask /\ 0x0001 \= 0 } ->
			maybe_read_num_handle_error(Calls,
				MaybeError0, MaybeError1)
		;
			{ Calls = 0 },
			{ MaybeError1 = MaybeError0 }
		),
		( { Mask /\ 0x0002 \= 0 } ->
			maybe_read_num_handle_error(Exits,
				MaybeError1, MaybeError2)
		;
			{ Exits = 0 },
			{ MaybeError2 = MaybeError1 }
		),
		( { Mask /\ 0x0004 \= 0 } ->
			maybe_read_num_handle_error(Fails,
				MaybeError2, MaybeError3)
		;
			{ Fails = 0 },
			{ MaybeError3 = MaybeError2 }
		),
		( { Mask /\ 0x0008 \= 0 } ->
			maybe_read_num_handle_error(Redos,
				MaybeError3, MaybeError4)
		;
			{ Redos = 0 },
			{ MaybeError4 = MaybeError3 }
		),
		( { Mask /\ 0x0010 \= 0 } ->
			maybe_read_num_handle_error(Quanta,
				MaybeError4, MaybeError5)
		;
			{ Quanta = 0 },
			{ MaybeError5 = MaybeError4 }
		),
		( { Mask /\ 0x0020 \= 0 } ->
			maybe_read_num_handle_error(Mallocs,
				MaybeError5, MaybeError6)
		;
			{ Mallocs = 0 },
			{ MaybeError6 = MaybeError5 }
		),
		( { Mask /\ 0x0040 \= 0 } ->
			maybe_read_num_handle_error(Words,
				MaybeError6, MaybeError7)
		;
			{ Words = 0 },
			{ MaybeError7 = MaybeError6 }
		),
		(
			{ MaybeError7 = yes(Error) },
			{ Res = error(Error) }
		;
			{ MaybeError7 = no },
			{ Res = ok(compress_profile(Calls, Exits, Fails, Redos, 
				Quanta, Mallocs, Words)) }
		)
	;
		{ Res0 = error(Error) },
		{ Res = error(Error) }
	).

:- pred maybe_read_num_handle_error(int::out,
	maybe(string)::in, maybe(string)::out,
	io__state::di, io__state::uo) is det.

maybe_read_num_handle_error(Value, MaybeError0, MaybeError) -->
	read_num(Res),
	(
		{ Res = ok(Value) },
		{ MaybeError = MaybeError0 }
	;
		{ Res = error(Error) },
		{ Value = 0 },
		{ MaybeError = yes(Error) }
	).

compress_profile(Calls, Exits, Fails, Redos, Quanta, Mallocs, Words) = PI :-
	(
		Calls = Exits,
		Fails = 0,
		Redos = 0
	->
		(
			Quanta = 0
		->
			PI = zdet(Calls, Mallocs, Words)
		;
			PI = det(Calls, Quanta, Mallocs, Words)
		)
	;
		PI = all(Calls, Exits, Fails, Redos, Quanta, Mallocs, Words)
	).

compress_profile(PI0) = PI :-
	(
		PI0 = all(Calls, Exits, Fails, Redos, Quanta, Mallocs, Words),
		(
			Calls = Exits,
			Fails = 0,
			Redos = 0
		->
			(
				Quanta = 0
			->
				PI = zdet(Calls, Mallocs, Words)
			;
				PI = det(Calls, Quanta, Mallocs, Words)
			)
		;
			PI = PI0
		)
	;
		PI0 = det(Calls, Quanta, Mallocs, Words),
		(
			Quanta = 0
		->
			PI = zdet(Calls, Mallocs, Words)
		;
			PI = PI0
		)
	;
		PI0 = zdet(_, _, _),
		PI = PI0
	).

:- pred read_call_site_ref(deep_result(call_site_array_slot)::out,
	io__state::di, io__state::uo) is det.

read_call_site_ref(Res) -->
	%format("reading call_site_ref.\n", []),
	read_call_site_kind(Res1),
	(
		{ Res1 = ok(Kind) },
		( { Kind = normal_call } ->
			read_ptr(csd, Res2),
			(
				{ Res2 = ok(Ptr) },
				{ CDPtr = call_site_dynamic_ptr(Ptr) },
				{ Res = ok(normal(CDPtr)) }
			;
				{ Res2 = error(Err) },
				{ Res = error(Err) }
			)
		;
			read_things(read_ptr(csd), Res2),
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
		{ Res = error(Err) }
	).

:- pred read_call_site_kind(deep_result(call_site_kind), io__state, io__state).
:- mode read_call_site_kind(out, di, uo) is det.

read_call_site_kind(Res) -->
	read_deep_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = token_normal_call } ->
			{ Res = ok(normal_call) }
		; { Byte = token_special_call } ->
			{ Res = ok(special_call) }
		; { Byte = token_higher_order_call } ->
			{ Res = ok(higher_order_call) }
		; { Byte = token_method_call } ->
			{ Res = ok(method_call) }
		; { Byte = token_callback } ->
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

:- pred read_n_things(int, pred(deep_result(T), io__state, io__state),
		deep_result(list(T)), io__state, io__state).
:- mode read_n_things(in, pred(out, di, uo) is det, out, di, uo) is det.

read_n_things(N, ThingReader, Res) -->
	read_n_things(N, ThingReader, [], Res0),
	(
		{ Res0 = ok(Things0) },
		{ reverse(Things0, Things) },
		{ Res = ok(Things) }
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_n_things(int, pred(deep_result(T), io__state, io__state),
		list(T), deep_result(list(T)), io__state, io__state).
:- mode read_n_things(in, pred(out, di, uo) is det, in, out, di, uo) is det.

read_n_things(N, ThingReader, Things0, Res) -->
	( { N =< 0 } ->
		{ Res = ok(Things0) }
	;
		call(ThingReader, Res1),
		(
			{ Res1 = ok(Thing) },
			read_n_things(N - 1, ThingReader, [Thing|Things0], Res)
		;
			{ Res1 = error(Err) },
			{ Res = error(Err) }
		)
	).

:- pred read_things(pred(deep_result(T), io__state, io__state),
		deep_result(list(T)), io__state, io__state).
:- mode read_things(pred(out, di, uo) is det, out, di, uo) is det.

read_things(ThingReader, Res) -->
	read_things(ThingReader, [], Res0),
	(
		{ Res0 = ok(Things0) },
		{ reverse(Things0, Things) },
		{ Res = ok(Things) }
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_things(pred(deep_result(T), io__state, io__state),
		list(T), deep_result(list(T)), io__state, io__state).
:- mode read_things(pred(out, di, uo) is det, in, out, di, uo) is det.

read_things(ThingReader, Things0, Res) -->
	read_deep_byte(Res0),
	(
		{ Res0 = ok(Byte) },
		( { Byte = 0 } ->
			{ Res = ok(Things0) }
		;
			putback_byte(Byte),
			call(ThingReader, Res1),
			(
				{ Res1 = ok(Thing) },
				read_things(ThingReader, [Thing|Things0], Res)
			;
				{ Res1 = error(Err) },
				{ Res = error(Err) }
			)
		)
	;
		{ Res0 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_sequence3(
		pred(deep_result(T1), io__state, io__state),
		pred(deep_result(T2), io__state, io__state),
		pred(deep_result(T3), io__state, io__state),
		pred(T1, T2, T3, deep_result(T4)),
		deep_result(T4), io__state, io__state).
:- mode read_sequence3(
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(in, in, in, out) is det,
		out, di, uo) is det.

read_sequence3(P1, P2, P3, Combine, Res) -->
	call(P1, Res1),
	(
		{ Res1 = ok(T1) },
		call(P2, Res2),
		(
			{ Res2 = ok(T2) },
			call(P3, Res3),
			(
				{ Res3 = ok(T3) },
				{ call(Combine, T1, T2, T3, Res) }
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_sequence4(
		pred(deep_result(T1), io__state, io__state),
		pred(deep_result(T2), io__state, io__state),
		pred(deep_result(T3), io__state, io__state),
		pred(deep_result(T4), io__state, io__state),
		pred(T1, T2, T3, T4, deep_result(T5)),
		deep_result(T5), io__state, io__state).
:- mode read_sequence4(
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(in, in, in, in, out) is det,
		out, di, uo) is det.

read_sequence4(P1, P2, P3, P4, Combine, Res) -->
	call(P1, Res1),
	(
		{ Res1 = ok(T1) },
		call(P2, Res2),
		(
			{ Res2 = ok(T2) },
			call(P3, Res3),
			(
				{ Res3 = ok(T3) },
				call(P4, Res4),
				(
					{ Res4 = ok(T4) },
					{ call(Combine, T1, T2, T3, T4, Res) }
				;
					{ Res4 = error(Err) },
					{ Res = error(Err) }
				)
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_sequence5(
		pred(deep_result(T1), io__state, io__state),
		pred(deep_result(T2), io__state, io__state),
		pred(deep_result(T3), io__state, io__state),
		pred(deep_result(T4), io__state, io__state),
		pred(deep_result(T5), io__state, io__state),
		pred(T1, T2, T3, T4, T5, deep_result(T6)),
		deep_result(T6), io__state, io__state).
:- mode read_sequence5(
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(in, in, in, in, in, out) is det,
		out, di, uo) is det.

read_sequence5(P1, P2, P3, P4, P5, Combine, Res) -->
	call(P1, Res1),
	(
		{ Res1 = ok(T1) },
		call(P2, Res2),
		(
			{ Res2 = ok(T2) },
			call(P3, Res3),
			(
				{ Res3 = ok(T3) },
				call(P4, Res4),
				(
					{ Res4 = ok(T4) },
					call(P5, Res5),
					(
						{ Res5 = ok(T5) },
						{ call(Combine, T1, T2, T3, T4,
							T5, Res) }
					;
						{ Res5 = error(Err) },
						{ Res = error(Err) }
					)
				;
					{ Res4 = error(Err) },
					{ Res = error(Err) }
				)
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) }
	).

:- pred read_sequence6(
		pred(deep_result(T1), io__state, io__state),
		pred(deep_result(T2), io__state, io__state),
		pred(deep_result(T3), io__state, io__state),
		pred(deep_result(T4), io__state, io__state),
		pred(deep_result(T5), io__state, io__state),
		pred(deep_result(T6), io__state, io__state),
		pred(T1, T2, T3, T4, T5, T6, deep_result(T7)),
		deep_result(T7), io__state, io__state).
:- mode read_sequence6(
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(out, di, uo) is det,
		pred(in, in, in, in, in, in, out) is det,
		out, di, uo) is det.

read_sequence6(P1, P2, P3, P4, P5, P6, Combine, Res) -->
	call(P1, Res1),
	(
		{ Res1 = ok(T1) },
		call(P2, Res2),
		(
			{ Res2 = ok(T2) },
			call(P3, Res3),
			(
				{ Res3 = ok(T3) },
				call(P4, Res4),
				(
					{ Res4 = ok(T4) },
					call(P5, Res5),
					(
						{ Res5 = ok(T5) },
						call(P6, Res6),
						(
							{ Res6 = ok(T6) },
							{ call(Combine, T1, T2,
								T3, T4, T5,
								T6, Res) }
						;
							{ Res6 = error(Err) },
							{ Res = error(Err) }
						)
					;
						{ Res5 = error(Err) },
						{ Res = error(Err) }
					)
				;
					{ Res4 = error(Err) },
					{ Res = error(Err) }
				)
			;
				{ Res3 = error(Err) },
				{ Res = error(Err) }
			)
		;
			{ Res2 = error(Err) },
			{ Res = error(Err) }
		)
	;
		{ Res1 = error(Err) },
		{ Res = error(Err) }
	).

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

:- pred read_ptr(ptr_kind, deep_result(int), io__state, io__state).
:- mode read_ptr(in, out, di, uo) is det.

read_ptr(_Kind, Res) -->
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

%:- func max(int, int) = int.
%max(A, B) = (A > B -> A ; B).

%------------------------------------------------------------------------------%

:- pragma c_header_code("
#include ""mercury_deep_profiling.h""
").

:- func token_root = int.
:- pragma c_code(token_root = (X::out),
	[will_not_call_mercury, thread_safe], "X = root;").

:- func token_call_site_static = int.
:- pragma c_code(token_call_site_static = (X::out),
	[will_not_call_mercury, thread_safe], "X = callsite_static;").

:- func token_call_site_dynamic = int.
:- pragma c_code(token_call_site_dynamic = (X::out),
	[will_not_call_mercury, thread_safe], "X = callsite_dynamic;").

:- func token_proc_static = int.
:- pragma c_code(token_proc_static = (X::out),
	[will_not_call_mercury, thread_safe], "X = proc_static;").

:- func token_proc_dynamic = int.
:- pragma c_code(token_proc_dynamic = (X::out),
	[will_not_call_mercury, thread_safe], "X = proc_dynamic;").

:- func token_normal_call = int.
:- pragma c_code(token_normal_call = (X::out),
	[will_not_call_mercury, thread_safe], "X = MR_normal_call;").

:- func token_special_call = int.
:- pragma c_code(token_special_call = (X::out),
	[will_not_call_mercury, thread_safe], "X = MR_special_call;").

:- func token_higher_order_call = int.
:- pragma c_code(token_higher_order_call = (X::out),
	[will_not_call_mercury, thread_safe], "X = MR_higher_order_call;").

:- func token_method_call = int.
:- pragma c_code(token_method_call = (X::out),
	[will_not_call_mercury, thread_safe], "X = MR_method_call;").

:- func token_callback = int.
:- pragma c_code(token_callback = (X::out),
	[will_not_call_mercury, thread_safe], "X = MR_callback;").

:- func token_isa_predicate = int.
:- pragma c_code(token_isa_predicate = (X::out),
	[will_not_call_mercury, thread_safe], "X = isa_predicate;").

:- func token_isa_function = int.
:- pragma c_code(token_isa_function = (X::out),
	[will_not_call_mercury, thread_safe], "X = isa_function;").

:- func token_isa_compiler_generated = int.
:- pragma c_code(token_isa_compiler_generated = (X::out),
	[will_not_call_mercury, thread_safe], "X = isa_compiler_generated;").

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

/*
deep2dot(FileName, Depth, Deep) -->
	io__tell(FileName, Res),
	(
		{ Res = ok },
		format("digraph L0 {\n", []),
		format("size =""8,11"";\n", []),
		{ Deep ^ root = call_site_dynamic_ptr(Root) },
		{ lookup(Deep ^ clique_index, Root, RootClique) },
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
		{ lookup(Deep ^ clique_tree, CliqueN, Children0) },
		{ lookup(Deep ^ clique_members, CliqueN, Members) },
		(
			{ Members = [call_site_dynamic_ptr(CSDI)|_] },
			{ CSDI > 0 },
			{ lookup(Deep ^ call_site_dynamics, CSDI, CSD) },
			{ CSD = call_site_dynamic(PDPtr, _) },
			{ PDPtr = proc_dynamic_ptr(PDI), PDI > 0 },
			{ lookup(Deep ^ proc_dynamics, PDI, PD) },
			{ PD = proc_dynamic(PSPtr, _) },
			{ PSPtr = proc_static_ptr(PSI), PSI > 0 },
			{ lookup(Deep ^ proc_statics, PSI, PS) },
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
	array_foldl((pred(CSDI::in, CSD::in, di, uo) is det -->
		{ CSDI = From },
		{ CSD = call_site_dynamic(proc_dynamic_ptr(To), _) },
		format("n%x -> { n%x };\n", [i(From), i(To)])
	), Deep ^ call_site_dynamics),
	array_foldl((pred(PDI::in, PD::in, di, uo) is det -->
		{ PDI = From },
		{ PD = proc_dynamic(PSPtr, Refs) },
		{ PSPtr = proc_static_ptr(PSI) },
		{ lookup(Deep ^ proc_statics, PSI, PS) },
		{ PS = proc_static(Id, _, _) },
		format("n%x [label=""%s""];\n",
			[i(From), s(proc_id_to_string(Id))]),
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
	), Deep ^ proc_dynamics),
	format("};\n", []).

:- pred resize_arrays(deep_result(initial_deep)::in, ptr_info::in,
	deep_result(initial_deep)::out) is det.

resize_arrays(error(Err), _, error(Err)).
resize_arrays(ok(InitDeep0), PI, ok(InitDeep)) :-
	PI ^ csd = CSDMax,
	CSDs0 = InitDeep0 ^ init_call_site_dynamics,
	lookup(CSDs0, 0, CSDx),
	resize(u(CSDs0), CSDMax + 1, CSDx, CSDs),
	InitDeep1 = InitDeep0 ^ init_call_site_dynamics := CSDs,

	PI ^ pd = PDMax,
	PDs0 = InitDeep1 ^ init_proc_dynamics,
	lookup(PDs0, 0, PDx),
	resize(u(PDs0), PDMax + 1, PDx, PDs),
	InitDeep2 = InitDeep1 ^ init_proc_dynamics := PDs,

	PI ^ css = CSSMax,
	CSSs0 = InitDeep2 ^ init_call_site_statics,
	lookup(CSSs0, 0, CSSx),
	resize(u(CSSs0), CSSMax + 1, CSSx, CSSs),
	InitDeep3 = InitDeep2 ^ init_call_site_statics := CSSs,

	PI ^ ps = PSMax,
	PSs0 = InitDeep3 ^ init_proc_statics,
	lookup(PSs0, 0, PSx),
	resize(u(PSs0), PSMax + 1, PSx, PSs),
	InitDeep = InitDeep3 ^ init_proc_statics := PSs.
