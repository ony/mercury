:- module intermod_pragma_import2.

:- interface.

:- pred implemented_as_pragma_import(T::in, int::out) is det.

:- implementation.

:- pred p(T::in, int::out) is det.

p(_, 4).

:- pragma foreign_proc("C",
	implemented_as_pragma_import(I::in, O::out),
	[promise_pure, will_not_call_mercury],
"
	imported(TypeInfo_for_T, I, &O);
").

:- pragma foreign_export("C", p(in, out), "imported").
