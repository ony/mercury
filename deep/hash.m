%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

:- module hash.

:- interface.

:- import_module array.

:- type hashtable(V).

:- func init(int) = hashtable(V).
:- mode (init(in) = array_uo) is det.

:- func insert(hashtable(V), int, V) = hashtable(V).
:- mode (insert(array_di, in, in) = array_uo) is det.

:- func search(hashtable(V), int) = V.
:- mode (search(array_ui, in) = out) is semidet.

:- implementation.

:- import_module int, list.

:- type hashtable(V) == array(list({int, V})).

init(Width) = init(Width, []).

insert(Table0, Key, Value) = Table :-
	array__max(Table0, Max),
	H = Key mod (Max + 1),
	lookup(Table0, H, List0),
	List = [{Key, Value}|List0],
	set(Table0, H, List, Table).

search(Table, Key) = Value :-
	array__max(Table, Max),
	H = Key mod (Max + 1),
	lookup(Table, H, List0),
	find(List0, Key, Value).

:- pred find(list({int, V}), int, V).
:- mode find(in, in, out) is semidet.

find([{K0, V0}|Rest], K, V) :-
	( K = K0 ->
		V = V0
	;
		find(Rest, K, V)
	).

