:- module deep:cliques.

:- interface.

:- type graph.

:- import_module list, set.

:- pred init(graph).
:- mode init(out) is det.

:- pred add_arc(graph, int, int, graph).
:- mode add_arc(in, in, in, out) is det.

:- pred atsort(graph, list(set(int))).
:- mode atsort(in, out) is det.

:- implementation.

:- import_module dense_bitset.
:- import_module array, int.

:- type graph	--->
		graph(
			int,
			array(set(int))
		).

:- type visit == dense_bitset.

init(graph(1, Array)) :-
	init(16, init, Array).

add_arc(graph(Size0, Array0), From, To, Graph) :-
	( in_bounds(Array0, From) ->
		lookup(Array0, From, Tos0),
		insert(Tos0, To, Tos),
		set(u(Array0), From, Tos, Array),
		Size = max(max(From, To), Size0),
		Graph = graph(Size, Array)
	;
		array__size(Array0, Size),
		array__resize(u(Array0), Size * 2, init, Array1),
		add_arc(graph(Size0, Array1), From, To, Graph)
	).

:- func max(int, int) = int.
max(X, Y) = (X > Y -> X ; Y).

atsort(Graph, ATSort) :-
	dfsrev(Graph, DfsRev),
	inverse(Graph, InvGraph),
	Visit = init,
	atsort_2(DfsRev, InvGraph, Visit, [], ATSort0),
	reverse(ATSort0, ATSort).

:- pred atsort_2(list(int), graph, visit, list(set(int)), list(set(int))).
:- mode atsort_2(in, in, array_di, in, out) is det.

atsort_2([], _InvGraph, _Visit, ATSort, ATSort).
atsort_2([Node|Nodes], InvGraph, Visit0, ATSort0, ATSort) :-
	( member(Node, Visit0) ->
		atsort_2(Nodes, InvGraph, Visit0, ATSort0, ATSort)
	;
		dfs_3([Node], InvGraph, Visit0, [], Visit, CliqueList),
		list_to_set(CliqueList, Clique),
		atsort_2(Nodes, InvGraph, Visit, [Clique|ATSort0], ATSort)
	).

:- pred dfsrev(graph, list(int)).
:- mode dfsrev(in, out) is det.

dfsrev(Graph, DfsRev) :-
	Graph = graph(N, _Array),
	mklist(N, [], DomList),
	Visit = init,
	dfs_2(DomList, Graph, Visit, [], DfsRev).

:- pred mklist(int, list(int), list(int)).
:- mode mklist(in, in, out) is det.

mklist(N, Acc0, Acc) :-
	( N < 0 ->
		Acc = Acc0
	;
		Acc1 = [N|Acc0],
		mklist(N - 1, Acc1, Acc)
	).

:- pred dfs_2(list(int), graph, visit, list(int), list(int)).
:- mode dfs_2(in, in, array_di, in, out) is det.

dfs_2([], _Graph, _Visit, DfsRev, DfsRev).
dfs_2([Node|Nodes], Graph, Visit0, DfsRev0, DfsRev) :-
	dfs_3([Node], Graph, Visit0, DfsRev0, Visit, DfsRev1),
	dfs_2(Nodes, Graph, Visit, DfsRev1, DfsRev).

:- pred dfs_3(list(int), graph, visit, list(int), visit, list(int)).
:- mode dfs_3(in, in, array_di, in, array_uo, out) is det.

dfs_3([], _Graph, Visit, Dfs, Visit, Dfs).
dfs_3([Node|Nodes], Graph, Visit0, Dfs0, Visit, Dfs) :-
	( member(Node, Visit0) ->
		dfs_3(Nodes, Graph, Visit0, Dfs0, Visit, Dfs)
	;
		Visit1 = insert(Visit0, Node),
		successors(Graph, Node, Succ),
		set__to_sorted_list(Succ, SuccList),
		dfs_3(SuccList, Graph, Visit1, Dfs0, Visit2, Dfs1),
		Dfs2 = [Node|Dfs1],
		dfs_3(Nodes, Graph, Visit2, Dfs2, Visit, Dfs)
	).

:- pred inverse(graph, graph).
:- mode inverse(in, out) is det.

inverse(Graph, InvGraph) :-
	init(InvGraph0),
	Graph = graph(Size, _Array),
	inverse_2(Size, Graph, InvGraph0, InvGraph).

:- pred inverse_2(int, graph, graph, graph).
:- mode inverse_2(in, in, in, out) is det.

inverse_2(To, Graph, InvGraph0, InvGraph) :-
	( To >= 0 ->
		successors(Graph, To, Froms),
		set__to_sorted_list(Froms, FromList),
		inverse_3(FromList, To, InvGraph0, InvGraph1),
		inverse_2(To - 1, Graph, InvGraph1, InvGraph)
	;
		InvGraph = InvGraph0
	).

:- pred inverse_3(list(int), int, graph, graph).
:- mode inverse_3(in, in, in, out) is det.

inverse_3([], _, Graph, Graph).
inverse_3([From|FromList], To, Graph0, Graph) :-
	add_arc(Graph0, From, To, Graph1),
	inverse_3(FromList, To, Graph1, Graph).

:- pred successors(graph, int, set(int)).
:- mode successors(in, in, out) is det.

successors(graph(_Size, Array), From, Tos) :-
	( in_bounds(Array, From) ->
		lookup(Array, From, Tos)
	;
		Tos = init
	).

