%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_data
% Main authors: nancy
% 
% The data structures which are shared between the various phases of the
% structure reuse analysis.
%
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_data.
:- interface.

:- import_module hlds__hlds_data.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_alias_as.
:- import_module structure_reuse__sr_live.

:- import_module bool, map, set, std_util, list, io, term.

	% The information placed in the goal info which is used by
	% structure reuse.
	% This field should be initilaised to empty.
	% The sr_dead module replaces empty with choice.
	% The sr_choice&sr_indirect module replaces choice with 
	% 	potential_reuse.
	% The sr_split module replaces potential_reuse with reuse for
	% 	the reuse-version of a procedure. 
:- type reuse_goal_info
	--->	empty
	;	choice(choice_info)
	; 	potential_reuse(short_reuse_info)
	;	reuse(short_reuse_info).

:- type short_reuse_info --->
				no_reuse 
			; 	cell_died
			; 	cell_reused(
						% The variable selected
						% for reuse.
					prog_var,
						% Is the reuse conditional?
					bool,
						% What are the possible
						% cons_ids that the cell
						% to be reused can have.
					list(cons_id),
						% Which of the fields of
						% the cell to be reused
						% already contain the
						% correct value.
					list(bool)
				)

					% Call the reuse version of the
					% call and whether calling the
					% reuse version is conditional.
			; 	reuse_call(bool)
			; 	missed_reuse_call(list(string)). 

:- type reuse_var
	--->	reuse_var(
			var		:: prog_var,
			condition	:: reuse_condition,
			cons_ids	:: maybe(list(cons_id)),
			reuse_fields	:: maybe(list(bool))
		).

:- type choice_info
	--->	deconstruct(
				% The condition under which this cell
				% can be reused, if at all.
			maybe(reuse_condition)
		)
	;	construct(
				% The cells which could be reused by the
				% current construction unification and
				% the condition associated with reusing
				% that cell.
			set(reuse_var)
		).

	% A reuse, whether direct or indirect, is only allowed as long
	% as the caller fulfills some conditions.  This type keeps track
	% of the information needed to verify whether the condition for
	% reuse is met or not. 
:- type reuse_condition
	--->	always
	;	condition(
		   nodes 		:: set(prog_data__datastruct),
		   local_use_headvars 	:: set(prog_var),
		   local_alias_headvars :: alias_as 
		).

:- type memo_reuse == maybe(list(reuse_condition)).


%-----------------------------------------------------------------------------%
% small predicates for manipulating/transforming reuse_goal_info
%-----------------------------------------------------------------------------%

% :- func reuse_to_string(reuse_goal_info) = string. 

%-----------------------------------------------------------------------------%
% reuse_condition predicates 
%-----------------------------------------------------------------------------%
:- pred reuse_condition_merge(reuse_condition::in, 
				reuse_condition::in,
				reuse_condition::out) is det.

:- pred reuse_condition_equal(reuse_condition::in, 
			reuse_condition::in) is semidet.

	% condition_init(Var, LFUi, LBUi, ALIASi, HVs, Condition).
:- pred reuse_condition_init(module_info::in, proc_info::in, prog_var::in,
			set(prog_var)::in, set(prog_var)::in, 
			alias_as::in, list(prog_var)::in, 
			reuse_condition::out) is det.

	% Rename the reuse condition given a map from FromVars, to
	% ToVars.
:- pred reuse_condition_rename(map(prog_var, prog_var)::in, 
		maybe(substitution(tvar_type))::in, 
		reuse_condition::in, reuse_condition::out) is det.

	% Print the reuse-condition.
:- pred reuse_condition_print(proc_info::in, pred_info::in,
				reuse_condition::in, 
				io__state::di, io__state::uo) is det.

	% Check whether the given live_set and alias_as satisfy
	% the condition for reuse. 
:- pred reuse_condition_verify(proc_info::in, module_info::in, 
			live_set::in, alias_as::in, set(prog_var)::in, 
			reuse_condition::in) is semidet.

:- pred reuse_condition_update(proc_info::in, module_info::in, 
			set(prog_var)::in, set(prog_var)::in, 
			alias_as::in, list(prog_var)::in, 
			reuse_condition::in, reuse_condition::out) is det.

:- pred reuse_conditions_simplify(list(reuse_condition)::in, 
		list(reuse_condition)::out) is det.
%-----------------------------------------------------------------------------%
% memo_reuse predicates
%-----------------------------------------------------------------------------%

:- pred memo_reuse_equal(memo_reuse::in, memo_reuse::in) is semidet.
:- pred memo_reuse_init(memo_reuse::out) is det.
:- pred memo_reuse_top(memo_reuse::in) is semidet.
:- pred memo_reuse_rename(map(prog_var, prog_var)::in, 
		maybe(substitution(tvar_type))::in, 
		memo_reuse::in, memo_reuse::out) is det.
	% memo_reuse_rename_types(FromTypes, ToTypes, Memo0, Memo).
	% Rename all the types occurring in the memo_reuse from FromTypes, 
	% to ToTypes.
:- pred memo_reuse_print(memo_reuse::in, sym_name::in, proc_info::in,
		pred_info::in, io__state::di, io__state::uo) is det.
:- pred memo_reuse_print_dump(memo_reuse::in, proc_info::in, 
		pred_info::in, io__state::di, io__state::uo) is det. 
:- pred memo_reuse_parse(term(T)::in, memo_reuse::out, 
		maybe(sym_name)::out) is semidet.
:- pred memo_reuse_verify_reuse(proc_info::in, module_info::in, 
		memo_reuse::in, live_set::in, alias_as::in,
		set(prog_var)::in) is semidet.
:- pred memo_reuse_is_conditional(memo_reuse::in) is semidet.
:- pred memo_reuse_is_unconditional(memo_reuse::in) is semidet.
:- pred memo_reuse_simplify(memo_reuse::in, memo_reuse::out) is det.
:- pred memo_reuse_merge(memo_reuse::in, memo_reuse::in, 
		memo_reuse::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module hlds__instmap. 
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_io.
:- import_module parse_tree__prog_io_pasr.
:- import_module parse_tree__prog_io_util.
:- import_module parse_tree__prog_out.
:- import_module possible_alias__pa_alias_as.
:- import_module possible_alias__pa_datastruct.
:- import_module possible_alias__pa_sr_util.
:- import_module structure_reuse__sr_util.

:- import_module list, string, require, varset, bool, assoc_list.
%-----------------------------------------------------------------------------%
/**
reuse_to_string(Reuse) = String :- 
	Reuse = empty, 
	String = "empty".
reuse_to_string(Reuse) = String :- 
	Reuse = choice(_), 
	String = "choice".
reuse_to_string(Reuse) = String :- 
	Reuse = potential_reuse(_), 
	String = "potential_reuse".
reuse_to_string(Reuse) = String :- 
	Reuse = reuse, 
	String = "reuse".
**/
%-----------------------------------------------------------------------------%


reuse_condition_merge(C1, C2, C):-
	(
		reuse_condition_equal(C1, C2)
	->
		C = C1
	;
		reuse_condition_merge_2(C1, C2, C)
	).

:- pred reuse_condition_merge_2(reuse_condition::in, 
				reuse_condition::in,
				reuse_condition::out) is det.

reuse_condition_merge_2(C1, C2, C) :- 
	(
		C1 = condition(N1, U1, A1)
	->
		(
			C2 = condition(N2, U2, A2)
		->
			set__union(N1, N2, N),
			set__union(U1, U2, U),
			pa_alias_as__add(A1, A2, A),
			C = condition(N, U, A)
		;
			% C2 = always
			C = C1
		)
	;
		% C1 = always
		C = C2
	).
			
			
reuse_condition_equal(always, always).
reuse_condition_equal(condition(Nodes1, LU1, LA1), 
			condition(Nodes2, LU2, LA2)):-
	set__equal(Nodes1, Nodes2),
	set__equal(LU1, LU2),
	pa_alias_as__equal(LA1, LA2).

reuse_condition_init(ModuleInfo, ProcInfo, 
				Var, LFUi, LBUi, ALIASi, HVs, Condition):- 
	% First determine the nodes to which the reuse is related. 
	% There are two cased:
	% 1. Var is a headvar, then it is sufficient to keep the topcel
	%    of that Var as only node. HeadVar-datastructures aliased
	%    to that node will still be retraceable at the moment 
	%    of verifying the condition
	% 2. Var is a local var, then we must compute all the headvar-
	%    datastructures aliased to the topcel of this var 
	%    (note that the aliases to some substructure of this var are
	%     not relevant for the nodes). All the obtained datastructures
	%    are the nodes for our condition. 
	pa_datastruct__init(Var, TopCel),
	(
		list__member(Var, HVs)
	->
		Nodes = [TopCel]
	;
		pa_alias_as__collect_aliases_of_datastruct(ModuleInfo, 
			ProcInfo, TopCel, 
			ALIASi, AliasedData),
		list__filter(
			pred(Data::in) is semidet :-
			  (list__member(Data^sc_var, HVs)),
			AliasedData,
			Nodes)
	),
	(
		Nodes = []
	->
		Condition = always
	;
		set__union(LFUi, LBUi, LUi),
		set__list_to_set(HVs, HVsSet),
			% XXX This is not what the theory sais. LUi should be
			% extended w.r.t. the local aliases, and the resulting
			% set of datastructures projected on the set of
			% headvariables. 
			% XXX Thus: WRONG here!!
		set__intersect(LUi, HVsSet, LUiHVs),
		pa_alias_as__project(HVs, ALIASi, LAiHVs),
		set__list_to_set(Nodes, Nodes_set),
		Condition = condition(Nodes_set, LUiHVs, LAiHVs)
	).

reuse_condition_rename(Dict, MaybeSubst, Cin, Cout) :- 
	(
		Cin = condition(Nodes, LUiH, LAiH)
	->
		% rename the nodes:
		set__to_sorted_list(Nodes, NodesList), 
		list__map(
			pa_datastruct__rename(Dict, MaybeSubst),
			NodesList,
			RenNodesList),
		% rename the datastructures
		set__to_sorted_list(LUiH, ListLUiH),
		list__map(
			map__lookup(Dict), 
			ListLUiH, 	
			ListRenLUiH),
		set__list_to_set(ListRenLUiH, RenLUiH),
		% rename the alias
		pa_alias_as__rename(Dict, MaybeSubst, LAiH, RenLAiH),
		set__list_to_set(RenNodesList, RenNodes),
		Cout = condition(RenNodes, RenLUiH, RenLAiH)
	;
		Cout = Cin
	).

reuse_condition_print(_, _, always) -->
	io__write_string("always").
reuse_condition_print(ProcInfo, PredInfo, condition(Nodes, LUiH, LAiH)) -->
	{ proc_info_varset(ProcInfo, ProgVarSet) }, 
	{ pred_info_typevarset(PredInfo, TypeVarSet) },
	{ set__to_sorted_list(Nodes, NodesList) }, 
	io__write_string("condition("),
		% write out the list of headvar-nodes involved
	io__write_string("["),
	io__write_list(NodesList, ",", 
			print_datastruct(ProgVarSet, TypeVarSet)), 
	io__write_string("], "),	

		% write out LUiH, list of prog_vars
	io__write_string("["),
	{ set__to_sorted_list(LUiH, ListLUiH) },
	mercury_output_vars(ListLUiH, ProgVarSet, bool__no), 
	io__write_string("], "),

		% write out LAiH, the aliases at the reuse-point
	{ from_alias_as_to_aliases_domain(LAiH, PublicLAiH) },
	print_aliases_domain(ProgVarSet, TypeVarSet, no, PublicLAiH),

	io__write_string(")").

reuse_condition_verify(_ProcInfo, _HLDS, _Live0, _Alias0, _Static, always).
reuse_condition_verify(ProcInfo, HLDS,  Live0, Alias0, Static,
		condition(Nodes, LUiH, LAiH)):- 

		% We cannot reuse a variable which was statically
		% constructed.
	list__filter_map(
		(pred(Node::in, Var::out) is semidet :-
			Var = Node^sc_var,
			set__member(Var, Static)
		), set__to_sorted_list(Nodes), []),
	
	pa_alias_as__extend(HLDS, ProcInfo, Alias0, LAiH, Alias),
	pa_alias_as__live(HLDS, ProcInfo, LUiH, Live0, Alias, Live), 
	set__to_sorted_list(Nodes, NodesList), 
	list__filter(
		pred(D::in) is semidet :- 
		    (sr_live__is_live_datastruct(HLDS, ProcInfo, D, Live)),
		NodesList,
		[]).


reuse_condition_update(_ProcInfo, _HLDS, 
		_LFUi, _LBUi, _ALIASi, _HVs, always, always).
reuse_condition_update(ProcInfo, HLDS, LFUi, LBUi, ALIASi, HVs,
		condition(OLD_NODES_set, OLD_LUiH, OLD_LAiH),
		CONDITION):- 
	set__to_sorted_list(OLD_NODES_set, OLD_NODES), 
	list__map(
		pred(TOP::in,LIST::out) is det :- 
			(pa_alias_as__collect_aliases_of_datastruct(HLDS,
				ProcInfo, TOP, 
				ALIASi, LIST)),
		OLD_NODES,
		LISTS_ALL_NEW_NODES),
	list__condense([ OLD_NODES | LISTS_ALL_NEW_NODES], ALL_NEW_NODES),
	list__filter(
		pred(DATA::in) is semidet :-
		  (list__member(DATA^sc_var, HVs)),
		ALL_NEW_NODES,
		NEW_NODES),
	(
		NEW_NODES = []
	->
		CONDITION = always
	;
		% normalize all the datastructs
		list__map(
			pa_datastruct__normalize_wti(HLDS, ProcInfo),
			NEW_NODES,
			NORM_NODES
			),
			% bit strange naming perhaps, but here the
			% OLD_LAiH has the role of `NEW' wrt the extension
			% operation.  
		pa_alias_as__extend(HLDS, ProcInfo, 
					OLD_LAiH, ALIASi, NewALIASi),
		pa_alias_as__project(HVs, NewALIASi, NEW_LAiH0),
			% XXX instmap here simply initialized, as currently
			% it's not used in the normalization anyway.. 	
		instmap__init_reachable(InstMap0), 
		pa_alias_as__normalize(HLDS, ProcInfo, InstMap0, 
				NEW_LAiH0, NEW_LAiH), 

		set__union(LFUi, LBUi, LUi),
		set__union(LUi, OLD_LUiH, NEW_LUi),
		set__list_to_set(HVs, HVsSet),
		set__intersect(NEW_LUi, HVsSet, NEW_LUiH),
		set__list_to_set(NORM_NODES, NORM_NODES_set), 
		CONDITION = condition(NORM_NODES_set, NEW_LUiH, NEW_LAiH)
	).

	% Collect the nodes a reuse-condition is talking about. Fail 
	% if the reuse condition is `always'. 
:- pred reuse_condition_get_nodes(reuse_condition::in, 
			set(prog_data__datastruct)::out) is semidet.
reuse_condition_get_nodes(Condition, Condition ^ nodes). 

	% Collect the nodes a reuse-condition is talking about. Fail 
	% if the reuse condition is `always'. 
:- pred reuse_condition_get_nodes_list(reuse_condition::in, 
			list(prog_data__datastruct)::out) is semidet.
reuse_condition_get_nodes_list(Condition, List):-
	set__to_sorted_list(Condition ^ nodes, List). 

reuse_conditions_simplify(ReuseCondition0, ReuseCondition):- 
	list__foldl( 
		reuse_conditions_simplify_2, 
		ReuseCondition0, 
		[],
		ReuseCondition). 

:- pred reuse_conditions_simplify_2(reuse_condition::in, 
		list(reuse_condition)::in, 
		list(reuse_condition)::out) is det.

reuse_conditions_simplify_2(Condition, Acc0, Acc) :-
	(
		Condition = always
	->
		Acc = Acc0
	;
		list_ho_member(reuse_condition_equal, 
				Condition, 
				Acc0)
	->
		Acc = Acc0
	;
		Acc = [Condition | Acc0]
	).
		

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
memo_reuse_equal(no, no).
memo_reuse_equal(yes(C1), yes(C2)):- 
	list__length(C1, L),
	list__length(C2, L), 
	list__filter(
		pred(COND::in) is semidet :- 
		    (
			(sr_util__list_ho_member(reuse_condition_equal,
					COND, 	
					C1)
			-> 
				fail
			; 
				true
			)
		   ),
		C2, 
		[]).
			
memo_reuse_init(no).
memo_reuse_top(no).

% memo_reuse_rename(ProcInfo, ActualVars, MEMOin, MEMOout):- 
	% proc_info_headvars(ProcInfo, FormalVars),
	% map__from_corresponding_lists(FormalVars, ActualVars, Dict),
	% memo_reuse_rename(Dict, MEMOin, MEMOout).

memo_reuse_rename(Dict, MaybeSubst, Memo0, Memo) :- 
	(
		Memo0 = yes(Cond0)
	->
		list__map(
			reuse_condition_rename(Dict, MaybeSubst), 
			Cond0, 
			Cond),
		Memo = yes(Cond)
	;
		Memo = Memo0
	).

memo_reuse_print(MemoReuse, Name, ProcInfo, PredInfo) --> 
	memo_reuse_print2(MemoReuse, yes(Name), ProcInfo, PredInfo). 

:- pred memo_reuse_print2(memo_reuse::in, maybe(sym_name)::in, 
		proc_info::in, pred_info::in, 
		io__state::di, io__state::uo) is det.
memo_reuse_print2(MemoReuse, MaybeName, ProcInfo, PredInfo) --> 
	( 	
		{ MemoReuse = yes(Cond) }
	->
		io__write_string("yes(["),
		io__write_list(Cond, ",", 
			reuse_condition_print(ProcInfo, PredInfo)),
		io__write_string("]"),
		(
			{ MaybeName = yes(Name) }
		->
			io__write_string(","),
			prog_out__write_quoted_sym_name(Name)
		;
			[]
		),
		io__write_string(")")
	;
		io__write_string("no")
	).

memo_reuse_print_dump(MemoReuse, ProcInfo, PredInfo) --> 
	memo_reuse_print2(MemoReuse, no, ProcInfo, PredInfo). 

memo_reuse_parse(ReuseInformation, ParsedReuse, MaybeReuseName) :- 
	(
		ReuseInformation = term__functor(term__atom("no"), _, _),
		MaybeReuseName = no,
		memo_reuse_init(ParsedReuse)
	;
		ReuseInformation = term__functor(term__atom("yes"),
					ReadConditions, _),
		conditions_list_parse(ReadConditions, Conditions, ReuseName),
		MaybeReuseName = yes(ReuseName),
		ParsedReuse = yes(Conditions)
	).

:- pred conditions_list_parse(list(term(T))::in,
		list(reuse_condition)::out, sym_name::out) is det.

conditions_list_parse(ListTerm, Conds, ReuseName) :- 
	(
		ListTerm = [OneItem, NameTerm]
	->
		condition_rest_parse(OneItem, Conds),
		parse_qualified_term(NameTerm, NameTerm, "pragma reuse",
				Result),
		(Result = ok(ReuseName0, []) ->
			ReuseName = ReuseName0
		;
			error("(sr_data) conditions_list_parse: conditions_list_parse")
		)
	;
		list__length(ListTerm, L), 
		string__int_to_string(L, LS), 
		string__append_list(["(sr_data) conditions_list_parse: ",
				"wrong number of arguments. yes/", LS,
				" should be yes/2"], Msg),
		error(Msg)
	).

:- pred condition_parse(term(T)::in, reuse_condition::out) is det.

condition_parse(Term, Cond) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "condition"	
		->
			(
				Args = [NodesTerm, LUiHTerm, LAiHTerm]
			->
				nodes_parse(NodesTerm, NodesList),
				set__list_to_set(NodesList, Nodes), 
				vars_parse(LUiHTerm, LUiH),
				parse_aliases_domain(LAiHTerm, 	
						LAiH_Domain),
				from_aliases_domain_to_alias_as(LAiH_Domain,
						LAiH),
				Cond = condition(Nodes, LUiH, LAiH)
			;
				list__length(Args, L),
				string__int_to_string(L, LS), 
				string__append_list( 
					[ "(sr_data) condition_parse: ",
					"wrong number of arguments. ",
					"condition/",LS, " should be ",
					"condition/3"], Msg),
				error(Msg)
			)
		;
			term__det_term_to_type(Term, Type),
			varset__init(V), 
			StringTerm = mercury_type_to_string(V, Type),
			string__append_list( 
				["(sr_data) condition_parse: ",
				"wrong constructur. `", 
				StringTerm, 
				"' should be `condition'"], Msg),
			error(Msg)
		)
	;
		error("(sr_data) condition_parse: term is not a functor")
	).

:- pred nodes_parse(term(T)::in, list(prog_data__datastruct)::out) is det.

nodes_parse(Term, Datastructs) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [First, Rest]
		->
			parse_datastruct(First, D1),
			nodes_parse(Rest, D2),
			Datastructs = [D1 | D2]
		;
			Cons = "[]"
		->
			Datastructs = []
		;
			string__append("(sr_data) nodes_parse: could not parse nodes, top cons: ", Cons, Msg),
			error(Msg)
		)
	;
		error("(sr_data) nodes_parse: term not a functor")
	).

:- pred vars_parse(term(T)::in, set(prog_var)::out) is det.

vars_parse(Term, Vars) :- 
	vars_parse_list(Term, VarList) , 
	set__list_to_set(VarList, Vars).

:- pred vars_parse_list(term(T)::in, list(prog_var)::out) is det.

vars_parse_list(Term, Vars) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [First, Rest]
		->
			( 
				First = term__variable(V)
			->
				V1 = V
			;
				error("(sr_data) vars_parse_list: list should contain variables.")
			),	
			term__coerce_var(V1, ProgVar),
			vars_parse_list(Rest, V2),
			Vars = [ProgVar | V2]
		;
			Cons = "[]"
		->
			Vars = []
		;
			string__append("(sr_data) vars_parse_list: could not parse nodes, top cons: ", Cons, Msg),
			error(Msg)
		)
	;
		error("(sr_data) vars_parse_list: term not a functor")
	).


:- pred condition_rest_parse(term(T)::in, list(reuse_condition)::out) is det.

condition_rest_parse(Term, Conds) :- 
	(
		Term = term__functor(term__atom(Cons), Args, _)
	->
		(
			Cons = "[|]",
			Args = [First, Rest]
		->
			condition_parse(First, Cond1),
			condition_rest_parse(Rest, Cond2),
			Conds = [Cond1 | Cond2]
		;
			Cons = "[]"
		->
			Conds = []
		;
			string__append("(sr_data) condition_rest_parse: could not parse conditions, top cons: ", Cons, Msg),
			error(Msg)
		)
	;
		error("(sr_data) condition_rest_parse: term not a functor")
	).

memo_reuse_verify_reuse(ProcInfo, HLDS, Memo, Live0, Alias0, Static) :-
	Memo = yes(Conditions), 
	list__takewhile(reuse_condition_verify(ProcInfo, HLDS, 
						Live0, Alias0, Static), 
				Conditions, _, []), 
	% Next to verifying each condition separately, one has to
	% verify whether the nodes which are reused in each of the
	% conditions are not aliased within the current context. If
	% this would be the case, then reuse is not allowed. If
	% this would be allowed, then the callee want to reuse
	% the different parts of the input while these may point
	% to exactly the same structure, resulting in undefined
	% behaviour. 
	no_aliases_between_reuse_nodes(HLDS, ProcInfo, Conditions, 
				Alias0 ). 

:- pred no_aliases_between_reuse_nodes(
		module_info::in, 
		proc_info::in, 
		list(reuse_condition)::in, 
		alias_as::in) is semidet.
no_aliases_between_reuse_nodes(ModuleInfo, ProcInfo, 
		Conditions, Alias):- 
	list__filter_map(
		reuse_condition_get_nodes_list,
		Conditions, 
		ListNodes), 
	list__condense(ListNodes, AllNodes), 
	(
		AllNodes = [Node | Rest] 
	-> 
		no_aliases_between_reuse_nodes_2(ModuleInfo, ProcInfo, 
					Node, Rest, Alias)
	;
		require__error("(sr_data): no_aliases_between_reuse_nodes has no nodes.")
	).

:- pred no_aliases_between_reuse_nodes_2(module_info::in, proc_info::in,
		prog_data__datastruct::in, 
		list(prog_data__datastruct)::in, 
		alias_as::in) is semidet. 
no_aliases_between_reuse_nodes_2(ModuleInfo, ProcInfo, Node, OtherNodes, 
		Alias):- 
	pa_alias_as__collect_aliases_of_datastruct(ModuleInfo, ProcInfo, 
		Node, Alias, AliasedNodes), 
	% Check whether none of the structures to which the current
	% Node is aliased is subsumed by or subsumes one of 
	% the other nodes, including the current node itself. 
	list__filter(
		there_is_a_subsumption_relation(ModuleInfo, ProcInfo, 
			[Node | OtherNodes]), 
		AliasedNodes, 
		[]), 
	(
		OtherNodes = [NextNode | NextOtherNodes],
		no_aliases_between_reuse_nodes_2(ModuleInfo, ProcInfo, 
			NextNode, NextOtherNodes, Alias)
	; 
		OtherNodes = [], 
		true
	).

	% there_is_a_subsumption_relation(ModuleInfo, ProcInfo, Datastructs, 
	% Data): This procedure succeeds if Data is subsumed or subsumes
	% some of the datastructures in Datastructs. 
:- pred there_is_a_subsumption_relation(module_info::in, proc_info::in, 
		list(prog_data__datastruct)::in, 
		prog_data__datastruct::in) is semidet.
there_is_a_subsumption_relation(ModuleInfo, ProcInfo, 
		Datastructs0, Data0):-
	list__filter(
		pred(Data1::in) is semidet:-
		    (
			( pa_datastruct__less_or_equal(ModuleInfo, ProcInfo, 
				Data0, Data1, _) ; 
			  pa_datastruct__less_or_equal(ModuleInfo, ProcInfo, 
				Data1, Data0, _)
			)
		     ), 
		Datastructs0, 
		SubsumedStructs), 
	SubsumedStructs \= []. 

		
memo_reuse_is_conditional(yes([_|_])).
memo_reuse_is_unconditional(yes([])).

memo_reuse_simplify(M0, M):-
	(
		M0 = yes(Conditions0)
	->
		reuse_conditions_simplify(Conditions0, Conditions),
		M = yes(Conditions)
	;
		M = M0
	).

memo_reuse_merge(M1, M2, M) :-
	(
		M1 = yes(L1)
	->
		(
			M2 = yes(L2)
		->
			list__append(L1, L2, L),
			M0 = yes(L)
		;
			M0 = M1
		)
	;
		M0 = M2
	),
	memo_reuse_simplify(M0, M).

