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
:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_alias_as.
:- import_module structure_reuse__sr_live.

:- import_module bool, map, set, std_util, list, io, term.

%-----------------------------------------------------------------------------%
:- type program_point 
	---> 	pp( 
			pp_context	:: term__context, 
			pp_path		:: goal_path
		).
:- pred program_point_init(hlds_goal_info::in, program_point::out) is det.

:- type dead_cell_table == map(program_point, reuse_condition).
:- func dead_cell_table_init = dead_cell_table. 
:- func dead_cell_table_search(program_point, dead_cell_table) 
		= reuse_condition is semidet.
:- pred dead_cell_table_set(program_point::in, reuse_condition::in, 
		dead_cell_table::in, dead_cell_table::out) is det.
:- pred dead_cell_table_remove(program_point::in, 
		dead_cell_table::in, dead_cell_table::out) is det.
:- pred dead_cell_table_remove_conditionals(dead_cell_table::in, 
		dead_cell_table::out) is det. 
:- pred dead_cell_table_dump(dead_cell_table::in, 
		io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%

:- type memo_reuse == maybe(list(reuse_condition)).

:- type reuse_condition_table == 
		map(pred_proc_id, maybe(list(reuse_condition))). 
:- func reuse_condition_table_init = reuse_condition_table.
:- func reuse_condition_table_search(pred_proc_id, reuse_condition_table) 
		= maybe(list(reuse_condition)) is semidet.
:- pred reuse_condition_table_set(pred_proc_id::in, 
		maybe(list(reuse_condition))::in, 
		reuse_condition_table::in, reuse_condition_table::out) is det.

%-----------------------------------------------------------------------------%
	% Conversion between public/private reuse condition types. 
:- pred from_reuse_condition_to_reuse_tuple(reuse_condition::in, 
		reuse_tuple::out) is det.
:- pred from_reuse_tuple_to_reuse_condition(reuse_tuple::in, 
		reuse_condition::out) is det.
:- pred from_memo_reuse_to_maybe_reuse_typles(memo_reuse::in, 
		maybe_reuse_tuples::out) is det.
:- pred from_maybe_reuse_tuples_to_memo_reuse(maybe_reuse_tuples::in, 
		memo_reuse::out) is det.
%-----------------------------------------------------------------------------%

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
		   nodes 		:: set(datastruct),
		   	% A description of the node that is reused if the
			% reuse is allowed. Given the existence of possible
			% aliases, the single node may be translated into a set
			% of nodes. 
		   local_use_headvars 	:: set(datastruct),
		   	% A description of the nodes that are inherently live
			% at the site of the last deconstruction of the
			% structure to be reused.
		   local_alias_headvars :: alias_as 
		   	% A description of the existing aliases at the site of
			% the last deconstruction of the structure to be
			% reused. 
		).



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
			alias_as::in, 
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

:- import_module list, string, require, varset, bool, assoc_list.
%-----------------------------------------------------------------------------%
program_point_init(Info, PP) :- 
	goal_info_get_context(Info, Context), 
	goal_info_get_goal_path(Info, GoalPath), 
	PP = pp(Context, GoalPath). 

dead_cell_table_init = map__init.
dead_cell_table_search(PP, Table) = Table ^ elem(PP). 
dead_cell_table_set(PP, RC, Table0, Table) :- 
	map__set(Table0, PP, RC, Table). 
dead_cell_table_remove(PP, !Table) :- 
	map__det_remove(!.Table, PP, _, !:Table). 
dead_cell_table_remove_conditionals(!Table) :- 
	map__foldl(dead_cell_table_add_unconditional, !.Table, 
		dead_cell_table_init, !:Table). 

:- pred dead_cell_table_add_unconditional(program_point::in, 
		reuse_condition::in, dead_cell_table::in, 
		dead_cell_table::out) is det.
dead_cell_table_add_unconditional(PP, C, !Table) :- 
	(
		C = always
	-> 
		dead_cell_table_set(PP, C, !Table)
	;
		true
	).

dead_cell_table_dump(Table, !IO) :- 
	io__write_string("\t\t|--------|\n", !IO),
	map__foldl(dead_cell_entry_dump, Table, !IO),
	io__write_string("\t\t|--------|\n", !IO).

:- pred dead_cell_entry_dump(program_point::in, reuse_condition::in, 
		io__state::di, io__state::uo) is det.
dead_cell_entry_dump(_PP, Cond, !IO) :- 
	Cond = always, 
	io__write_string("\t\t| always |\n", !IO). 
dead_cell_entry_dump(_PP, Cond, !IO) :- 
	Cond = condition(_, _, _), 
	io__write_string("\t\t|  cond  |\n", !IO). 
	

%-----------------------------------------------------------------------------%
reuse_condition_table_init = map__init. 
reuse_condition_table_search(PredProcId, Table) = Table ^ elem(PredProcId). 
reuse_condition_table_set(PredProcId, Conds, Table0, Table) :- 
	map__set(Table0, PredProcId, Conds, Table). 
%-----------------------------------------------------------------------------%

from_reuse_condition_to_reuse_tuple(Condition, Tuple) :- 
	(
		Condition = always,
		Tuple = unconditional
	;
		Condition = condition(Nodes, LocalUseData, AliasAs), 
		from_alias_as_to_aliases_domain(AliasAs, AliasesDomain), 
		Tuple = conditional(Nodes, LocalUseData, AliasesDomain)
	).
from_reuse_tuple_to_reuse_condition(Tuple, Condition) :- 
	(
		Tuple = unconditional,
		Condition = always
	;
		Tuple = conditional(Nodes, LocalUseData, AliasesDomain),
		from_aliases_domain_to_alias_as(AliasesDomain, AliasAs),
		Condition = condition(Nodes, LocalUseData, AliasAs)
	).
from_memo_reuse_to_maybe_reuse_typles(no, no). 
from_memo_reuse_to_maybe_reuse_typles(yes(Conditions), yes(Tuples)):-
	list__map(from_reuse_condition_to_reuse_tuple, 
		Conditions, Tuples).
from_maybe_reuse_tuples_to_memo_reuse(no, no). 
from_maybe_reuse_tuples_to_memo_reuse(yes(Tuples), yes(Conditions)):-
	list__map(from_reuse_tuple_to_reuse_condition,
		Tuples, Conditions). 
%-----------------------------------------------------------------------------%
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
		Var, LFUi, LBUi, ALIASi, Condition):- 
	proc_info_headvars(ProcInfo, HVs), 
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
		LUiHVsData = set__map(pa_datastruct__init, LUiHVs),
		pa_alias_as__project(HVs, ALIASi, LAiHVs),
		set__list_to_set(Nodes, Nodes_set),
		Condition = condition(Nodes_set, LUiHVsData, LAiHVs)
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
		set__list_to_set(RenNodesList, RenNodes),
		% rename the datastructures in use: 
		set__to_sorted_list(LUiH, ListLUiH),
		list__map(
			pa_datastruct__rename(Dict, MaybeSubst),
			ListLUiH, 	
			ListRenLUiH),
		set__list_to_set(ListRenLUiH, RenLUiH),
		% rename the alias
		pa_alias_as__rename(Dict, MaybeSubst, LAiH, RenLAiH),
		Cout = condition(RenNodes, RenLUiH, RenLAiH)
	;
		Cout = Cin
	).

reuse_condition_print(ProcInfo, PredInfo, Condition, !IO) :- 
	proc_info_varset(ProcInfo, ProgVarSet), 
	pred_info_typevarset(PredInfo, TypeVarSet),
	from_reuse_condition_to_reuse_tuple(Condition, Tuple), 
	print_reuse_tuple(ProgVarSet, TypeVarSet, Tuple, !IO). 

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

		% collect the datastructs in use part of the reuse condition: 
		% 1. collect all the in use information (as datastructs!);
		% 2. extend wrt the local aliases;
		% 3. project on the headvars;
		set__union(LFUi, LBUi, LUi),
		LUi_data = set__map(pa_datastruct__init, LUi), 
		set__union(LUi_data, OLD_LUiH, NEW_LUi_data),
		set__to_sorted_list(NEW_LUi_data, NEW_LUi_data_list), 
		list__map(
		    pred(TopCell::in, AliasedCells::out) is det :- 
			(pa_alias_as__collect_aliases_of_datastruct(HLDS, 
			    ProcInfo, TopCell, NewALIASi, AliasedCells)),
		    NEW_LUi_data_list, ListAliasedCells), 
		list__condense([NEW_LUi_data_list | ListAliasedCells], 
			Extended_LUi_list),
		list__filter(
			pred(Data::in) is semidet :- 
				(list__member(Data^sc_var, HVs)),
			Extended_LUi_list, Extended_LUiHvs_list),
		set__list_to_set(Extended_LUiHvs_list, NEW_LUiH),

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
		% Remove all the occurrences of Condition in Acc0, and then add
		% the Condition back to the list. 
		list__filter(reuse_condition_equal(Condition), Acc0, _, Acc1),
		Acc = [Condition | Acc1]
	).
		

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
memo_reuse_equal(no, no).
memo_reuse_equal(yes(C1), yes(C2)):- 
	list__length(C1, L),
	list__length(C2, L), 
	list__foldl(
		pred(Cond::in, Conditions0::in, Conditions::out) is det :- 
		    (
		    	% remove all the occurrences of Cond from the
			% accumulator. 
		    	list__filter(reuse_condition_equal(Cond), 
				Conditions0, _, Conditions)
		   ),
		C1, C2, Result), 
	Result = []. 
			
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
memo_reuse_print2(MemoReuse, MaybeName, ProcInfo, PredInfo, !IO) :-
	proc_info_varset(ProcInfo, ProgVarSet), 
	pred_info_typevarset(PredInfo, TypeVarSet),
	from_memo_reuse_to_maybe_reuse_typles(MemoReuse, MaybeReuseTuples), 
	print_maybe_reuse_tuples(ProgVarSet, TypeVarSet, MaybeReuseTuples, 
		MaybeName, !IO). 

memo_reuse_print_dump(MemoReuse, ProcInfo, PredInfo) --> 
	memo_reuse_print2(MemoReuse, no, ProcInfo, PredInfo). 

memo_reuse_parse(ReuseInformation, ParsedReuse, MaybeReuseName) :- 
	parse_maybe_reuse_tuples(ReuseInformation, MaybeReuseTuples, 
		MaybeReuseName), 
	from_maybe_reuse_tuples_to_memo_reuse(MaybeReuseTuples, ParsedReuse).

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

