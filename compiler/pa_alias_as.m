%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias_as: This module defines the type "alias_as" and its
% operations. This type is used to represent the possible aliases information
% during the possible alias-analysis and structure reuse analysis. 

% main author: nancy

:- module possible_alias__pa_alias_as.

:- interface.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module hlds__instmap.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_datastruct.
	% XXX sr_live dependency should be removed. 
:- import_module structure_reuse__sr_live.

:- import_module set, list, map, string, int, varset.
:- import_module io, term, std_util, bool.

%-----------------------------------------------------------------------------%

:- type alias_as_table == map(pred_proc_id, alias_as).
:- func alias_as_table_init = alias_as_table. 
:- func alias_as_table_init(list(pred_proc_id)) = alias_as_table.
:- func alias_as_table_search_alias(pred_proc_id, alias_as_table) 
		= alias_as is semidet.
:- pred alias_as_table_set_alias(pred_proc_id::in, alias_as::in, 
		alias_as_table::in, alias_as_table::out) is det.

%-----------------------------------------------------------------------------%

:- type alias_as.

:- pred init(alias_as::out) is det.
:- func init = alias_as.
:- pred is_bottom(alias_as::in) is semidet.

:- pred top(string::in, alias_as::out) is det.

	% top(String, AliasIn, AliasOut). 
	% Set the current alias to be Top. If the current alias is already
	% top, add the string to the list of strings explaining that top. 
:- pred top(string::in, alias_as::in, alias_as::out) is det.
:- pred is_top(alias_as::in) is semidet.

	% Compute the size of the set of pairs of aliased data structures as
	% described by the alias description. 
:- func size(alias_as) = int.

	% project(Vars, AliasIn, AliasOut). 
	% Reduce the alias information to the alias information concerning
	% a given list of variables only. This operation is generally known
	% as projection. 
	% We have: vars(AliasOut) \subseteq Vars
	%          vars(AliasIn - AliasOut) \cap Vars = \emptyset
:- pred project(list(prog_var)::in, alias_as::in, alias_as::out) is det.

	% The same as project, yet here using a set of program variables
	% instead of a list of program variables. 
:- pred project_set(set(prog_var)::in, alias_as::in, alias_as::out) is det.

	% Project a set of aliases to aliases relating to variables that are
	% either in forward use (LFU), backward use (LBU) or that are head
	% variables of the procedure. This projection is useful to downsize the
	% set of aliases to the relevant set only. 
	% Used in pa_run, and sr_indirect. 
	% XXX Does the use of this procedure really guarantee correctness of
	% the results? And how much analysis-time does it save?
:- pred project_on_live_vars(proc_info::in, hlds_goal_info::in, 
		alias_as::in, alias_as::out) is det.

	% Extend the current data structure to the full set of data
	% structures referring to the same memory space. 
	% This corresponds to the "extend" operation used in Nancy's Phd. 
	% The operation produces a software error when called with
	% a top alias description. 
:- pred collect_aliases_of_datastruct(module_info::in, proc_info::in, 
		prog_data__datastruct::in, alias_as::in, 
		list(prog_data__datastruct)::out) is det.

	% If AliasIn is the exit description stored for a particular
	% procedure definition (identified by its pred_proc_id, Id), then
	% rename_call_alias(Id, Module, ActualArgs, ActualTypes, AliasIn,
	% AliasOut) is defined such that AliasOut is the renaming of
	% AliasIn from the formal args and types (that can be known using the
	% pred_proc_id from the procedure) to the actual args and types
	% (given as arguments). 
	% Typical call: 
	%	rename_call_alias(PredProcId, ModuleInfo, ActualVars, 
	% 	ActualTypes, FormalAlias, ActualAlias). 
:- pred rename_call_alias(pred_proc_id::in, module_info::in, 
		list(prog_var)::in, list((type))::in, 
		alias_as::in, alias_as::out) is det.

:- func to_type_renaming(list((type)), list((type))) = 
		substitution(tvar_type).

	% Rename the abstract description according to the renaming
	% mapping of prog_vars (which maps FROM_VARS to the TO_VARS). 
:- pred rename(map(prog_var, prog_var)::in, maybe(substitution(tvar_type))::in,
		alias_as::in, alias_as::out) is det.

	% The call equal(Alias1,Alias2) succeeds if both abstract
	% descriptions are equal (i.e. Alias1 subsumes Alias2, and vice
	% versa). 
	% XXX Ideally, equal should be defined as A1 <= A2, and A2 <= A1 (where
	% "<=" means "less or equal"). This is currently not the case. Replace,
	% and check whether the same results are still obtained. 
	% This means that the implementation of the procedures "equal",
	% "less_or_equal" and "least_upper_bound" need to be checked. The
	% central operation should be "less_or_equal". In the current
	% implementation, less_or_equal relies on "least_upper_bound" and
	% "equal". 
:- pred equal(alias_as::in, alias_as::in) is semidet.

	% less_or_equal(ModuleInfo, ProcInfo, AliasAs1, AliasAs2). 
	% The first description AliasAs1 describes a smaller set of aliases
	% than the second description, i.e. AliasAs2. This means that for each 
	% alias Alias1 subsumed by AliasAs1, there exists an alias
	% Alias2 from AliasAs2 such that Alias1 is also described by
	% Alias2. In the same time, for each Alias2 described by AliasAs2,
	% there should be an Alias1 in AliasAs1 such that Alias1 is subsumed by
	% Alias2. 
	% This operation is essential for the fixpoint-computation process. 
	%
	% XXX It seems that less_or_equal is defined in terms of the least
	% upper bound and the equality property. Thus: 
	% 	A1 <= A2 iff A1 \cup A2 = A2
	% XXX Why is a module_info and proc_info needed? Apparently this is
	% needed to compute the least-upper-bound. To be checked more
	% thoroughly. 
:- pred less_or_equal(module_info::in, proc_info::in, alias_as::in,
		alias_as::in) is semidet.

	% Compute the least upper bound of two given alias descriptions.
:- pred least_upper_bound(module_info::in, proc_info::in,
		alias_as::in, alias_as::in, alias_as::out) is det.

	% Compute least upper bound of a list of abstract alias descriptions.
:- pred least_upper_bound_list(module_info::in, proc_info::in, 
		hlds_goal_info::in, list(alias_as)::in, alias_as::out) is det.

	% extend(ProcInfo, ModuleInfo, NEW, OLD, RESULT).
	% This is the "comb" operation used in the Nancy's Phd-textbook. It is
	% used to combine a given new alias description to an existing old
	% alias description. This operation is not commutative! Therefore, the
	% order of the arguments is crucial. 
:- pred extend(module_info::in, proc_info::in, alias_as::in, 
		alias_as::in, alias_as::out) is det.

	% Specialized extend for unifications. This corresponds to the "add"
	% operation used in Nancy's Phd-textbook. 
:- pred extend_unification(module_info::in, proc_info::in, pred_info::in,
		hlds_goal__unification::in, hlds_goal__hlds_goal_info::in, 
		alias_as::in, alias_as::out, 
		io__state::di, io__state::uo) is det.
:- pred extend_unification(module_info::in, proc_info::in, 
		hlds_goal__unification::in, hlds_goal__hlds_goal_info::in, 
		alias_as::in, alias_as::out) is det.

	% Specialized extend for foreign code. If considering foreign code as a
	% special case of "builtin" and thus primitive operations, this can be
	% seen as another case of the "add" operation as used in Nancy's Phd. 
:- pred extend_foreign_code(module_info::in, proc_info::in,
		pragma_foreign_proc_attributes::in, pred_id::in, proc_id::in, 
		list(prog_var)::in, list(maybe(pair(string, mode)))::in,
                list(type)::in, hlds_goal_info::in, 
		alias_as::in, alias_as::out) is det.

	% Compute the union of two abstract descriptions, yet, without
	% combining them (no alternating closure). This operation is
	% commutative. 
	% XXX What makes this operation different from the least_upper_bound
	% operation? Where is it used? Only in sr_data for merging reuse
	% conditions. This seems odd. 
:- pred add(alias_as, alias_as, alias_as).
:- mode add(in, in, out) is det.

	% Simplify the representation of the aliases by normalizing
	% the selectors used in these aliases. During the analysis,
	% we apparently do not normalize the aliases at each step,
	% and only enforce it on demand. 
	% The normalisation is based on the type information (retreivable from
	% the proc_info and module_info) and on the instantation mapping of the
	% variables (?). 
	% XXX The instmap is clearly not used. What was the initial idea of
	% passing the instmap? To be checked.
	% XXX This operation should eventually be dropped altogether. We should
	% try to keep a compact representation all the time. But this may mean
	% that the module_info needs to be passed around for each update of the
	% alias_sets... hmmm, needs some more thinking. 
:- pred normalize(module_info::in, proc_info::in, instmap::in, 
		alias_as::in, alias_as::out) is det.
:- pred normalize(module_info::in, proc_info::in, 
		alias_as::in, alias_as::out) is det.

%-----------------------------------------------------------------------------%
% Computing the live data structure set using alias information. 
% XXX This procedure should go into sr_live by providing a routine to convert
% alias_as types to lists of pairs of data structures. 
%-----------------------------------------------------------------------------%

	% live(ModuleInfo, ProcInfo, InUse, Live0, Alias, Live). 
	% Compute the (sr_live__)live-set Live based on an initial InUse set, 
	% an initial Live0 set, and a list of aliases Alias.
:- pred live(module_info::in, proc_info::in, 
		set(prog_var)::in, live_set::in, alias_as::in,
		sr_live__live_set::out) is det.
	
% :- func live(module_info, proc_info, 
% 		set(prog_var),live_set, alias_as) = sr_live__live_set.
% :- mode live(in, in, in,in, in) = out is det.

%-----------------------------------------------------------------------------%
% Widening of the alias description. 
% Cf. Type-Widening as described in Nancy's Phd Textbook. 
%-----------------------------------------------------------------------------%

	% Apply widening on an alias description if the 'size' of the set of
	% aliases it describes is larger than the threshold expressed by the
	% integer-argument. The boolean is set to "yes" if widening was indeed
	% applied. 
:- pred apply_widening(module_info::in, proc_info::in, int::in, 
		alias_as::in, alias_as::out, bool::out) is det. 

%-----------------------------------------------------------------------------%
	% predict_bottom_alias(ModuleInfo, HeadVars, Modes, Types) checks
	% whether the aliases produced by a procedure with the given
	% headvariables, modes and types can correctly be approximated by the 
	% bottom-alias element, simply by looking at the modes and types. 
	% It fails if the alias can not be shown to be bottom in this way. 
:- pred predict_bottom_alias(module_info::in, list(prog_var)::in, 
		list(mode)::in, list(type)::in) is semidet.

%-----------------------------------------------------------------------------%
:- pred from_aliases_domain_to_alias_as(aliases_domain::in, 
		alias_as::out) is det.
:- pred from_alias_as_to_aliases_domain(alias_as::in, 
		aliases_domain::out) is det.
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- implementation.

:- include_module pa_alias_set.
:- import_module check_hlds__inst_match.
:- import_module check_hlds__mode_util.
:- import_module check_hlds__type_util.
:- import_module hlds__hlds_llds.
:- import_module parse_tree__mercury_to_mercury.
:- import_module parse_tree__prog_io_pasr.
:- import_module possible_alias__pa_alias.
:- import_module possible_alias__pa_alias_as__pa_alias_set.
:- import_module possible_alias__pa_selector. 
:- import_module possible_alias__pa_sr_util.
:- import_module possible_alias__pa_util.

:- import_module require, term, assoc_list.
:- import_module std_util.


%-----------------------------------------------------------------------------%
alias_as_table_init = map__init. 
alias_as_table_init(Ids) = list__foldl(
		func(Id, T0) = T :-
		    (
		        alias_as_table_set_alias(Id, pa_alias_as__init,
				T0, T)
		    ),
		Ids, 
		alias_as_table_init).
alias_as_table_search_alias(PredProcId, Table) = Alias :- 
	Table^elem(PredProcId) = Alias.
alias_as_table_set_alias(PredProcId, Alias, Table0, Table) :- 
	Table = Table0^elem(PredProcId) := Alias.


%-----------------------------------------------------------------------------%
:- type alias_as ---> 
			real_as(alias_set)
		;	bottom
		; 	top(list(string)).
	% where list(alias) contains no doubles!
	% near future: alias_as should also include top(string),
	% where string could be some sort of message.

% constants
:- func alias_limit = int. 
:- func top_limit = int. 

alias_limit = 500000. % 100
top_limit = 200000.

%-----------------------------------------------------------------------------%

	% init
init(bottom).
init = B :- init(B).

	% is_bottom
is_bottom(bottom).
is_bottom(real_as(AliasSet)):- is_empty(AliasSet).

	% top
top(Msg, top([NewMsg])):- 
	% string__append_list(["- ",Msg," -"],NewMsg).
	NewMsg = Msg.

top(Msg, Alias, top(Msgs)):-
	(
		Alias = top(FirstMsgs)
	->
		Msgs = [Msg|FirstMsgs]
	;
		Msgs = [Msg]
	).

:- pred top_merge(alias_as::in, alias_as::in, alias_as::out) is det.
top_merge(A0, A1, A) :- 
	(
		A0 = top(Msgs0),
		A1 = top(Msgs1)
	->
		list__append(Msgs0, Msgs1, MsgsDups),
		list__remove_dups(MsgsDups, Msgs),
		A = top(Msgs)
	;
		require__error("(pa_alias_as) top_merge: aliases ought to be
both top.")
	).

	% is_top
is_top(top(_)).

size(bottom) = 0.
size(top(_)) = 9999999.
size(real_as(AliasSet)) = size(AliasSet). 

	% project
project(Listvar, ASin , ASout):-
	(
		ASin = real_as(AliasSet0)
	->
		project(Listvar, AliasSet0, AliasSet), 
		wrap(AliasSet, ASout)
	;
		% ASin is bottom or top(_)
		ASout = ASin
	).

project_set(SetVar, ASin, ASout):-
	set__to_sorted_list(SetVar, ListVar),
	project(ListVar, ASin, ASout).

project_on_live_vars(ProcInfo, GoalInfo, Alias0, Alias):- 
	goal_info_get_lfu(GoalInfo, LFUi), 
	goal_info_get_lbu(GoalInfo, LBUi), 
	proc_info_headvars(ProcInfo, ListHeadVars), 
	set__list_to_set(ListHeadVars, HeadVars),
        set__union(LFUi, LBUi, IN_USEi),
        set__union(IN_USEi, HeadVars, AliveVars),
	project_set(AliveVars, Alias0, Alias). 

	

collect_aliases_of_datastruct(ModuleInfo, ProcInfo, Datastruct, AS, 
				AliasList):-
	(
		AS = real_as(AliasSet)
	->
		collect_aliases_of_datastruct(ModuleInfo, 
			ProcInfo, Datastruct, AliasSet, AliasList)
	;
		is_bottom(AS)
	->
		AliasList = []
	;
		% is_top
		error("(pa_alias_as) collect_aliases_of_datastruct: alias_as is top.")
	).
	
		
rename_call_alias(PredProcId, ModuleInfo, ActualVars, ActualTypes,
		FormalAlias, ActualAlias):- 
	module_info_pred_proc_info(ModuleInfo, PredProcId, PredInfo,
			ProcInfo),
	pred_info_arg_types(PredInfo, FormalTypes), 
	proc_info_headvars(ProcInfo, FormalVars),
	map__from_corresponding_lists(FormalVars, ActualVars, Dict), 
	pa_alias_as__rename(Dict, 
		yes(to_type_renaming(FormalTypes, ActualTypes)), 
		FormalAlias, ActualAlias).

to_type_renaming(FromTypes, ToTypes) = Substitution :- 
	assoc_list__from_corresponding_lists(FromTypes, 
		ToTypes, FromToTypes), 
	list__foldl(
		(pred(P::in, S0::in, S::out) is det :- 
			P = F - T, 
			( 
			 	term__unify(F, T, S0, S1) 
			-> 	S = S1
			; 	S = S0
		)), FromToTypes, map__init, Substitution).

rename(_, _, top(M), top(M)). 
rename(_, _, bottom, bottom). 
rename(MapVar, MaybeTypeSubst, real_as(Aliases0), real_as(Aliases)):- 
	pa_alias_set__rename(MapVar, MaybeTypeSubst, Aliases0, Aliases).

equal(AS1, AS2):-
	(
		AS1 = real_as(AliasSet1),
		AS2 = real_as(AliasSet2), 
		equal(AliasSet1, AliasSet2)
	;
		% AS1 is bottom or top(_)
		(AS1 = bottom, AS2 = bottom)
		;
		(is_top(AS1), is_top(AS2))
	).

less_or_equal(ModuleInfo, ProcInfo, AS1, AS2):-
	% XXX This could should be equivalent to: 
	% 	least_upper_bound(ModuleInfo, ProcInfo, AS1, AS2, AS), 
	% 	equal(AS, AS2).
	% To be checked. 
	(
		AS1 = real_as(AliasSet1),
		AS2 = real_as(AliasSet2),
		less_or_equal(ModuleInfo, ProcInfo, 
				AliasSet1, AliasSet2) 
	;
		(AS1 = bottom ; AS2 = top(_))
	).

least_upper_bound(HLDS, ProcInfo, AS1, AS2, RESULT) :-
	(
		AS1 = real_as(AliasSet1)
	->
		(
			AS2 = real_as(AliasSet2)
		->
			least_upper_bound(HLDS, ProcInfo, 
				AliasSet1, AliasSet2, AliasSet), 
			wrap_and_control(HLDS, ProcInfo, AliasSet, RESULT)
		;
			AS2 = top(_)
		->
			RESULT = AS2
		;
			% AS2 = bottom
			RESULT = AS1
		)
	;
		AS1 = top(_)
	->
		(
			AS2 = top(_)
		->
			top_merge(AS1, AS2, RESULT)
		;
			RESULT = AS1
		)
	;
		% AS1 = bottom
		RESULT = AS2
	).

least_upper_bound_list(HLDS, ProcInfo, _GoalInfo, Alias_list0, AS) :-
	list__foldl(least_upper_bound(HLDS, ProcInfo) , Alias_list0, 
			bottom, AS).

extend(HLDS, ProcInfo, A1, A2, RESULT):-
	(
		A1 = real_as(NEW)
	->
		(
			A2 = real_as(OLD)
		->
			extend(HLDS, ProcInfo, 
				NEW, OLD, Aliases),
			wrap_and_control(HLDS, ProcInfo, Aliases, RESULT)
		;
			A2 = top(_)
		->
			RESULT = A2
		;
			% A2 = bottom
			RESULT = A1
		)
	;
		A1 = top(_)
	->
		(
			A2 = top(_)
		->
			RESULT = A2 	% if the old alias was already
					% top, keep the old one.
		; 		
			RESULT = A1 	
		)
	; 
		% A1 = bottom
		RESULT = A2	
	).

add(AS1, AS2, AS) :- 
	(
		AS1 = real_as(AliasSet1)
	->
		(
			AS2 = real_as(AliasSet2)
		->
			add(AliasSet1, AliasSet2, AliasSet), 
			AS = real_as(AliasSet)
		;
			AS2 = bottom
		->
			AS = AS1
		;
			AS = AS2
		)
	;
		AS1 = bottom
	->
		AS = AS2
	;
		% AS1 = top 
		AS = AS1
	).
	

%-----------------------------------------------------------------------------%
extend_unification(HLDS, ProcInfo, Unif, GoalInfo, !AS) :- 
	pa_alias__from_unification(HLDS, ProcInfo, Unif, GoalInfo, AUnif),
	from_pair_alias_list(AUnif, AliasSetUnif), 
	wrap(AliasSetUnif, ASUnif0),
		% pa_alias__from_unification does not ensure that the created
		% aliases are normalized, hence this must be explicitly done: 
	normalize_wti(HLDS, ProcInfo, ASUnif0, ASUnif),
	extend(HLDS, ProcInfo, ASUnif, !AS), 
	(
		Unif = construct(_, _, _, _, _, _, _)
	-> 
		optimization_remove_deaths(ProcInfo, GoalInfo, !AS)
	;
		true
	).

extend_unification(HLDS, ProcInfo, _PredInfo, Unif, GoalInfo, !AS, !IO) :-
	pa_alias__from_unification(HLDS, ProcInfo, Unif, GoalInfo, AUnif),
	from_pair_alias_list(AUnif, AliasSetUnif),
	wrap(AliasSetUnif, ASUnif0),
		% pa_alias__from_unification does not ensure that the created
		% aliases are normalized, hence this must be explicitly done: 
	normalize_wti(HLDS, ProcInfo, ASUnif0, ASUnif),
	extend(HLDS, ProcInfo, ASUnif, !AS),
	(
		Unif = construct(_, _, _, _, _, _, _)
	-> 
		optimization_remove_deaths(ProcInfo, GoalInfo, !AS) 
	;
		true
	).


:- pred optimization_remove_deaths(proc_info::in, hlds_goal_info::in, 
			alias_as::in, alias_as::out) is det.

optimization_remove_deaths(ProcInfo, GI, ASin, ASout) :-
	proc_info_headvars(ProcInfo, HeadVars), 
	set__list_to_set(HeadVars, HeadVarsSet), 
	hlds_llds__goal_info_get_post_deaths(GI, Deaths0),
	set__difference(Deaths0, HeadVarsSet, Deaths), 
	set__to_sorted_list(Deaths, DeathsList),
	(
		ASin = real_as(Aliases0)
	->
		(
			DeathsList = []
		->
		 	ASout = ASin
		;
			remove_vars(DeathsList, Aliases0, 
				Aliases), 
			wrap(Aliases, ASout)
		)
	;
		ASout = ASin
	).


%-----------------------------------------------------------------------------%
extend_foreign_code(HLDS, ProcInfo, Attrs, PredId, ProcId, 
		Vars, MaybeModes, Types, Info, Ain, A) :- 
	from_foreign_code(HLDS, ProcInfo, PredId, ProcId, Info, Attrs, Vars, 
		MaybeModes, Types, ForeignAlias),
	(
		(is_bottom(ForeignAlias); is_top(ForeignAlias)) 
	-> 	
		% easy extend
		extend(HLDS, ProcInfo, ForeignAlias, Ain, A)
	; 
		% rename variables and types !
		proc_info_vartypes(ProcInfo, VarTypes), 
		list__map(map__lookup(VarTypes), Vars, ActualTypes), 
		rename_call_alias(proc(PredId, ProcId), HLDS, Vars, 
				ActualTypes, ForeignAlias, RenamedForeign), 
%		RenamedForeign = ForeignAlias, 
		extend(HLDS, ProcInfo, RenamedForeign, Ain, A)
	). 

				
:- pred from_foreign_code(module_info, proc_info, 
			pred_id, proc_id, 
			hlds_goal_info,
			pragma_foreign_proc_attributes,
			list(prog_var), list(maybe(pair(string, mode))),
                        list(type), alias_as).
:- mode from_foreign_code(in, in, in, in, in, in, in, in, in, out) is det.

from_foreign_code(HLDS, _ProcInfo, PredId, ProcId, GoalInfo, Attrs, Vars, 
		MaybeModes, Types, AliasAs):-
	module_info_pred_proc_info(HLDS, proc(PredId, ProcId), 
			_PredInfo, PragmaProcInfo), 
	(
		aliasing(Attrs, UserDefinedAlias), 
		UserDefinedAlias = aliasing(_, _, UserAlias),
		UserAlias \= top(_)
	->
		% Typecheck the aliasing: 
		(
			proc_info_headvars(PragmaProcInfo, FormalVars), 	
			typecheck_user_aliases_domain(HLDS, FormalVars, 
				Types, UserAlias)
		-> 
			Alias = UserAlias
		; 
			report_pragma_type_error(PragmaProcInfo, 
					GoalInfo, UserDefinedAlias)
		)
	;
		(
			maybe_modes_to_modes(MaybeModes, Modes),
			predict_bottom_alias(HLDS, Vars, Modes, Types)
		->
			Alias = bottom
		; 
			goal_info_get_context(GoalInfo, Context), 
			format_context(Context, ContextStr), 
			string__append_list(["pragma_foreign_code:",
					" (",ContextStr, ")"], Msg), 
			Alias = top([Msg])
		)
	), 
	from_aliases_domain_to_alias_as(Alias, AliasAs).


predict_bottom_alias(HLDS, Vars, Modes, Types):- 
	% else --> apply heuristics
	to_trios(Vars, Modes, Types, Trios), 
	% remove all unique objects
	remove_all_unique_vars(HLDS, Trios, NonUniqueVars), 
	% keep only the output vars
	collect_all_output_vars(HLDS, NonUniqueVars, OutputVars), 
	(
		OutputVars = [] 
	;	
		list__map(
			pred(Trio::in, Type::out) is det:-
			(
				Trio = trio(_, _, Type)
			), 
			OutputVars,
			OutputTypes),
		types_are_primitive(HLDS, OutputTypes) 
	).

:- pred report_pragma_type_error(proc_info::in, hlds_goal_info::in, 
				aliasing::in) is erroneous. 
report_pragma_type_error(ProcInfo, GoalInfo, Aliasing):- 
	proc_info_varset(ProcInfo, VarSet), 
	goal_info_get_context(GoalInfo, Context), 
	format_context(Context, ContextStr), 
	to_user_declared_aliasing(Aliasing, VarSet, AliasingString), 
	string__append_list(
		["\n", ContextStr, 
		": Type error in user declared aliasing. \n", 
		"\tDeclared aliasing = ", AliasingString, "\n", 
		"\t(NB: type-variables might be renamed in this error message)\n"],
		Msg), 
	require__error(Msg). 
	
:- pred typecheck_user_aliases_domain(module_info::in, 
		list(prog_var)::in,
		list(type)::in, aliases_domain::in) is semidet.
typecheck_user_aliases_domain(_, _, _, bottom). 
typecheck_user_aliases_domain(_, _, _, top(_)). 
typecheck_user_aliases_domain(ModuleInfo, Vars, Types, real(Aliases)):- 
	map__from_corresponding_lists(Vars, Types, VarTypes), 
	list__takewhile(
		typecheck_user_annotated_alias(ModuleInfo, VarTypes),
		Aliases, _, []).

:- pred typecheck_user_annotated_alias(module_info::in, 
		map(prog_var, type)::in, alias::in) is semidet.
typecheck_user_annotated_alias(ModuleInfo, VarTypes, Alias):-
	Alias = Data1 - Data2, 
	type_unify( 
		type_of_node_with_vartypes(ModuleInfo, VarTypes, Data1), 
		type_of_node_with_vartypes(ModuleInfo, VarTypes, Data2),
		[], 
		map__init, 
		Substitution),
	map__is_empty(Substitution).
		
:- pred maybe_modes_to_modes(list(maybe(pair(string, mode))), list(mode)).
:- mode maybe_modes_to_modes(in, out) is semidet.

maybe_modes_to_modes([], []).
maybe_modes_to_modes([MaybeMode | MaybeRest], [Mode | Rest]):- 
	MaybeMode = yes(_String - Mode), 
	maybe_modes_to_modes(MaybeRest, Rest). 

:- type trio ---> trio(prog_var, mode, type). 

:- pred to_trios(list(prog_var), list(mode), 
			list(type), list(trio)).
:- mode to_trios(in, in, in, out) is det.

to_trios(Vars, Modes, Types, Trios):-
	(
		Vars = [ V1 | VR ]
	->
		(
			Modes = [ Mode | MR ],
			Types = [ T1 | TR ]
		->
			Trio1 = trio(V1, Mode, T1), 
			to_trios(VR, MR, TR, TrioR), 
			Trios = [ Trio1 | TrioR ]
		;
			require__error("(pa_run) to_trios: lists of different length.")
		)
	;
		(
			Modes = [], Types = []
		->
			Trios = []
		;
			require__error("(pa_run) to_trios: not all lists empty.")
		)
	).
			
:- pred collect_all_output_vars(module_info::in, 
		list(trio)::in, list(trio)::out) is det.
:- pred remove_all_unique_vars(module_info::in, 
		list(trio)::in, list(trio)::out) is det.
:- pred collect_all_input_vars(module_info::in,
		list(trio)::in, list(trio)::out) is det.


collect_all_output_vars(HLDS, VarsIN, VarsOUT):- 
	list__filter(
		pred(P0::in) is semidet :- 
		(
			P0 = trio(_, Mode, Type), 
			mode_to_arg_mode(HLDS, Mode, Type, ArgMode), 
			ArgMode = top_out
		), 
		VarsIN, 
		VarsOUT
	).
	
remove_all_unique_vars(HLDS, VarsIN, VarsOUT):- 
	list__filter(
		pred(P0::in) is semidet :- 
		(
			P0 = trio(_, Mode, _), 
			mode_util__mode_get_insts(HLDS, Mode, _LeftInst, 
				RightInst),
			\+ inst_is_unique(HLDS, RightInst), 
			\+ inst_is_clobbered(HLDS, RightInst)
		),
		VarsIN, 
		VarsOUT
	).

collect_all_input_vars(HLDS, VarsIN, VarsOUT):- 
	list__filter(
		pred(P0::in) is semidet :- 
		(
			P0 = trio(_, Mode, Type), 
			mode_to_arg_mode(HLDS, Mode, Type, ArgMode), 
			ArgMode = top_in
		), 
		VarsIN, 
		VarsOUT
	).

%-----------------------------------------------------------------------------%

:- pred normalize_with_goal_info(proc_info::in, module_info::in, 
		hlds_goal_info::in, alias_as::in, alias_as::out) is det.
normalize_with_goal_info(ProcInfo, HLDS, GoalInfo, Alias0, Alias):- 
	goal_info_get_instmap_delta(GoalInfo, InstMapDelta),
	instmap__init_reachable(InitIM),
	instmap__apply_instmap_delta(InitIM, InstMapDelta, InstMap),
	normalize(HLDS, ProcInfo, InstMap, Alias0, Alias). 
	

normalize(HLDS, ProcInfo, Alias0, Alias):- 
	% normalize only using type-info's
	normalize_wti(HLDS, ProcInfo, Alias0, Alias).

normalize(HLDS, ProcInfo, _InstMap, Alias0, Alias):- 
	% normalize only using type-info's
	normalize_wti(HLDS, ProcInfo, Alias0, Alias).

:- pred normalize_wti(module_info::in, proc_info::in,
		alias_as::in, alias_as::out) is det.

normalize_wti(HLDS, ProcInfo, ASin, ASout):-
	(
		ASin = real_as(Aliases0)
	->
		normalize(HLDS, ProcInfo, Aliases0, 
				Aliases), 
		wrap(Aliases, ASout)
	;
		ASout = ASin
	).
		

%-----------------------------------------------------------------------------%
% Extra 
%-----------------------------------------------------------------------------%
:- pred wrap(alias_set, alias_as).
:- mode wrap(in, out) is det.

wrap(AliasSet, AS) :-
	(
		is_empty(AliasSet)
	->
		AS = bottom
	;
%		list__length(LIST,Length), 
%		Length > top_limit
%	->
%		top("Size too big", AS)
%	;
		AS = real_as(AliasSet)
	).

:- pred wrap_and_control(module_info::in, proc_info::in, 
				alias_set::in, alias_as::out) is det.

wrap_and_control(_ModuleInfo, _ProcInfo, AliasSet, AS):-
	wrap(AliasSet, AS).
/**
	(
		AliasList = []
	->
		AS = bottom
	; 
		list__length(AliasList,Length),
		Length > top_limit
	->
		pa_alias__apply_widening_list(ModuleInfo, ProcInfo, 
				AliasList, AliasList1), 
		AS = real_as(AliasList1)
	;
		AS = real_as(AliasList)
	).
**/

apply_widening(ModuleInfo, ProcInfo, Threshold, A0, A, Widening) :- 
	(	A0 = bottom, A = bottom, Widening = no
	; 	A0 = top(_), A = A0, Widening = no
	; 	A0 = real_as(AliasSet0), 
		apply_widening(ModuleInfo, ProcInfo, 
			Threshold, AliasSet0, AliasSet, Widening), 
		A = real_as(AliasSet)
	).

%-----------------------------------------------------------------------------%
% computing LIVE_SET
%-----------------------------------------------------------------------------%
live(ModuleInfo, ProcInfo, IN_USE, LIVE_0, AS, LIVE) :-
	(
		set__empty(IN_USE)
	->
		LIVE = LIVE_0
	;
		% IN_USE is not empty
		% AS top
		is_top(AS)
	->
		% then live must also be considered top
		sr_live__top(LIVE)
	;
		% IN_USE is not empty, 
		% AS is not top
		% AS bottom?
		is_bottom(AS)
	->
		sr_live__init(IN_USE, LIVE_1),
		sr_live__union([LIVE_1, LIVE_0], LIVE)
		
	;
		% most general case
		AS = real_as(AliasSet)
	->
		to_pair_alias_list(AliasSet, Aliases), 
		live_2(ModuleInfo, ProcInfo, IN_USE, LIVE_0, Aliases, LIVE)
	;
		error("(pa_alias_as) live: impossible situation.")	
	).


	% live_2(IN_USE, Aliases, Liveset)
	% pre-condition: IN_USE is not empty
:- pred live_2(module_info, proc_info, set(prog_var),sr_live__live_set,
		list(prog_data__alias), sr_live__live_set).
:- mode live_2(in, in, in, in, in, out) is det.

live_2(ModuleInfo, ProcInfo, IN_USE, LIVE_0, ALIASES, LIVE) :- 
	% LIVE = LIVE0 + LIVE1 + LIVE2 + LIVE3
	% where
	%	LIVE0 = LIVE_0
	%	LIVE1 = top-level datastructs from IN_USE
	%	LIVE2 = datastructs X^s such that X^s is aliased to
	%		Y^t, and Y is in IN_USE
	%	LIVE3 = datastructs X^s such that X^s is aliased to Y^t, 
	% 		and Y^t or some part of it is in LIVE_0
	%			X^sx1 in LIVE3
	%		if X^sx,Y^sy aliased, and
	%		exists s1,s2 such that Y^s1 in LIVE_0
	%		and sy = s1.s2 => sx1 = sx
	%			(the structure to which X^sx is aliased
	%			is fully live, therefore also X^sx will
	%			be fully live)
	%		or  sy.s2 = s1 => sx1 = sx.s2
	%			(only a subpart of the structure to which
	%			X^sx is aliased appears to be live, 
	%			then also the same subpart of X^sx will 
	%			be live)

	% (LIVE0)
	LIVE0 = LIVE_0,

	% (LIVE1)
	sr_live__init(IN_USE, LIVE1), 

	% (LIVE2)
	pa_alias__live_from_in_use(IN_USE, ALIASES, LIVE2),

	% (LIVE3)
	pa_alias__live_from_live0(ModuleInfo, ProcInfo, 
			LIVE_0, ALIASES, LIVE3),

	% LIVE
	sr_live__union([LIVE0,LIVE1,LIVE2,LIVE3],LIVE).


% live(ModuleInfo, ProcInfo, IN_USE, LIVE_0, AS) = LIVE :- 
	% live(ModuleInfo, ProcInfo, IN_USE, LIVE_0, AS, LIVE).


%-----------------------------------------------------------------------------%
from_aliases_domain_to_alias_as(bottom, bottom).
from_aliases_domain_to_alias_as(real(Aliases), AliasAS):- 
	from_pair_alias_list(Aliases, AliasSet), 
	wrap(AliasSet, AliasAS).
from_aliases_domain_to_alias_as(top(Msg), top(Msg)).

from_alias_as_to_aliases_domain(bottom, bottom).
from_alias_as_to_aliases_domain(real_as(AliasSet), real(Aliases)):-
	to_pair_alias_list(AliasSet, Aliases).
from_alias_as_to_aliases_domain(top(Msg), top(Msg)).

