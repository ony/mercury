%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias_as: defines the possible alias abstract substitution 
% main author: nancy

:- module possible_alias__pa_alias_as.

:- interface.

:- import_module hlds__hlds_goal.
:- import_module hlds__hlds_module.
:- import_module hlds__hlds_pred.
:- import_module hlds__instmap.
:- import_module parse_tree__prog_data.
:- import_module possible_alias__pa_datastruct.
:- import_module structure_reuse__sr_live.

:- import_module set, list, map, string, int, varset.
:- import_module io, term, std_util.

%-----------------------------------------------------------------------------%
%-- exported types

:- type alias_as.

%-----------------------------------------------------------------------------%
%-- exported predicates

:- pred init(alias_as::out) is det.
:- pred is_bottom(alias_as::in) is semidet.

:- pred top(string::in, alias_as::out) is det.
:- pred top(alias_as::in, string::in, alias_as::out) is det.
:- pred is_top(alias_as::in) is semidet.

	% project alias abstract substitution on a list of variables.
	% (for each alias in alias_as, the variables involved will belong
	% to the given list of prog_var). 
:- pred project(list(prog_var), alias_as, alias_as).
:- mode project(in, in, out) is det.

:- pred project_on_live_vars(proc_info::in, hlds_goal_info::in, 
		alias_as::in, alias_as::out) is det.

:- pred project_set(set(prog_var), alias_as, alias_as).
:- mode project_set(in, in, out) is det.

	% Collect all the datastructures to which the datastructure
	% is aliased, taking into account possible termshifting.
	% Gives an error when alias_as is top.
:- pred collect_aliases_of_datastruct(module_info, proc_info, 
		pa_datastruct__datastruct, 
		alias_as, list(pa_datastruct__datastruct)).
:- mode collect_aliases_of_datastruct(in, in, in, in, out) is det.

	% Fully rename a given alias originating from a call
	% to a procedure with given pred_proc_id. 
	% rename_call_alias(PredProcId, ModuleInfo, ActualVars, 
	% 	ActualTypes, FormalAlias, ActualAlias). 
:- pred rename_call_alias(pred_proc_id, module_info, list(prog_var),
				list((type)), 
				alias_as, alias_as).
:- mode rename_call_alias(in, in, in, in, in, out) is det.

	% rename abstract substitution according to a mapping
	% of prog_vars (map (FROM_VARS, TO_VARS)).
:- pred rename(map(prog_var, prog_var), alias_as, alias_as).
:- mode rename(in, in, out) is det.

	% rename_types(FromTypes, ToTypes, Alias0, Alias).
	% Rename all the typevariables occurring in the aliases using the
	% mapping from FromTypes to ToTypes. 
:- pred rename_types(list((type))::in, list((type))::in, 
		alias_as::in, alias_as::out) is det.
	% rename_types(Substitution, Alias0, Alias). 
	% Rename all the type-variables occurring in the aliases using the
	% substitution mapping. 
:- pred rename_types(term__substitution(tvar_type)::in, 
		alias_as::in, alias_as::out) is det.

	% returns true if both abstract substitutions are equal. 
	% needed for fixpoint
:- pred equal(alias_as, alias_as).
:- mode equal(in, in) is semidet.

	% less_or_equal(ModuleInfo, ProcInfo, AliasAs1, AliasAs2). 
	% first abstract subst. is less than or equal to second
	% abstract subst. (for fixpoint). i.e. The first abstract
	% substitution expresses less than the second one: for each
	% alias Alias1 expressed by AliasAs1, there exists an alias
	% Alias2 from AliasAs2 such that Alias1 is tighter than 
	% Alias2. And there are no aliases from AliasAs2 which are not
	% greater than any of the aliases from AliasAs1. 
:- pred less_or_equal(module_info, proc_info, alias_as, alias_as).
:- mode less_or_equal(in, in, in, in) is semidet.

	% compute least upper bound. 
:- pred least_upper_bound(proc_info, module_info, 
				alias_as, alias_as, alias_as).
:- mode least_upper_bound(in, in, in, in, out) is det.

	% compute least upper bound of a list of abstract substitutions.
:- pred least_upper_bound_list(proc_info, module_info, hlds_goal_info, 
					list(alias_as), alias_as).
:- mode least_upper_bound_list(in, in, in, in, out) is det.

	% extend(ProcInfo, ModuleInfo, NEW, OLD, RESULT).
	% extend a given abstract substitution with new information.
	% NB: the order is _very_ important! The first alias-set is
	% the (new) one to be added to the second one (cumulating one). 
:- pred extend(proc_info, module_info, alias_as, alias_as, alias_as).
:- mode extend(in, in, in, in, out) is det.

	% specialized extend for unifications
:- pred extend_unification(proc_info, module_info, 
			hlds_goal__unification, 
			hlds_goal__hlds_goal_info, alias_as, alias_as).

:- mode extend_unification(in, in, in, in, in, out) is det.

:- pred extend_foreign_code(module_info::in, proc_info::in,
		pragma_foreign_proc_attributes::in, pred_id::in, proc_id::in, 
		list(prog_var)::in, list(maybe(pair(string, mode)))::in,
                list(type)::in, hlds_goal_info::in, 
		alias_as::in, alias_as::out) is det.

	% Add two abstract substitutions to each other. These
	% abstract substitutions come from different contexts, and have
	% not to be 'extended' wrt each other. 
:- pred add(alias_as, alias_as, alias_as).
:- mode add(in, in, out) is det.

	% normalization of the representation based on the types of
	% the variables (retreived from proc_info) and the instmaps.
:- pred normalize(hlds_pred__proc_info, module_info, instmap, alias_as, alias_as).
:- mode normalize(in, in, in, in, out) is det.



	% Dump the alias information (used in hlds_dumps). 
	% Each alias will be preceded by the string "% ". 
:- pred print_maybe_possible_aliases(maybe(alias_as), proc_info, pred_info, 
				io__state, io__state).
:- mode print_maybe_possible_aliases(in, in, in, di, uo) is det.

	% print_maybe_possible_aliases(RepeatingString, MaybeAS, ProcInfo, 
	% PredInfo). 
	% Dump the aliases, each alias preceded with the given first
	% string. 
:- pred print_maybe_possible_aliases(string, maybe(alias_as), proc_info, 
		pred_info, io__state, io__state).
:- mode print_maybe_possible_aliases(in, in, in, in, di, uo) is det.

	% print_maybe_interface_aliases: routine for printing
	% alias information in interface files.
:- pred print_maybe_interface_aliases(maybe(alias_as), 
				proc_info, pred_info, io__state, io__state).
:- mode print_maybe_interface_aliases(in, in, in, di, uo) is det.

:- pred print_aliases(alias_as, proc_info, pred_info, io__state, io__state).
:- mode print_aliases(in, in, in, di, uo) is det.

	% reverse routine of print_maybe_interface_aliases.
:- pred parse_read_aliases(list(term(T)), alias_as).
:- mode parse_read_aliases(in,out) is det.

:- pred parse_read_aliases_from_single_term(term(T), alias_as).
:- mode parse_read_aliases_from_single_term(in, out) is det.

:- pred parse_user_declared_aliases(term, varset, aliasing).
:- mode parse_user_declared_aliases(in, in, out) is semidet.

:- pred to_user_declared_aliases(aliasing, prog_varset, string). 
:- mode to_user_declared_aliases(in, in, out) is det.

	% Live = live(IN_USE,LIVE_0,ALIASES).
	% compute the live-set based upon an initial IN_USE set, 
	% and a list of aliases.
:- pred live(module_info, proc_info, 
		set(prog_var),live_set, alias_as, sr_live__live_set).
:- mode live(in, in, in,in, in,out) is det.

:- func live(module_info, proc_info, 
		set(prog_var),live_set, alias_as) = sr_live__live_set.
:- mode live(in, in, in,in, in) = out is det.

:- func size(alias_as) = int.
:- mode size(in) = out is det.

:- pred apply_widening(module_info::in, proc_info::in, alias_as::in, 	
		alias_as::out) is det. 

	% is_bottom_alias(ModuleInfo, HeadVars, Modes, Types) will check
	% whether the procedure with the given headvariables, modes and
	% types has a bottom-alias just by looking at the modes and types. 
	% It fails if the alias can not be shown to be bottom in this way. 
:- pred is_bottom_alias(module_info::in, list(prog_var)::in, 
		list(mode)::in, list(type)::in) is semidet.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- implementation.

:- import_module check_hlds__inst_match.
:- import_module check_hlds__mode_util.
:- import_module check_hlds__type_util.
:- import_module hlds__hlds_llds.
:- import_module parse_tree__mercury_to_mercury.
:- import_module possible_alias__pa_alias.
:- import_module possible_alias__pa_alias_set.
:- import_module possible_alias__pa_selector. 
:- import_module possible_alias__pa_sr_util.
:- import_module possible_alias__pa_util.

:- import_module require, term, assoc_list.
:- import_module std_util.

%-----------------------------------------------------------------------------%
%-- type definitions 

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

	% is_bottom
is_bottom(bottom).
is_bottom(real_as(AliasSet)):- pa_alias_set__is_empty(AliasSet).

	% top
top(Msg, top([NewMsg])):- 
	% string__append_list(["- ",Msg," -"],NewMsg).
	NewMsg = Msg.

top(Alias, Msg, top(Msgs)):-
	(
		Alias = top(FirstMsgs)
	->
		Msgs = FirstMsgs
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
size(top(_)) = 999999.
size(real_as(AliasSet)) = L :- 
	pa_alias_set__get_size(AliasSet, L). 

	% project
project(Listvar, ASin , ASout):-
	(
		ASin = real_as(AliasSet0)
	->
		pa_alias_set__project(Listvar, AliasSet0, AliasSet), 
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
		pa_alias_set__collect_aliases_of_datastruct(ModuleInfo, 
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
	pa_alias_as__rename(Dict, FormalAlias, FormalAlias1),
	pa_alias_as__rename_types(FormalTypes,  ActualTypes, 
			FormalAlias1, ActualAlias).

rename(MapVar, ASin, ASout):-
	(
		ASin = real_as(Aliases)
	->
		pa_alias_set__rename(MapVar, Aliases, RAliases), 
		wrap(RAliases, ASout)
	;
		% ASin is bottom or top(_)
		ASout = ASin 
	).

rename_types(FromTypes, ToTypes, ASin, ASout) :- 
	(
		ASin = real_as(AliasSet0)
	-> 
		assoc_list__from_corresponding_lists(FromTypes, ToTypes, 
				FromToTypes), 
		list__foldl(rename_type_det, FromToTypes, 
				map__init, Substitution), 
		pa_alias_set__rename_types(Substitution, AliasSet0, 
				AliasSet),
		ASout = real_as(AliasSet)
	; 
		ASout = ASin 	% bottom or top
	).

rename_types(Substitution, A0, A) :- 
	(
		A0 = real_as(AliasSet0)
	-> 
		pa_alias_set__rename_types(Substitution, AliasSet0, 
				AliasSet), 
		A = real_as(AliasSet)
	; 
		A = A0
	).
			

equal(AS1, AS2):-
	(
		AS1 = real_as(AliasSet1),
		AS2 = real_as(AliasSet2), 
		pa_alias_set__equal(AliasSet1, AliasSet2)
	;
		% AS1 is bottom or top(_)
		(AS1 = bottom, AS2 = bottom)
		;
		(is_top(AS1), is_top(AS2))
	).

less_or_equal(ModuleInfo, ProcInfo, AS1, AS2):-
	(
		AS1 = real_as(AliasSet1),
		AS2 = real_as(AliasSet2),
		pa_alias_set__less_or_equal(ModuleInfo, ProcInfo, 
				AliasSet1, AliasSet2) 
	;
		(AS1 = bottom ; AS2 = top(_))
	).

least_upper_bound(ProcInfo, HLDS, AS1, AS2, RESULT) :-
	(
		AS1 = real_as(AliasSet1)
	->
		(
			AS2 = real_as(AliasSet2)
		->
			pa_alias_set__least_upper_bound(HLDS, ProcInfo, 
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

least_upper_bound_list(ProcInfo, HLDS, _GoalInfo, Alias_list0, AS) :-
	list__foldl(least_upper_bound(ProcInfo, HLDS) , Alias_list0, 
			bottom, AS).

extend(ProcInfo, HLDS,  A1, A2, RESULT):-
	(
		A1 = real_as(NEW)
	->
		(
			A2 = real_as(OLD)
		->
			pa_alias_set__extend(HLDS, ProcInfo, 
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
			pa_alias_set__add(AliasSet1, AliasSet2, AliasSet), 
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
extend_unification(ProcInfo, HLDS, Unif, GoalInfo, ASin, ASout):-
	pa_alias__from_unification(ProcInfo, HLDS, Unif, GoalInfo, AUnif),
	pa_alias_set__from_pair_alias_list(AUnif, AliasSetUnif), 
	wrap(AliasSetUnif, ASUnif),
	extend(ProcInfo, HLDS, ASUnif, ASin, ASout0), 
	(
		Unif = construct(_, _, _, _, _, _, _)
	-> 
		optimization_remove_deaths(ProcInfo, ASout0, GoalInfo, ASout)
	;
		ASout = ASout0
	).

:- pred optimization_remove_deaths(proc_info, alias_as, 
					hlds_goal_info, alias_as).
:- mode optimization_remove_deaths(in, in, in, out) is det.

optimization_remove_deaths(ProcInfo, ASin, GI, ASout) :-
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
			pa_alias_set__remove_vars(DeathsList, Aliases0, 
				Aliases), 
			wrap(Aliases, ASout)
		)
	;
		ASout = ASin
	).


%-----------------------------------------------------------------------------%
extend_foreign_code(HLDS, ProcInfo, Attrs, PredId, ProcId, 
		Vars, MaybeModes, Types, Info, Ain, A) :- 
	from_foreign_code(ProcInfo, HLDS, PredId, ProcId, Info, Attrs, Vars, 
		MaybeModes, Types, ForeignAlias),
	(
		(is_bottom(ForeignAlias); is_top(ForeignAlias)) 
	-> 	
		% easy extend
		pa_alias_as__extend(ProcInfo, HLDS, ForeignAlias, Ain, A)
	; 
		% rename variables and types !
		proc_info_vartypes(ProcInfo, VarTypes), 
		list__map(map__lookup(VarTypes), Vars, ActualTypes), 
		rename_call_alias(proc(PredId, ProcId), HLDS, Vars, 
				ActualTypes, ForeignAlias, RenamedForeign), 
%		RenamedForeign = ForeignAlias, 
		pa_alias_as__extend(ProcInfo, HLDS, RenamedForeign, Ain, A)
	). 

				
:- pred from_foreign_code(proc_info, module_info, 
			pred_id, proc_id, 
			hlds_goal_info,
			pragma_foreign_proc_attributes,
			list(prog_var), list(maybe(pair(string, mode))),
                        list(type), alias_as).
:- mode from_foreign_code(in, in, in, in, in, in, in, in, in, out) is det.

from_foreign_code(_ProcInfo, HLDS, PredId, ProcId, GoalInfo, Attrs, Vars, 
		MaybeModes, Types, Alias):-
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
			typecheck_user_annotated_alias(HLDS, FormalVars, 
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
			is_bottom_alias(HLDS, Vars, Modes, Types)
		->
			Alias = bottom
		; 
			goal_info_get_context(GoalInfo, Context), 
			format_context(Context, ContextStr), 
			string__append_list(["pragma_foreign_code:",
					" (",ContextStr, ")"], Msg), 
			pa_alias_as__top(Msg, Alias)
		)
	).


is_bottom_alias(HLDS, Vars, Modes, Types):- 
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
	to_user_declared_aliases(Aliasing, VarSet, AliasingString), 
	string__append_list(
		["\n", ContextStr, 
		": Type error in user declared aliasing. \n", 
		"\tDeclared aliasing = ", AliasingString, "\n", 
		"\t(NB: type-variables might be renamed in this error message)\n"],
		Msg), 
	require__error(Msg). 
	
:- pred typecheck_user_annotated_alias(module_info::in, list(prog_var)::in,
		list(type)::in, alias_as::in) is semidet.
typecheck_user_annotated_alias(_, _, _, bottom). 
typecheck_user_annotated_alias(_, _, _, top(_)). 
typecheck_user_annotated_alias(ModuleInfo, Vars, Types, real_as(AliasSet)):- 
	map__from_corresponding_lists(Vars, Types, VarTypes), 
	to_pair_alias_list(AliasSet, AliasList),
	typecheck_user_annotated_alias_2(ModuleInfo, VarTypes, AliasList). 

:- pred typecheck_user_annotated_alias_2(module_info::in, 
		map(prog_var, type)::in, list(alias)::in) is semidet.
typecheck_user_annotated_alias_2(_, _, []). 
typecheck_user_annotated_alias_2(ModuleInfo, VarTypes, [Alias | Rest]):-
	Alias = Data1 - Data2, 
	type_unify( 
		type_of_node_with_vartypes(ModuleInfo, VarTypes, Data1), 
		type_of_node_with_vartypes(ModuleInfo, VarTypes, Data2),
		[], 
		map__init, 
		Substitution),
	map__is_empty(Substitution),
	typecheck_user_annotated_alias_2(ModuleInfo, VarTypes, Rest).
		

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
	normalize(ProcInfo, HLDS, InstMap, Alias0, Alias). 
	

normalize(ProcInfo, HLDS, _InstMap, Alias0, Alias):- 
	% normalize only using type-info's
	normalize_wti(ProcInfo, HLDS, Alias0, Alias).

:- pred normalize_wti(proc_info, module_info, alias_as, alias_as).
:- mode normalize_wti(in, in, in, out) is det.

normalize_wti(ProcInfo, HLDS, ASin, ASout):-
	(
		ASin = real_as(Aliases0)
	->
		pa_alias_set__normalize(HLDS, ProcInfo, Aliases0, 
				Aliases), 
		wrap(Aliases, ASout)
	;
		ASout = ASin
	).
		

%-----------------------------------------------------------------------------%
% printing routines
%-----------------------------------------------------------------------------%

	% MaybeAs = yes(Alias_as) -> print out Alias_as
	%         = no		   -> print "not available"
print_maybe_possible_aliases(MaybeAS, ProcInfo, PredInfo) -->
	print_maybe_possible_aliases("% ", MaybeAS, ProcInfo, PredInfo). 

print_maybe_possible_aliases(RepeatingStart, MaybeAS, ProcInfo, PredInfo) -->
	(
		{ MaybeAS = yes(AS) }
	->
		print_possible_aliases(RepeatingStart, AS, ProcInfo, PredInfo)
	;
		io__write_string("% not available.")
	).

	% print_possible_aliases(Abstract Substitution, Proc Info).
	% print alias abstract substitution
:- pred print_possible_aliases(string::in, alias_as::in, proc_info::in, 
		pred_info::in, io__state::di, io__state::uo) is det.
print_possible_aliases(RepeatingStart, AS, ProcInfo, PredInfo) -->
	(
		{ AS = real_as(Aliases) }
	->
		io__nl, 
		pa_alias_set__print(PredInfo, ProcInfo, Aliases, 
				RepeatingStart, ",\n", "")
	;
		{ AS = top(Msgs) }
	->
		{ list__map(
			pred(S0::in, S::out) is det :- 
				(string__append_list(["%\t",S0,"\n"], S)),
			Msgs, 
			MsgsF) }, 
		{ string__append_list([RepeatingStart, "aliases are top:\n" |MsgsF],Msg) },
		io__write_string(Msg)
	;
		{ string__append_list([RepeatingStart, "aliases = bottom"],
			Msg) }, 
		io__write_string(Msg)
	).

	% MaybeAs = yes(Alias_as) -> print `yes(printed Alias_as)'
	%         = no		  -> print `not_available'
print_maybe_interface_aliases(MaybeAS, ProcInfo, PredInfo) -->
	(
		{ MaybeAS = yes(AS) }
	->
		io__write_string("yes("),
		print_aliases(AS, ProcInfo, PredInfo),
		io__write_string(")")
	;
		io__write_string("not_available")
	).

print_aliases(AS, ProcInfo, PredInfo) --> 
	(
		{ AS = real_as(Aliases) }
	->
		io__write_string("["),
		pa_alias_set__print(PredInfo, ProcInfo, Aliases, 
				" ", ""),
		io__write_string("]")
	;
		{ AS = top(_Msgs) }
	->
		io__write_string("top")
	;
		io__write_string("bottom")
	).


%-----------------------------------------------------------------------------%
% parsing routines
%-----------------------------------------------------------------------------%

parse_read_aliases(LISTTERM ,AS):- 
	(
		% LISTTERM ought to have only one element
		LISTTERM = [ OneITEM ]
	->
		parse_read_aliases_from_single_term(OneITEM, AS)
	;
		list__length(LISTTERM, L),
		string__int_to_string(L, LS), 
		string__append_list(["(pa_alias_as) parse_read_aliases: wrong number of arguments. yes/", LS,
				" should be yes/1"], Msg),
		error(Msg)
	).

parse_read_aliases_from_single_term(OneITEM, AS) :- 
	(
		OneITEM = term__functor(term__atom(CONS), _TERMS, Context)
	->
		(
			CONS = "[|]"
		->
			parse_list_alias_term(OneITEM, Aliases),
			pa_alias_set__from_pair_alias_list(Aliases, 
					AliasSet), 
			wrap(AliasSet, AS)
			% AS = bottom
		;
			CONS = "bottom"
		->
			AS = bottom

		; 
			CONS = "top"
		->
			format_context(Context, ContextString), 
			string__append_list(["imported top (", 
				ContextString, ")"], 
					Msg),
			top(Msg, AS)
		;
			string__append(
		"(pa_alias_as) parse_read_aliases_from_single_term: could not parse aliases, top cons: ", CONS, Msg),
			error(Msg)
		)
	;
		error("(pa_alias_as) parse_read_aliases_from_single_term: term not a functor")
	).


:- pred parse_list_alias_term(term(T), list(pa_alias__alias)).
:- mode parse_list_alias_term(in, out) is det.

parse_list_alias_term(TERM, Aliases) :-
	(
		TERM = term__functor(term__atom(CONS), Args, _)
	->
		(
		        CONS = "[|]",
                        Args = [ AliasTerm, Rest]
                ->
			pa_alias__parse_term(AliasTerm, Alias),
			parse_list_alias_term(Rest, RestAliases), 
                        Aliases = [ Alias | RestAliases ]
                ;
			CONS = "[]"
		->
			Aliases = []
		;
			string__append("(pa_alias_as) parse_list_alias_term: could not parse aliases, top cons: ", CONS, Msg),
			error(Msg)
		)
        ;
                error("(pa_alias_as) parse_list_alias_term: term is not a functor")
	).

%-----------------------------------------------------------------------------%
% user declared aliases
%-----------------------------------------------------------------------------%

parse_user_declared_aliases(term__functor(term__atom("no_aliasing"), [], _),
		_VarSet, Aliasing):-
        pa_alias_as__init(BottomAlias),
	Aliasing = aliasing(no, varset__init, BottomAlias). 
parse_user_declared_aliases(term__functor(term__atom("unknown_aliasing"), 
				[], Context), _VarSet, Aliasing):-
	format_context(Context, ContextString), 
	string__append_list(["user declared top (", ContextString, ")"], Msg),
        pa_alias_as__top(Msg, TopAlias), 
	Aliasing = aliasing(no, varset__init, TopAlias). 
parse_user_declared_aliases(term__functor(term__atom("alias"), 
		[TypesTerm,AliasTerm], _), VarSet, Aliasing):-
	(
		TypesTerm = term__functor(term__atom("yes"), 
					ListTypesTerms, _), 
		term__vars_list(ListTypesTerms, TypeVars), 
		set__list_to_set(TypeVars, SetTypeVars), 
		varset__select(VarSet, SetTypeVars, TypeVarSet0),
		varset__coerce(TypeVarSet0, TypeVarSet),
		
		list__map(term__coerce, ListTypesTerms, Types), 
		MaybeTypes = yes(Types)
	;
		TypesTerm = term__functor(term__atom("no"),[],_), 
		MaybeTypes = no,
		varset__init(TypeVarSet) 
	), 
	parse_user_declared_aliases_2(AliasTerm, AliasAs), 
	Aliasing = aliasing(MaybeTypes, TypeVarSet, AliasAs). 

:- pred format_context(term__context::in, string::out) is det.
format_context(Context, String):- 
	term__context_line(Context, ContextLine), 
	term__context_file(Context, ContextFile), 
	string__int_to_string(ContextLine, ContextLineS), 
	string__append_list([ContextFile, ":", ContextLineS], 
			String).

:- pred parse_user_declared_aliases_2(term::in, alias_as::out) is det.
parse_user_declared_aliases_2(ListTerm, AliasAS):- 
	(
		parse_list_term(ListTerm, AllTerms)
	-> 
		list__map(parse_single_user_declared_alias, 
				AllTerms, AliasList),
		pa_alias_set__from_pair_alias_list(AliasList, AliasSet),
		wrap(AliasSet, AliasAS)
	;
		error("(pa_alias_as) parse_user_declared_aliases_2: term not a functor")
	).

:- pred parse_list_term(term::in, list(term)::out) is semidet.
parse_list_term(ListTerm, Terms):- 
	ListTerm = term__functor(term__atom(Cons), Args, _), 
	(
		Cons = "[|]"
	->
		Args = [FirstTerm, RestTerm],
		parse_list_term(RestTerm, RestList), 
		Terms = [FirstTerm | RestList]
	;
		Cons = "[]"
	->
		Terms = []
	; 
		fail
	). 

:- pred parse_single_user_declared_alias(term::in, alias::out) is det.
parse_single_user_declared_alias(Term, Alias):- 
	(
		Term = term__functor(term__atom("-"), [Left, Right], _)
	->
		% Left and Right have shape "cel(ProgVar, Types)"
		parse_user_datastruct(Left, LeftData), 
		parse_user_datastruct(Right, RightData), 
		Alias = LeftData - RightData
	;
		error("(pa_alias_as) parse_single_user_declared_alias: wrong functor.")
	).

% might be better to move this code to pa_datastruct ? 
:- pred parse_user_datastruct(term::in, 
		pa_datastruct__datastruct::out) is det. 
parse_user_datastruct(Term, Data):- 
	(
		Term = term__functor(term__atom("cel"),
			[VarTerm, TypesTerm], Context)
	->
		(
			VarTerm = term__variable(GenericVar),
			term__coerce_var(GenericVar, ProgVar) 
		-> 
			(
				parse_list_term(TypesTerm, ListTypesTerms)
			-> 
				list__map(term__coerce, ListTypesTerms, Types),
				pa_selector__from_types(Types, Selector), 
				pa_datastruct__create(ProgVar, Selector, Data)
			;
				format_context(Context, ContextString), 
				string__append_list([
				"(pa_alias_as) parse_user_datastruct: ", 
				"error in declared selector (", 
					ContextString, ")"], Msg), 
				error(Msg)
				
			)
		;
			format_context(Context, ContextString), 
			string__append_list([
				"(pa_alias_as) parse_user_datastruct: ", 
				"error in declared alias (", 
				ContextString, ")"], Msg), 
			error(Msg)
		)
	;
		error("(pa_alias_as) parse_user_datastruct: wrong datastructure description -- should be cel/2")
	).

		
to_user_declared_aliases(aliasing(_, _, bottom), _, "no_aliasing"). 
to_user_declared_aliases(aliasing(_, _, top(_)), _, "unknown_aliasing").
% to_user_declared_aliases(aliasing(_, _, real_as(_)), _, "alias(no, [])"). 
% to_user_declared_aliases(aliasing(MaybeTypes, real_as(_)), 
%				ProgVarSet, String):- 
to_user_declared_aliases( aliasing(MaybeTypes, TypeVarSet, real_as(AliasSet)), 
		ProgVarSet, String):-
	(
		MaybeTypes = yes(Types) 
	->
		TypesString0 = mercury_type_list_to_string(TypeVarSet, Types),
		string__append_list(["yes(", TypesString0, ")"], 
			TypesString)
	;
		TypesString = "no"
	), 
	pa_alias_set__to_pair_alias_list(AliasSet, AliasList), 
	alias_list_to_user_declared_aliases(AliasList, 
			ProgVarSet, TypeVarSet, AliasString0), 
	string__append_list(["[",AliasString0,"]"], AliasString), 

	string__append_list(["alias(", TypesString, ", ", 
			AliasString, ")"], String).

:- pred alias_list_to_user_declared_aliases(list(alias)::in, 
		prog_varset::in, tvarset::in, string::out) is det. 
alias_list_to_user_declared_aliases([], _, _, ""). 
alias_list_to_user_declared_aliases([Alias|Rest], ProgVarSet, TypeVarSet,
		String):- 
	alias_to_user_declared_alias(Alias, ProgVarSet, TypeVarSet, 
			AliasString), 
	(
		Rest = []
	->
		String = AliasString
	; 
		alias_list_to_user_declared_aliases(Rest, ProgVarSet, 
				TypeVarSet, RestString), 
		string__append_list([AliasString, ", ", RestString], 
				String)
	).

:- pred alias_to_user_declared_alias(alias::in, prog_varset::in,
		tvarset::in, string::out) is det.
alias_to_user_declared_alias(Alias, ProgVarSet, TypeVarSet, String):- 
	Alias = Data0 - Data1, 
	pa_datastruct__to_user_declared(Data0, ProgVarSet, TypeVarSet, 
			Data0String), 
	pa_datastruct__to_user_declared(Data1, ProgVarSet, TypeVarSet,
			Data1String),
	string__append_list([Data0String, " - ", Data1String],
			String). 
		
		

%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
% Extra 
%-----------------------------------------------------------------------------%
:- pred wrap(pa_alias_set__alias_set, alias_as).
:- mode wrap(in, out) is det.

wrap(AliasSet, AS) :-
	(
		pa_alias_set__get_size(AliasSet, 0) 
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

apply_widening(_, _, A0, A):- 
	A0 = bottom, 
	A = A0. 
apply_widening(_, _, A0, A):- 
	A0 = top(_), 
	A = A0. 
apply_widening(ModuleInfo, ProcInfo, A0, A):- 
	A0 = real_as(AliasSet0), 
	pa_alias_set__apply_widening(ModuleInfo, ProcInfo, 
			AliasSet0, AliasSet), 
	A = real_as(AliasSet).

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
		pa_alias_set__to_pair_alias_list(AliasSet, Aliases), 
		live_2(ModuleInfo, ProcInfo, IN_USE, LIVE_0, Aliases, LIVE)
	;
		error("(pa_alias_as) live: impossible situation.")	
	).


	% live_2(IN_USE, Aliases, Liveset)
	% pre-condition: IN_USE is not empty
:- pred live_2(module_info, proc_info, set(prog_var),sr_live__live_set,
		list(pa_alias__alias), sr_live__live_set).
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


live(ModuleInfo, ProcInfo, IN_USE, LIVE_0, AS) = LIVE :- 
	live(ModuleInfo, ProcInfo, IN_USE, LIVE_0, AS, LIVE).


