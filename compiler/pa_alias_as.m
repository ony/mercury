%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_alias_as: defines the possible alias abstract substitution 
% main author: nancy

:- module pa_alias_as.

:- interface.

%-----------------------------------------------------------------------------%
%-- import_module 

% library modules
:- import_module set, list, map, string, int.
:- import_module io, term, std_util.

% compiler modules
:- import_module prog_data.
:- import_module hlds_goal.
:- import_module hlds_pred, hlds_module.
:- import_module instmap.
:- import_module sr_live.
:- import_module pa_datastruct.

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

:- pred project_set(set(prog_var), alias_as, alias_as).
:- mode project_set(in, in, out) is det.

	% Collect all the datastructures to which the datastructure
	% is aliased, taking into account possible termshifting.
	% Gives an error when alias_as is top.
:- pred collect_aliases_of_datastruct(module_info, proc_info, 
		pa_datastruct__datastruct, 
		alias_as, list(pa_datastruct__datastruct)).
:- mode collect_aliases_of_datastruct(in, in, in, in, out) is det.

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

:- pred extend_foreign_code(proc_info, module_info, hlds_goal_info, 
			list(prog_var), list(maybe(pair(string, mode))),
                        list(type), alias_as, alias_as).
:- mode extend_foreign_code(in, in, in, in, in, in, in, out) is det.

	% Add two abstract substitutions to each other. These
	% abstract substitutions come from different contexts, and have
	% not to be 'extended' wrt each other. 
:- pred add(alias_as, alias_as, alias_as).
:- mode add(in, in, out) is det.

	% normalization of the representation based on the types of
	% the variables (retreived from proc_info) and the instmaps.
:- pred normalize(hlds_pred__proc_info, module_info, instmap, alias_as, alias_as).
:- mode normalize(in, in, in, in, out) is det.



	% print-procedures:
	% print_maybe_possible_aliases: routine used within
	% hlds_dumps.
:- pred print_maybe_possible_aliases(maybe(alias_as), proc_info, pred_info, 
				io__state, io__state).
:- mode print_maybe_possible_aliases(in, in, in, di, uo) is det.

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

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
:- implementation.

% library modules
:- import_module require, term, assoc_list.

% compiler modules
:- import_module pa_alias, pa_util, pa_sr_util.
:- import_module pa_alias_set.

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
	assoc_list__from_corresponding_lists(FromTypes, ToTypes, 
				FromToTypes), 
	list__foldl(rename_type_det, FromToTypes, 
				map__init, Substitution), 
	rename_types(Substitution, ASin, ASout). 

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
	hlds_goal__goal_info_get_post_deaths(GI, Deaths0),
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
extend_foreign_code(_ProcInfo, HLDS, GoalInfo, 
			Vars, MaybeModes, Types, Alias0, Alias):-
	to_trios(Vars, MaybeModes, Types, Trios), 
	% remove all unique objects
	remove_all_unique_vars(HLDS, Trios, NonUniqueVars), 
	% keep only the output vars
	collect_all_output_vars(HLDS, NonUniqueVars, OutputVars), 
%	collect_all_input_vars(HLDS, NonUniqueVars, InputVars), 
	(
%		(
			OutputVars = [] 
%		; 
%			% XXXXXXXXXXXXXXXXX !!
%			OutputVars = [_], InputVars = []
%		)
	->
		Alias = Alias0
	;
		list__map( 
			pred(Trio::in, Type::out) is det:-
			( 
				Trio = trio(_, _, Type)
			), 
			OutputVars,
			OutputTypes),
		(
			types_are_primitive(HLDS, OutputTypes) 
		-> 
			Alias = Alias0
		; 

			goal_info_get_context(GoalInfo, Context), 
			term__context_line(Context, ContextLine), 
			term__context_file(Context, ContextFile), 
			string__int_to_string(ContextLine, ContextLineS), 

			string__append_list(["pragma_foreign_code:",
						" (",ContextFile, ":", 
						ContextLineS, ")"], Msg), 
			
			pa_alias_as__top(Alias0, Msg, Alias)
		)
	).
	

:- import_module std_util, inst_match.

:- type trio ---> trio(prog_var, mode, type). 

:- pred to_trios(list(prog_var), list(maybe(pair(string, mode))), 
			list(type), list(trio)).
:- mode to_trios(in, in, in, out) is det.

to_trios(Vars, MaybeModes, Types, Trios):-
	(
		Vars = [ V1 | VR ]
	->
		(
			MaybeModes = [ M1 | MR ],
			Types = [ T1 | TR ]
		->
			(
				M1 = yes(_String - Mode)
			->
				Trio1 = trio(V1, Mode, T1), 
				to_trios(VR, MR, TR, TrioR), 
				Trios = [ Trio1 | TrioR ]
			;
				to_trios(VR, MR, TR, Trios)
			)
		;
			require__error("(pa_run) to_trios: lists of different length.")
		)
	;
		(
			MaybeModes = [], Types = []
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

:- import_module mode_util.

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
		

%-------------------------------------------------------------------%
% printing routines
%-------------------------------------------------------------------%

	% MaybeAs = yes(Alias_as) -> print out Alias_as
	%         = no		   -> print "not available"
print_maybe_possible_aliases(MaybeAS, ProcInfo, PredInfo) -->
	(
		{ MaybeAS = yes(AS) }
	->	
		print_possible_aliases(AS, ProcInfo, PredInfo)
	;
		io__write_string("% not available.")
	).

	% print_possible_aliases(Abstract Substitution, Proc Info).
	% print alias abstract substitution
:- pred print_possible_aliases(alias_as, proc_info, pred_info, 
					io__state, io__state).
:- mode print_possible_aliases(in, in, in, di, uo) is det. 

print_possible_aliases(AS, ProcInfo, PredInfo) -->
	(
		{ AS = real_as(Aliases) }
	->
		pa_alias_set__print(PredInfo, ProcInfo, Aliases, 
				"% ", "\n")
	;
		{ AS = top(Msgs) }
	->
		{ list__map(
			pred(S0::in, S::out) is det :- 
				(string__append_list(["%\t",S0,"\n"], S)),
			Msgs, 
			MsgsF) }, 
		{ string__append_list(["% aliases are top:\n" |MsgsF],Msg) },
		io__write_string(Msg)
	;
		io__write_string("% aliases = bottom")
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


%-------------------------------------------------------------------%
% parsing routines
%-------------------------------------------------------------------%

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
			CONS = "."
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
			term__context_line(Context, ContextLine), 
			term__context_file(Context, ContextFile), 
			string__int_to_string(ContextLine, ContextLineS), 
			string__append_list(["imported top (", 
				ContextFile, ":", ContextLineS, ")"], 
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
		        CONS = ".",
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


%-------------------------------------------------------------------%
% computing LIVE_SET
%-------------------------------------------------------------------%
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


