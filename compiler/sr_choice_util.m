%-----------------------------------------------------------------------------%
% Copyright (C) 2001-2002,2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_choice_util
% Main authors: nancy
%
% Common data types and procedures to sr_choice, and sr_choice_graphing. 
%-----------------------------------------------------------------------------%

:- module structure_reuse__sr_choice_util.
:- interface.

:- import_module hlds__hlds_module. 
:- import_module hlds__hlds_data.
:- import_module hlds__hlds_pred.
:- import_module parse_tree__prog_data.

:- import_module bool, io, std_util, list.

:- type strategy
        --->    strategy(
                        constraint      :: constraint,
                        selection       :: selection
                ).

        % The constraint on the cells that we consider available for
        % reuse.
:- type constraint
        --->    same_cons_id
        ;       within_n_cells_difference(int)
        .

        % How to select specific reuse candidates amongst a set of possible
	% candidates is either:
	% 	- lifo: take the cell that has died the most recently with
	%	  respect to the construction where it can be reused. 
	% 	- graph: build up a weighted graph, and select the
	% 	  best fitting candidate.
	% Both strategies are implemented in module sr_choice_graphing.
:- type selection
        --->    lifo
        ;       graph
        .

:- pred get_strategy(strategy::out, module_info::in, module_info::out,
                io__state::di, io__state::uo) is det.

%-----------------------------------------------------------------------------%

	% Type is not a tag-type. 
:- pred no_tag_type(module_info::in, vartypes::in, prog_var::in) is semidet.

        %
        % has_secondary_tag(Var, ConsId, HasSecTag) is true iff the
        % variable, Var, with cons_id, ConsId, requires a remote
        % secondary tag to distinguish between its various functors.
        %
:- pred has_secondary_tag(module_info::in, vartypes::in,
                prog_var::in, cons_id::in, bool::out) is det.

	%
	% already_correct_fields(HasSecTagC, VarsC, HasSecTagR - VarsR)
	% takes a list of variables, VarsC, which are the arguments for
	% the cell to be constructed and the list of variables, VarsR,
	% which are the arguments for the cell to be reused and returns
	% a list of bool where each yes indicates that argument already
	% has the correct value stored in it.  To do this correctly we
	% need to know whether each cell has a secondary tag field.
	%
:- func already_correct_fields(bool, prog_vars,
		pair(bool, prog_vars)) = list(bool).

%-----------------------------------------------------------------------------%
:- implementation. 

:- import_module libs__globals.
:- import_module libs__options.
:- import_module check_hlds__type_util.

:- import_module map, require, int.

get_strategy(Strategy, ModuleInfo0, ModuleInfo) -->
	io_lookup_string_option(structure_reuse_constraint, ConstraintStr),
	( 
		{ ConstraintStr = "same_cons_id" } 
	->
		{ Constraint = same_cons_id },
		{ ModuleInfo1 = ModuleInfo0 }
	; 
		{ ConstraintStr = "within_n_cells_difference" } 
	->
		io_lookup_int_option(structure_reuse_constraint_arg, NCells),
		{ Constraint = within_n_cells_difference(NCells) },
		{ ModuleInfo1 = ModuleInfo0 }
	;
		{ Constraint = same_cons_id },
		io__write_string("error: Invalid argument to --structure-reuse-constraint.\n"),
		io__set_exit_status(1),
		{ module_info_incr_errors(ModuleInfo0, ModuleInfo1) }
	),
	io_lookup_string_option(structure_reuse_selection, SelectionStr),
	( 
		{ SelectionStr = "lifo" } 
	->
		{ Selection = lifo },
		{ ModuleInfo = ModuleInfo1 }
	; 
		{ SelectionStr = "graph" } 
	->
		{ Selection = graph },
		{ ModuleInfo = ModuleInfo1 }
	; 
		{ Selection = lifo },
		io__write_string("error: Invalid argument to --structure-reuse-selection.\n"),
		io__set_exit_status(1),
		{ module_info_incr_errors(ModuleInfo1, ModuleInfo) }
	),
	{ Strategy = strategy(Constraint, Selection) }.

%-----------------------------------------------------------------------------%
no_tag_type(ModuleInfo, Vartypes, Var):-
	map__lookup(Vartypes, Var, VarType),
	type_is_no_tag_type(ModuleInfo, VarType, _, _).


has_secondary_tag(ModuleInfo, VarTypes, Var, ConsId, SecondaryTag) :- 
	(
		map__lookup(VarTypes, Var, Type),
		type_to_ctor_and_args(Type, TypeCTor, _)
	->
		module_info_types(ModuleInfo, Types),
		( map__search(Types, TypeCTor, TypeDefn) ->
			hlds_data__get_type_defn_body(TypeDefn, TypeBody),
			( TypeBody = du_type(_, ConsTagValues, _, _, _) ->
				(
						% The search can fail
						% for such types as
						% private_builtin:type_info,
						% if the search fails we
						% will not have a
						% secondary tag.
					map__search(ConsTagValues, ConsId,
							ConsTag),
					ConsTag = shared_remote_tag(_, _)
				->
					SecondaryTag = yes
				;
					SecondaryTag = no
				)
			;
				error("has_secondary_tag: not du type.")
			)
		;
				% Must be a basic type.
			SecondaryTag = no
		)
	;
		error("has_secondary_tag: type_to_ctor_and_args failed.")
		
	).

already_correct_fields(SecTagC, CurrentCellVars, SecTagR - ReuseCellVars)
	= Bools ++ list__duplicate(LengthC - LengthB, no) :-
		Bools = already_correct_fields_2(SecTagC, CurrentCellVars,
				SecTagR, ReuseCellVars),
		LengthC = list__length(CurrentCellVars),
		LengthB = list__length(Bools).

:- func already_correct_fields_2(bool, prog_vars, bool, prog_vars) = list(bool).

already_correct_fields_2(yes, CurrentCellVars, yes, ReuseCellVars)
	= equals(CurrentCellVars, ReuseCellVars).
already_correct_fields_2(yes, CurrentCellVars, no, ReuseCellVars)
	= [no | equals(CurrentCellVars, drop_one(ReuseCellVars))].
already_correct_fields_2(no, CurrentCellVars, yes, ReuseCellVars) 
	= [no | equals(drop_one(CurrentCellVars), ReuseCellVars)].
already_correct_fields_2(no, CurrentCellVars, no, ReuseCellVars) 
	= equals(CurrentCellVars, ReuseCellVars).

	%
	% equals(ListA, ListB) produces a list of bools which indicates
	% whether the corresponding elements from ListA and ListB were
	% equal.  If ListA and ListB are of different lengths, the
	% resulting list is the length of the shorter of the two.
	%
:- func equals(list(T), list(T)) = list(bool).

equals([], []) = [].
equals([], [_|_]) = [].
equals([_|_], []) = [].
equals([X | Xs], [Y | Ys]) = [Bool | equals(Xs, Ys)] :-
	( X = Y ->
		Bool = yes
	;
		Bool = no
	).

:- func drop_one(list(T)) = list(T).

drop_one([]) = [].
drop_one([_ | Xs]) = Xs.


%-----------------------------------------------------------------------------%
