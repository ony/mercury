%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_sr_util: extra utility predicates common to the alias (pa_*) and
%		     reuse passes (sr_*)
% main author: nancy

:- module pa_sr_util.

:- interface. 
%-----------------------------------------------------------------------------%

% library modules
:- import_module io, list, std_util, term. 

% XXX parent modules
:- import_module hlds, parse_tree.
% compiler modules. 
:- import_module hlds__hlds_pred, parse_tree__prog_data. 
:- import_module hlds__hlds_module.

:- pred trans_opt_output_vars_and_types(
		prog_varset::in, 
		vartypes::in, 
		tvarset::in, 
		list(prog_var)::in, 
		io__state::di, 
		io__state::uo) is det.

:- pred rename_type_det(pair((type), (type))::in,
                term__substitution(tvar_type)::in,
                term__substitution(tvar_type)::out) is det.

:- pred some_are_special_preds(list(pred_proc_id)::in, 
		module_info::in) is semidet.


%-----------------------------------------------------------------------------%
:- implementation. 

:- import_module bool, map, require.
:- import_module parse_tree__mercury_to_mercury.


trans_opt_output_vars_and_types(ProgVarSet, VarTypes, TypeVarSet, 
			RealHeadVars) --> 
	(
		{ RealHeadVars = [] } 
	->
		io__write_string("vars, types")

	;
		io__write_string("vars("),
		mercury_output_vars(RealHeadVars, ProgVarSet, no),
		io__write_string("), "),

		% extra info: 
		io__write_string("types("),
		io__write_list(RealHeadVars, ",",
			output_type_of_var(VarTypes, TypeVarSet)),
		io__write_string(")")
	).

:- pred output_type_of_var(vartypes::in, tvarset::in, 
		prog_var::in,
                io__state::di, io__state::uo) is det.

output_type_of_var(VarTypes, TypeVarSet, SomeVar) -->
        { map__lookup(VarTypes, SomeVar, Type) },
        mercury_output_term(Type, TypeVarSet, bool__no).


rename_type_det(FromType - ToType, S0, S) :-
        (
                term__unify(FromType, ToType, S0, S1)
        ->
                S = S1
        ;
		S = S0
       ).


%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

some_are_special_preds(PredProcIds, ModuleInfo):- 
	module_info_get_special_pred_map(ModuleInfo, SpecialPredMap), 
	map__values(SpecialPredMap, SpecialPreds), 

	(
		% either some of the predicates are special 
		% preds, such as __Unify__ and others

		list__filter(pred_id_in(SpecialPreds), PredProcIds,
				SpecialPredProcs),
		SpecialPredProcs = [_|_]

	; 
		% or some of the predicates are not defined in this
		% module. 

		list__filter(not_defined_in_this_module(ModuleInfo), 	
				PredProcIds,
				FilteredPredProcIds), 
		FilteredPredProcIds = [_|_]
	).

:- pred pred_id_in(list(pred_id), pred_proc_id).
:- mode pred_id_in(in, in) is semidet.

pred_id_in(PredIds, PredProcId):-
	PredProcId = proc(PredId, _),
	list__member(PredId, PredIds). 

:- pred not_defined_in_this_module(module_info, pred_proc_id).
:- mode not_defined_in_this_module(in,in) is semidet.

not_defined_in_this_module(ModuleInfo, proc(Predid, _)):-
	hlds_module__pred_not_defined_in_this_module(ModuleInfo,
		Predid).

