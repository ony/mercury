%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% module pa_sr_util: extra utility predicates common to the alias (pa_*) and
%		     reuse passes (sr_*)
% main author: nancy

:- module pa_sr_util.

:- interface. 
%-----------------------------------------------------------------------------%

:- import_module io, list, std_util, term. 
:- import_module hlds_pred, prog_data. 
:- import_module hlds_module.

:- pred trans_opt_output_vars_and_types( 
		prog_varset::in, 
		vartypes::in, 
		tvarset::in, 
		list(prog_var)::in, 
		io__state::di, 
		io__state::uo) is det.

:- pred rename_type_det( pair( (type), (type) )::in,
                term__substitution(tvar_type)::in,
                term__substitution(tvar_type)::out ) is det.

:- pred some_are_special_preds(list(pred_proc_id)::in, 
		module_info::in) is semidet.

%-----------------------------------------------------------------------------%
:- implementation. 

:- import_module bool, map, require.
:- import_module mercury_to_mercury.


trans_opt_output_vars_and_types( ProgVarSet, VarTypes, TypeVarSet, 
			RealHeadVars ) --> 
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
			output_type_of_var(VarTypes, TypeVarSet) ),
		io__write_string(")")
	).

:- pred output_type_of_var( vartypes::in, tvarset::in, prog_var::in,
                io__state::di, io__state::uo) is det.

output_type_of_var( VarTypes, TypeVarSet, SomeVar ) -->
        { map__lookup( VarTypes, SomeVar, Type ) },
        mercury_output_term(Type, TypeVarSet, bool__no).


rename_type_det( FromType - ToType, S0, S ) :-
        (
                term__unify( FromType, ToType, S0, S1 )
        ->
                S = S1
        ;
		S = S0
/**
		term_to_tmp_string( FromType, FromTypeString), 
		term_to_tmp_string( ToType, ToTypeString), 
		string__append_list( [ 
		"(pa_sr_util) rename_type_det: types are not unifiable. \n",
		"\tFromType = ", FromTypeString, "\n", 
		"\tToType   = ", ToTypeString ], Msg ), 
                require__error(Msg)
**/
        ).

:- import_module string. 
:- pred term_to_tmp_string( term(T)::in, string::out) is det.

term_to_tmp_string( functor( Const, Args, _Cxt ), String ):-
		const_to_tmp_string( Const, S0 ), 
		list__map( term_to_tmp_string, Args, ArgStrings), 
		(
			ArgStrings = []
		->
			Arguments = ""
		;
			to_comma_separated_list( ArgStrings, Args0), 
			string__append_list( ["(", Args0, ")" ], Arguments)
		),	
		string__append_list( [ S0, Arguments ], String). 
term_to_tmp_string( variable( _ ), "var"). 

:- pred context_to_tmp_string( term__context::in, string::out) is det.
context_to_tmp_string( context( File, LineNumber ), String ):-
	string__int_to_string( LineNumber, Line), 
	string__append_list( [ File, ":", Line ], String). 	

:- pred to_comma_separated_list( list(string)::in, string::out) is det.
to_comma_separated_list( [], ""). 
to_comma_separated_list( [ First | Rest ], String ):- 
	(
		Rest = []
	->
		String = First
	; 
		to_comma_separated_list( Rest, StringRest), 
		string__append_list( [First, ",", StringRest ], String)
	).

:- pred const_to_tmp_string( const::in, string::out) is det.
const_to_tmp_string( Const, String ):-
	(
		Const = atom(String)
	; 
		Const = integer(Int), 
		string__int_to_string(Int,String)
	; 
		Const = string(String)
	; 	
		Const = float(Float), 
		string__float_to_string(Float, String)
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

