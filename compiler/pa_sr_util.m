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
                require__error("(pa_alias_as) rename_type_det: types are not
unifiable.")
        ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
