%-----------------------------------------------------------------------------%
% Copyright (C) 1997-1998 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% term_util.m
% Main authors: crs, vjteag.
%
% This module:
%
% -	defines the types used by termination analysis
% -	defines predicates for computing functor norms
% -	defines some utility predicates
%
%-----------------------------------------------------------------------------%

:- module term_util.

:- interface.

:- import_module term_errors, prog_data.
:- import_module hlds_module, hlds_pred, hlds_data, hlds_goal.

:- import_module bag, bimap, bool, int, list, lp_rational, map, 
	set, std_util. 

%-----------------------------------------------------------------------------%


:- type size_var_type	--->	size_var_type(pred_proc_id).

:- type size_var	==	lp_var.
% :- type size_var_supply	==	safe_term__var_supply(size_var_type).
:- type size_varset	==	lp_varset.

%-----------------------------------------------------------------------------%

% The arg size info defines an upper bound on the difference
% between the sizes of the output arguments of a procedure and the sizes
% of the input arguments:
%
% | input arguments | + constant >= | output arguments |
%
% where | | represents a semilinear norm.

:- type arg_size_info
	--->	finite(int, list(bool))
				% The termination constant is a finite integer.
				% The list of bool has a 1:1 correspondence
				% with the input arguments of the procedure.
				% It stores whether the argument contributes
				% to the size of the output arguments.

	;	infinite(list(term_errors__error))
				% There is no finite integer for which the
				% above equation is true. The argument says
				% why the analysis failed to find a finite
				% constant.

	;	constraints(
			equations,
			set(size_var),
			bimap(prog_var, size_var)
		)
	.

:- type termination_info
	---> 	cannot_loop	% This procedure terminates for all
				% possible inputs.

	;	can_loop(list(term_errors__error)).
				% The analysis could not prove that the
				% procedure terminates.

:- type used_args	==	map(pred_proc_id, list(bool)).

%-----------------------------------------------------------------------------%

% We use semilinear norms (denoted by ||) to compute the sizes of terms.
% These have the form
%
% | f(t1, ... tn) | = weight(f) + sum of | ti |
% where i is an element of a set I, and I is a subset of {1, ... n}
%
% We currently support four kinds of semilinear norms.

:- type functor_info
	--->	simple	% All non-constant functors have weight 1,
			% while constants have weight 0.
			% Use the size of all subterms (I = {1, ..., n}.

	;	total	% All functors have weight = arity of the functor.
			% Use the size of all subterms (I = {1, ..., n}.

	;	use_map(weight_table)
			% The weight of each functor is given by the table.
			% Use the size of all subterms (I = {1, ..., n}.

	;	use_map_and_args(weight_table).
			% The weight of each functor is given by the table,
			% and so is the set of arguments of the functor whose
			% size should be counted (I is given by the table
			% entry of the functor).

:- type unify_info	==	pair(map(prog_var, type), functor_info).

:- type weight_info	--->	weight(int, list(bool)).
:- type weight_table	==	map(pair(type_id, cons_id), weight_info).

:- pred find_weights(module_info::in, weight_table::out) is det.

% This predicate computes the weight of a functor and the set of arguments
% of that functor whose sizes should be counted towards the size of the whole
% term.

:- pred functor_norm(functor_info::in, type_id::in, cons_id::in,
	module_info::in, int::out, list(prog_var)::in, list(prog_var)::out,
	list(uni_mode)::in, list(uni_mode)::out) is det.

:- type pass_info
	--->	pass_info(
			functor_info,
			int,		% Max number of errors to gather.
			int		% Max number of paths to analyze.
		).
%-----------------------------------------------------------------------------%

:- type constraint_info 
	---> 	constr_info(  

			size_varset,	% A varset is used to create a set of
					% non-clashing variables to pass to
					% project and convex_hull.  
			 
			eqn_info	% All the constraints found so far
					% If this isn't "false_equation", 
					% it should imply that all the
					% variables are non-negative, except
					% possibly for those known to be of
					% zero-size type.
		).			
 
 :- type eqn_info 
 	--->	eqns(equations)	 	% All the constraints found so far.	

	;	false_equation. 	% Bottom. Indicates that we found a 
					% call to a procedure that has 
					% not yet been approximated,
					% or that we found the conjunction of
					% two or more mutually inconsistent
					% approximations.
				

%-----------------------------------------------------------------------------%

% These predicates are for dealing with equations.

% rename_vars: takes a list of prog_vars and outputs the corresponding
% list of size_vars, based on the given bimap.
:- pred rename_vars(list(prog_var), list(size_var), bimap(prog_var, size_var)).
:- mode rename_vars(in, out, in) is det.

:- pred rename_var(prog_var, size_var, bimap(prog_var, size_var)).
:- mode rename_var(in, out, in) is det.  

% compare_eqns(Eqn1, Eqn2, Result). 
% Compares two equations, assumed to be in canonical form.
% If Eqn1 is implied by Eqn2, then the result is '>'.  Otherwise, order
% is determined by compare_var_lists, for which any two equations with the
% same variables are 'equal'.
:- pred compare_eqns(equation, equation, comparison_result).
:- mode compare_eqns(in, in, out) is det.

% Compares a list of coefficients, by lexicographic order on the corresponding
% list of variables.  Individual variables are compared using the compare 
% builtin.  The rat in the coefficient is ignored.
:- pred compare_var_lists(list(coeff), list(coeff), comparison_result).
:- mode compare_var_lists(in, in, out) is det.

% Compares a list of coefficients, by lexicographic order on the corresponding
% list of rationals.
:- pred compare_rat_lists(list(coeff), list(coeff), comparison_result).
:- mode compare_rat_lists(in, in, out) is det.

% Put equations into a canonical form:  Every equation contains =<, 
% has its coefficients listed in increasing order of variable name,
% and has first coefficient equal to plus or minus 1.
:- pred canonical_form(equations, equations).
:- mode canonical_form(in, out) is det.

% Removes from equations coefficients corresponding to vars we know to be
% of zero-size type.  Removes any equations that then have no coefficients.
:- pred remove_zero_vars(set(size_var), equations, equations).
:- mode remove_zero_vars(in, in, out) is det.

% Returns a set containing all the size_vars corresponding to prog_vars
% that have a type that is always of zero size.
:- pred find_zero_size_vars(module_info, bimap(prog_var, size_var),
                map(prog_var, type), set(size_var)).
:- mode find_zero_size_vars(in, in, in, out) is det.


% This checks every pair of equations in the set for pairwise implication.
% It is not as sophisticated as checking for each new equation whether all
% the other constraints entail it, but it is faster.
% This is necessary before widening by testing for
% parallel weaker equations, since otherwise we might widen unnecessarily.
% For example, if x =< 1 is in the old constraints and x =< 2 is in the new
% constraints, we don't need to remove this equation if x =< 1 also occurs
% in the new constraints.
:- pred remove_redundant_eqns(equations, equations).
:- mode remove_redundant_eqns(in, out) is det.


%-----------------------------------------------------------------------------

% This predicate partitions the arguments of a call into a list of input
% variables and a list of output variables,

:- pred partition_call_args(module_info::in, list(mode)::in, list(prog_var)::in,
	bag(prog_var)::out, bag(prog_var)::out) is det.

% Given a list of variables from a unification, this predicate divides the
% list into a bag of input variables, and a bag of output variables.

:- pred split_unification_vars(list(prog_var)::in, list(uni_mode)::in,
	module_info::in, bag(prog_var)::out, bag(prog_var)::out) is det.

%  Used to create lists of boolean values, which are used for used_args.
%  make_bool_list(HeadVars, BoolIn, BoolOut) creates a bool list which is
%  (length(HeadVars) - length(BoolIn)) `no' followed by BoolIn.  This is
%  used to set the used args for compiler generated predicates.  The no's
%  at the start are because the Type infos are not used. length(BoolIn)
%  should equal the arity of the predicate, and the difference in length
%  between the arity of the procedure and the arity of the predicate is
%  the number of type infos.

:- pred term_util__make_bool_list(list(_T)::in, list(bool)::in,
	list(bool)::out) is det.

% Removes variables from the InVarBag that are not used in the call.
% remove_unused_args(InVarBag0, VarList, BoolList, InVarBag)
% VarList and BoolList are corresponding lists.  Any variable in VarList
% that has a `no' in the corresponding place in the BoolList is removed
% from InVarBag.

:- pred remove_unused_args(bag(prog_var), list(prog_var), list(bool),
		bag(prog_var)).
:- mode remove_unused_args(in, in, in, out) is det.

% This predicate sets the argument size info of a given a list of procedures.

:- pred set_pred_proc_ids_arg_size_info(list(pred_proc_id)::in,
	arg_size_info::in, module_info::in, module_info::out) is det.

% This predicate sets the termination info of a given a list of procedures.

:- pred set_pred_proc_ids_termination_info(list(pred_proc_id)::in,
	termination_info::in, module_info::in, module_info::out) is det.

:- pred lookup_proc_termination_info(module_info::in, pred_proc_id::in,
	maybe(termination_info)::out) is det.

:- pred lookup_proc_arg_size_info(module_info::in, pred_proc_id::in,
	maybe(arg_size_info)::out) is det.

% Succeeds if one or more variables in the list are higher order.

:- pred horder_vars(list(prog_var), map(prog_var, type)).
:- mode horder_vars(in, in) is semidet.

% Succeeds if all values of the given type are zero size (for all norms).

:- pred zero_size_type(type, module_info).
:- mode zero_size_type(in, in) is semidet.

:- pred get_context_from_scc(list(pred_proc_id)::in, module_info::in,
	prog_context::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module inst_match, prog_out, mode_util, type_util.
:- import_module globals, options.

:- import_module assoc_list, require.
:- import_module rat, lp_rational.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

% Equation-handling predicates:

rename_vars(Vars, RenamedVars, VarToSizeVarMap) :-
	Rename_Var = lambda([Var::in, SizeVar::out] is det, (
		rename_var(Var, SizeVar, VarToSizeVarMap)
	)),
	list__map(Rename_Var, Vars, RenamedVars).


rename_var(Var, SizeVar, VarToSizeVarMap) :-
	(bimap__search(VarToSizeVarMap, Var, SizeVar0) ->
		SizeVar = SizeVar0
	;
		error("term_util: tried to rename a variable not in map")
	).

remove_zero_vars(Zeros, Equations0, Equations) :-
	Simplify_eqns = lambda([Eqn::in, Eqns0::in, Eqns::out] is det, (
		Eqn = eqn(Coeffs0, Op, Const),
		simplify_coeffs(Zeros, Coeffs0, Coeffs),
		( 	Coeffs = [],
			Const \= zero
		->
			error("term_util: Illegal equation.")
		;
			Coeffs = []
		->
			Eqns = Eqns0
		;
			Eqns = [eqn(Coeffs, Op, Const)|Eqns0]
		)
	)),
	list__foldl(Simplify_eqns, Equations0, [], Equations).
			


:- pred simplify_coeffs(set(size_var), list(coeff), list(coeff)).
:- mode simplify_coeffs(in, in, out) is det.
simplify_coeffs(_, [], []). 
simplify_coeffs(Zeros, [Var0-Rat0|Coeffs0], Coeffs) :-
	( set__member(Var0, Zeros) ->
		simplify_coeffs(Zeros, Coeffs0, Coeffs)
	;
		simplify_coeffs(Zeros, Coeffs0, Coeffs1),
		Coeffs = [Var0-Rat0 | Coeffs1]
	).
	

find_zero_size_vars(Module, VarToSizeVarMap, VarTypes, Zeros) :-
	Is_zero = lambda([VarA::in] is semidet, (
		lookup(VarTypes, VarA, Type), 
		zero_size_type(Type, Module)
	)),
	bimap__ordinates(VarToSizeVarMap, Vars),
	list__filter(Is_zero, Vars, ZeroVars),

	% Build Zeros from corresponding size_vars
	VarToSize = lambda([VarB::in, SizeVar::out] is det, (
		lookup(VarToSizeVarMap, VarB, SizeVar)
	)),
	list__map(VarToSize, ZeroVars, ZerosList),
	list_to_set(ZerosList, Zeros).
						  

% If Eqn1 is implied by Eqn2, then the result is '>'.  Otherwise, order
% is determined by compare_var_lists, for which any two equations with the
% same variables are 'equal'.
compare_eqns(Eqn1, Eqn2, Result) :-
	(
		Eqn1 = eqn(Coeffs1, (=<), _Const1),
                Eqn2 = eqn(Coeffs2, (=<), _Const2)
        ->
		( Eqn1 = Eqn2 ->
			Result = (=)
		;
			( 
				fm_standardize_equations([Eqn1, Eqn2], 
					[Std1, Std2]),
				eqns_to_vectors([Std1], [Vec1]),
				eqns_to_vectors([Std2], [Vec2]),
				implied_eqn(Vec1, Vec2) 
			->

				Result = (>)
			;
				compare_var_lists(Coeffs1, Coeffs2, Result1),
				( Result1 = (=) ->
					compare_rat_lists(Coeffs1, Coeffs2, 
									Result)
				;
					Result = Result1
				)
			)
		)
	;
		error("term_util: Non-canonical equation passed to 
								compare_eqns\n")
	).

% lexicographic order on list of vars.
compare_var_lists([], [], (=)).
compare_var_lists([], [_|_], (<)).
compare_var_lists([_|_], [], (>)).
compare_var_lists([C1|Coeffs1], [C2|Coeffs2], Result) :-
	compare_vars(C1, C2, Coeff_Result),
	( Coeff_Result = (=) ->
		compare_var_lists(Coeffs1, Coeffs2, Result)
	;
		Result = Coeff_Result
	).


:- pred compare_vars(coeff, coeff, comparison_result).
:- mode compare_vars(in, in, uo) is det.
compare_vars(Var1-_, Var2-_, Result) :-
	compare(Result, Var1, Var2).

% lexicographic order on list of rats.
compare_rat_lists([], [], (=)).
compare_rat_lists([], [_|_], (<)).
compare_rat_lists([_|_], [], (>)).
compare_rat_lists([C1|Coeffs1], [C2|Coeffs2], Result) :-
	compare_rats(C1, C2, Rat_Result),
	( Rat_Result = (=) ->
		compare_rat_lists(Coeffs1, Coeffs2, Result)
	;
		Result = Rat_Result
	).


:- pred compare_rats(coeff, coeff, comparison_result).
:- mode compare_rats(in, in, uo) is det.
compare_rats(_-Rat1, _-Rat2, Result) :-
	( rat:'<'(Rat1, Rat2) ->
		Result = (>)
	;
		( rat:'>'(Rat1, Rat2) ->
			Result = (<)
		;
			Result = (=)
		)
	).

% Outputs an equation with coefficients sorted in increasing order on variable.
% These are normalised on the smallest variable (i.e. multiplied by a constant
% so that that variable has coefficient 1 or -1), which ends up as the first
% variable in the list of coefficients.
canonical_form(Eqns0, Canonical_eqns) :-
        fm_standardize_equations(Eqns0, Standardized_eqns),
        eqns_to_vectors(Standardized_eqns, Vectors),

	%XXX I think the fact that this is normalised on smallest var is
	% never used.
        Normalize_on_smallest_var = lambda([Vec1::in, Norm_vec::out] is det,(
                Vec1 = Map0-_,
		( map__remove_smallest(Map0, LeastVar, _, _) ->
			normalize_vector(Vec1, LeastVar, Norm_vec)
		;
			error("term_util:Can't normalise null vector\n")

		)
	)),
	list__map(Normalize_on_smallest_var, Vectors, Canonical_vecs),

	vectors_to_eqns(Canonical_vecs, Almost_canonical_eqns),

	Sort_vars = lambda([eqn(Coeffs, Op, Num)::in, Sort_eqn::out] is det, (
		list__sort(compare_vars, Coeffs, Sorted_coeffs),
		Sort_eqn = eqn(Sorted_coeffs, Op, Num)
	)),
	list__map(Sort_vars, Almost_canonical_eqns, Canonical_eqns).

	
remove_redundant_eqns(Eqns0, Eqns) :-
	fm_standardize_equations(Eqns0, StdEqns),
	eqns_to_vectors(StdEqns, Vectors0),
	remove_redundant_eqns2(Vectors0, Vectors1),
	vectors_to_eqns(Vectors1, Eqns1),
	list__sort(compare_eqns, Eqns1, Eqns).


% The non-redundant equations have the property that, for any particular
% equation in the list, there is no other equation in the list that
% implies it or is implied by it.
% They _don't_ have the property that no equation is implied by any set
% of the other equations - only pairwise implication is considered.
:- pred remove_redundant_eqns2(list(vector), list(vector)).
:- mode remove_redundant_eqns2(in, out) is det.

remove_redundant_eqns2([], []).
remove_redundant_eqns2([Eqn1|Eqns], Non_redundant_eqns) :-
	remove_comparable_eqns(Eqn1, Strongest_eqn, Eqns, Filtered_eqns0),
	remove_redundant_eqns2(Filtered_eqns0, Non_redundant_eqns0),
	Non_redundant_eqns = [Strongest_eqn | Non_redundant_eqns0].


% remove_comparable_eqns(Eqn, Strongest_eqn, Eqns0, Eqns).
% Strongest_eqn is an equation implying all other equations
% implied by Eqn, such that there are no other equations in Eqns0
% that imply Strongest_eqn (Note that this isn't necessarily unique, 
% but that doesn't matter). 
% This removes all equations implied by Strongest_eqn (including
% Strongest_eqn itself) from Eqns0.
% It makes a special case of "non-negative" equations, i.e. those of the
% form "x >= 0".  They have to be kept unless there is also an equation
% "x >= a" where a > 0.

:- pred remove_comparable_eqns(vector, vector, list(vector), list(vector)).
:- mode remove_comparable_eqns(in, out, in, out) is det.
remove_comparable_eqns(Eqn, Eqn, [], []). 
remove_comparable_eqns(Eqn, Strongest_eqn, [Eqn0|Eqns0], Filtered_eqns) :-
	( 	implied_eqn(Eqn0, Eqn), 
		\+ non_redundant_nonneg(Eqn0, Eqn)
	->
		remove_comparable_eqns(Eqn, Strongest_eqn, Eqns0, Filtered_eqns)
	;
		( 
			implied_eqn(Eqn, Eqn0),
			\+ non_redundant_nonneg(Eqn, Eqn0)
		->
			remove_comparable_eqns(Eqn0, Strongest_eqn, Eqns0,
								Filtered_eqns)
		;
			remove_comparable_eqns(Eqn, Strongest_eqn, Eqns0,
								Filtered_eqns1),
			Filtered_eqns = [Eqn0|Filtered_eqns1]
		)
	).
	


% implied_eqn(Eqn1, Eqn2): 
% Succeeds if Eqn1 is implied by Eqn2.  Assumes that both are in canonical
% form.
% The implication is only correct under the additional assumption that 
% all the variables are non-negative.
% There are some implied equations that won't be caught, i.e. those where
% Eqn1 contains a proper subset or superset of the variables in Eqn2
% (e.g. x + y <= 3 implies x <= 3). 
:- pred implied_eqn(vector, vector).
:- mode implied_eqn(in, in) is semidet.
implied_eqn(CoeffMap1-Rat1, CoeffMap2-Rat2) :-
	map__sorted_keys(CoeffMap1, SortedVars1),
	map__sorted_keys(CoeffMap2, SortedVars2),
	SortedVars1 = SortedVars2,
	implied_eqn2(SortedVars1, CoeffMap1-Rat1, CoeffMap2-Rat2).

:- pred implied_eqn2(list(size_var), vector, vector).
:- mode implied_eqn2(in, in, in) is semidet.
implied_eqn2([], _, _) :-
	fail.

implied_eqn2([Var|Vars], Vec1, Vec2) :-
	(
		normalize_vector(Vec1, Var, NormedMap1-NormedRat1),
		map__to_sorted_assoc_list(NormedMap1, Coeff_list1),

		normalize_vector(Vec2, Var, NormedMap2-NormedRat2),
		map__to_sorted_assoc_list(NormedMap2, Coeff_list2),

		\+ any_larger_coeffs(Coeff_list1, Coeff_list2),
		rat:'>='(NormedRat1, NormedRat2)
	;
		implied_eqn2(Vars, Vec1, Vec2)
	).


% Succeeds if any of the coefficients in the first list are larger than
% the corresponding one in the second list. (e.g. 2x is larger than 1x and
% -3x is larger than -4x).
:- pred any_larger_coeffs(list(coeff), list(coeff)).
:- mode any_larger_coeffs(in, in) is semidet.

any_larger_coeffs([], []) :-
	fail.
any_larger_coeffs([_|_], []) :-
	error("term_util: unequal length coefficient lists in
		any_larger_coeffs").
any_larger_coeffs([], [_|_]) :-
	error("term_util: unequal length coefficient lists in
		any_larger_coeffs").
any_larger_coeffs([Var1-Rat1 | Coeffs1], [Var2-Rat2 | Coeffs2]) :-
	Var1 = Var2, 
	(	
		rat:'>'(Rat1, Rat2)
	;
		any_larger_coeffs(Coeffs1, Coeffs2)
	).

% obvious_eqn: Succeeds iff the equation is implied by the
% assumption that all variables are non-negative.
:- pred obvious_eqn(equation).
:- mode obvious_eqn(in) is semidet.

obvious_eqn(eqn(Coeffs, (=<), Rat)) :-
	list__length(Coeffs, Length),
	Length >= 2,
	rat:'>='(Rat, zero),
	all_negative(Coeffs).

:- pred all_negative(list(coeff)).
:- mode all_negative(in) is semidet.
all_negative([]).
all_negative([_-Rat | Coeffs] ) :-
	rat:'<'(Rat, zero),
	all_negative(Coeffs).

% non_redundant_nonneg(Maybe_nonneg, Maybe_stronger): Succeeds if 
% Maybe_nonneg is of the form "-x =< b", and 
% Maybe_stronger is not of the form " -x =< a" where a =< b. 
% This assumes that both equations are in canonical form, i.e. all the
% inequalities are "=<".
:- pred non_redundant_nonneg(vector, vector).
:- mode non_redundant_nonneg(in, in) is semidet.

non_redundant_nonneg(Map1-Const1, Map2-Const2) :-
	map__values(Map1, [Rat1]),
	map__keys(Map1, [SVar]),
	rat:'<'(Rat1, zero),
	
	\+ ( 
		map__values(Map2, [Rat2]),
		map__keys(Map2, [SVar]),
		rat:'<'(Rat2, zero),
		rat:'=<'(Const1, Const2)
	).

%-----------------------------------------------------------------------------%
% Calculate the weight to be assigned to each function symbol for the
% use_map and use_map_and_args semilinear norms.
%
% Given a type definition such as
%
% :- type t(Tk)	--->	f1(a11, ... a1n1)	where n1 is the arity of f1
%		;	...
%		;	fm(am1, ... amnm)	where nm is the arity of fm
%
% we check, for each aij, whether its type is recursive (i.e. it is t with
% type variable arguments that are a permutation of Tk). The weight info
% we compute for each functor will have a boolean list that has a `yes'
% for each recursive argument and a `no' for each nonrecursive argument.
% The weight to be assigned to the functor is the number of nonrecursive
% arguments, except that we assign a weight of at least 1 to all functors
% which are not constants.

find_weights(ModuleInfo, Weights) :-
	module_info_types(ModuleInfo, TypeTable),
	map__to_assoc_list(TypeTable, TypeList),
	map__init(Weights0),
	find_weights_for_type_list(TypeList, Weights0, Weights).

:- pred find_weights_for_type_list(assoc_list(type_id, hlds_type_defn)::in,
	weight_table::in, weight_table::out) is det.

find_weights_for_type_list([], Weights, Weights).
find_weights_for_type_list([TypeId - TypeDefn | TypeList], Weights0, Weights) :-
	find_weights_for_type(TypeId, TypeDefn, Weights0, Weights1),
	find_weights_for_type_list(TypeList, Weights1, Weights).

:- pred find_weights_for_type(type_id::in, hlds_type_defn::in,
	weight_table::in, weight_table::out) is det.

find_weights_for_type(TypeId, TypeDefn, Weights0, Weights) :-
	hlds_data__get_type_defn_body(TypeDefn, TypeBody),
	(
		TypeBody = du_type(Constructors, _, _, _),
		hlds_data__get_type_defn_tparams(TypeDefn, TypeParams),
		find_weights_for_cons_list(Constructors, TypeId, TypeParams,
			Weights0, Weights)
	;
		TypeBody = uu_type(_),
		error("undiscriminated union types not yet implemented")
	;
		% This type does not introduce any functors
		TypeBody = eqv_type(_),
		Weights = Weights0
	;
		% This type may introduce some functors,
		% but we will never see them in this analysis
		TypeBody = abstract_type,
		Weights = Weights0
	).

:- pred find_weights_for_cons_list(list(constructor)::in,
	type_id::in, list(type_param)::in,
	weight_table::in, weight_table::out) is det.

find_weights_for_cons_list([], _, _, Weights, Weights).
find_weights_for_cons_list([Constructor | Constructors], TypeId, Params,
		Weights0, Weights) :-
	find_weights_for_cons(Constructor, TypeId, Params, Weights0, Weights1),
	find_weights_for_cons_list(Constructors, TypeId, Params,
		Weights1, Weights).

:- pred find_weights_for_cons(constructor::in,
	type_id::in, list(type_param)::in,
	weight_table::in, weight_table::out) is det.

find_weights_for_cons(Ctor, TypeId, Params, Weights0, Weights) :-
	% XXX should we do something about ExistQVars here?
 	Ctor = ctor(_ExistQVars, _Constraints, SymName, Args),
	list__length(Args, Arity),
	( Arity > 0 ->
		find_and_count_nonrec_args(Args, TypeId, Params,
			NumNonRec, ArgInfos0),
		( NumNonRec = 0 ->
			Weight = 1,
			list__duplicate(Arity, yes, ArgInfos)
		;
			Weight = NumNonRec,
			ArgInfos = ArgInfos0
		),
		WeightInfo = weight(Weight, ArgInfos)
	;
		WeightInfo = weight(0, [])
	),
	ConsId = cons(SymName, Arity),
	map__det_insert(Weights0, TypeId - ConsId, WeightInfo, Weights).

:- pred find_and_count_nonrec_args(list(constructor_arg)::in,
	type_id::in, list(type_param)::in,
	int::out, list(bool)::out) is det.

find_and_count_nonrec_args([], _, _, 0, []).
find_and_count_nonrec_args([Arg | Args], Id, Params, NonRecArgs, ArgInfo) :-
	find_and_count_nonrec_args(Args, Id, Params, NonRecArgs0, ArgInfo0),
	( is_arg_recursive(Arg, Id, Params) ->
		NonRecArgs = NonRecArgs0,
		ArgInfo = [yes | ArgInfo0]
	;
		NonRecArgs is NonRecArgs0 + 1,
		ArgInfo = [no | ArgInfo0]
	).

:- pred is_arg_recursive(constructor_arg::in,
	type_id::in, list(type_param)::in) is semidet.

is_arg_recursive(Arg, Id, Params) :-
	Arg = _Name - ArgType,
	type_to_type_id(ArgType, ArgTypeId, ArgTypeParams),
	Id = ArgTypeId,
	list__perm(Params, ArgTypeParams).

%-----------------------------------------------------------------------------%

% Although the module info is not used in either of these norms, it could
% be needed for other norms, so it should not be removed.

functor_norm(simple, _, ConsId, _, Int, Args, Args, Modes, Modes) :-
	(
		ConsId = cons(_, Arity),
		Arity \= 0
	->
		Int = 1
	;
		Int = 0
	).
functor_norm(total, _, ConsId, _Module, Int, Args, Args, Modes, Modes) :-
	( ConsId = cons(_, Arity) ->
		Int = Arity
	;
		Int = 0
	).
functor_norm(use_map(WeightMap), TypeId, ConsId, _Module, Int,
		Args, Args, Modes, Modes) :-
	( map__search(WeightMap, TypeId - ConsId, WeightInfo) ->
		WeightInfo = weight(Int, _)
	;
		Int = 0
	).
functor_norm(use_map_and_args(WeightMap), TypeId, ConsId, _Module, Int,
		Args0, Args, Modes0, Modes) :-
	( map__search(WeightMap, TypeId - ConsId, WeightInfo) ->
		WeightInfo = weight(Int, UseArgList),
		(
			functor_norm_filter_args(UseArgList, Args0, Args1,
				Modes0, Modes1)
		->
			Modes = Modes1,
			Args = Args1
		;
			error("Unmatched lists in functor_norm_filter_args.")
		)
	;
		Int = 0,
		Modes = Modes0,
		Args = Args0
	).

% This predicate will fail if the length of the input lists are not matched.

:- pred functor_norm_filter_args(list(bool), list(prog_var), list(prog_var),
	list(uni_mode), list(uni_mode)).
:- mode functor_norm_filter_args(in, in, out, in, out) is semidet.

functor_norm_filter_args([], [], [], [], []).
functor_norm_filter_args([yes | Bools], [Arg0 | Args0], [Arg0 | Args],
		[Mode0 | Modes0], [Mode0 | Modes]) :-
	functor_norm_filter_args(Bools, Args0, Args, Modes0, Modes).
functor_norm_filter_args([no | Bools], [_Arg0 | Args0], Args,
		[_Mode0 | Modes0], Modes) :-
	functor_norm_filter_args(Bools, Args0, Args, Modes0, Modes).

%-----------------------------------------------------------------------------%

partition_call_args(Module, ArgModes, Args, InVarsBag, OutVarsBag) :-
	partition_call_args_2(Module, ArgModes, Args, InVars, OutVars),
	bag__from_list(InVars, InVarsBag),
	bag__from_list(OutVars, OutVarsBag).

:- pred partition_call_args_2(module_info::in, list(mode)::in,
	list(prog_var)::in, list(prog_var)::out, list(prog_var)::out) is det.

partition_call_args_2(_, [], [], [], []).
partition_call_args_2(_, [], [_ | _], _, _) :-
	error("Unmatched variables in term_util:partition_call_args").
partition_call_args_2(_, [_ | _], [], _, _) :-
	error("Unmatched variables in term_util__partition_call_args").
partition_call_args_2(ModuleInfo, [ArgMode | ArgModes], [Arg | Args],
		InputArgs, OutputArgs) :-
	partition_call_args_2(ModuleInfo, ArgModes, Args,
		InputArgs1, OutputArgs1),
	( mode_is_input(ModuleInfo, ArgMode) ->
		InputArgs = [Arg | InputArgs1],
		OutputArgs = OutputArgs1
	; mode_is_output(ModuleInfo, ArgMode) ->
		InputArgs = InputArgs1,
		OutputArgs = [Arg | OutputArgs1]
	;
		InputArgs = InputArgs1,
		OutputArgs = OutputArgs1
	).

% For these next two predicates (split_unification_vars and
% partition_call_args) there is a problem of what needs to be done for
% partially instantiated data structures.  The correct answer is that the
% system shoud use a norm such that the size of the uninstantiated parts of
% a partially instantiated structure have no effect on the size of the data
% structure according to the norm.  For example when finding the size of a
% list-skeleton, list-length norm should be used.  Therefore, the size of
% any term must be given by
% sizeof(term) = constant + sum of the size of each
% 			(possibly partly) instantiated subterm.
% It is probably easiest to implement this by modifying term_weights.
% The current implementation does not correctly handle partially
% instantiated data structures.

split_unification_vars([], Modes, _ModuleInfo, Vars, Vars) :-
	bag__init(Vars),
	( Modes = [] ->
		true
	;
		error("term_util:split_unification_vars: Unmatched Variables")
	).
split_unification_vars([Arg | Args], Modes, ModuleInfo,
		InVars, OutVars):-
	( Modes = [UniMode | UniModes] ->
		split_unification_vars(Args, UniModes, ModuleInfo,
			InVars0, OutVars0),
		UniMode = ((_VarInit - ArgInit) -> (_VarFinal - ArgFinal)),
		( % if
			inst_is_bound(ModuleInfo, ArgInit)
		->
			% Variable is an input variable
			bag__insert(InVars0, Arg, InVars),
			OutVars = OutVars0
		; % else if
			inst_is_free(ModuleInfo, ArgInit),
			inst_is_bound(ModuleInfo, ArgFinal)
		->
			% Variable is an output variable
			InVars = InVars0,
			bag__insert(OutVars0, Arg, OutVars)
		; % else
			InVars = InVars0,
			OutVars = OutVars0
		)
	;
		error("term_util__split_unification_vars: Unmatched Variables")
	).

%-----------------------------------------------------------------------------%

term_util__make_bool_list(HeadVars0, Bools, Out) :-
	list__length(Bools, Arity),
	( list__drop(Arity, HeadVars0, HeadVars1) ->
		HeadVars = HeadVars1
	;
		error("Unmatched variables in term_util:make_bool_list")
	),
	term_util__make_bool_list_2(HeadVars, Bools, Out).

:- pred term_util__make_bool_list_2(list(_T), list(bool), list(bool)).
:- mode term_util__make_bool_list_2(in, in, out) is det.

term_util__make_bool_list_2([], Bools, Bools).
term_util__make_bool_list_2([ _ | Vars ], Bools, [no | Out]) :-
	term_util__make_bool_list_2(Vars, Bools, Out).

remove_unused_args(Vars, [], [], Vars).
remove_unused_args(Vars, [], [_X | _Xs], Vars) :-
	error("Unmatched variables in term_util:remove_unused_args").
remove_unused_args(Vars, [_X | _Xs], [], Vars) :-
	error("Unmatched variables in term_util__remove_unused_args").
remove_unused_args(Vars0, [ Arg | Args ], [ UsedVar | UsedVars ], Vars) :-
	( UsedVar = yes ->
		% The variable is used, so leave it
		remove_unused_args(Vars0, Args, UsedVars, Vars)
	;
		% The variable is not used in producing output vars, so
		% dont include it as an input variable.
		bag__delete(Vars0, Arg, Vars1),
		remove_unused_args(Vars1, Args, UsedVars, Vars)
	).

%-----------------------------------------------------------------------------%

set_pred_proc_ids_arg_size_info([], _ArgSize, Module, Module).
set_pred_proc_ids_arg_size_info([PPId | PPIds], ArgSize, Module0, Module) :-
	PPId = proc(PredId, ProcId),
	module_info_preds(Module0, PredTable0),
	map__lookup(PredTable0, PredId, PredInfo0),
	pred_info_procedures(PredInfo0, ProcTable0),
	map__lookup(ProcTable0, ProcId, ProcInfo0),

	proc_info_set_maybe_arg_size_info(ProcInfo0, yes(ArgSize), ProcInfo),

	map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable),
	pred_info_set_procedures(PredInfo0, ProcTable, PredInfo),
	map__det_update(PredTable0, PredId, PredInfo, PredTable),
	module_info_set_preds(Module0, PredTable, Module1),
	set_pred_proc_ids_arg_size_info(PPIds, ArgSize, Module1, Module).

set_pred_proc_ids_termination_info([], _Termination, Module, Module).
set_pred_proc_ids_termination_info([PPId | PPIds], Termination,
		Module0, Module) :-
	PPId = proc(PredId, ProcId),
	module_info_preds(Module0, PredTable0),
	map__lookup(PredTable0, PredId, PredInfo0),
	pred_info_procedures(PredInfo0, ProcTable0),
	map__lookup(ProcTable0, ProcId, ProcInfo0),

	proc_info_set_maybe_termination_info(ProcInfo0, yes(Termination),
		ProcInfo),

	map__det_update(ProcTable0, ProcId, ProcInfo, ProcTable),
	pred_info_set_procedures(PredInfo0, ProcTable, PredInfo),
	map__det_update(PredTable0, PredId, PredInfo, PredTable),
	module_info_set_preds(Module0, PredTable, Module1),
	set_pred_proc_ids_termination_info(PPIds, Termination,
		Module1, Module).

lookup_proc_termination_info(Module, PredProcId, MaybeTermination) :-
	PredProcId = proc(PredId, ProcId),
	module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo),
	proc_info_get_maybe_termination_info(ProcInfo, MaybeTermination).

lookup_proc_arg_size_info(Module, PredProcId, MaybeArgSize) :-
	PredProcId = proc(PredId, ProcId),
	module_info_pred_proc_info(Module, PredId, ProcId, _, ProcInfo),
	proc_info_get_maybe_arg_size_info(ProcInfo, MaybeArgSize).

horder_vars([Arg | Args], VarType) :-
	(
		map__lookup(VarType, Arg, Type),
		type_is_higher_order(Type, _, _)
	;
		horder_vars(Args, VarType)
	).

zero_size_type(Type, Module) :-
	classify_type(Type, Module, TypeCategory),
	zero_size_type_category(TypeCategory, Type, Module, yes).

:- pred zero_size_type_category(builtin_type, type, module_info, bool).
:- mode zero_size_type_category(in, in, in, out) is det.

zero_size_type_category(int_type, _, _, yes).
zero_size_type_category(char_type, _, _, yes).
zero_size_type_category(str_type, _, _, yes).
zero_size_type_category(float_type, _, _, yes).
zero_size_type_category(pred_type, _, _, no).
zero_size_type_category(enum_type, _, _, yes).
zero_size_type_category(polymorphic_type, _, _, no).
zero_size_type_category(user_type, _, _, no).

%-----------------------------------------------------------------------------%

get_context_from_scc(SCC, Module, Context) :-
	( SCC = [proc(PredId, _) | _] ->
		module_info_pred_info(Module, PredId, PredInfo),
		pred_info_context(PredInfo, Context)
	;
		error("Empty SCC in pass 2 of termination analysis")
	).

%-----------------------------------------------------------------------------%
