%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% File: ml_foreign_class.m
% Main author: petdr
%
% Transform the foreign class table in the HLDS into an MLDS
% representation which exports these foreign classes.
%
%-----------------------------------------------------------------------------%

:- module ml_foreign_class.

:- interface.

:- import_module hlds_module, mlds.
:- import_module io.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred ml_foreign_class(module_info, mlds__defns, io__state, io__state).
:- mode ml_foreign_class(in, out, di, uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module code_model, hlds_data, hlds_pred.
:- import_module ml_call_gen, ml_code_util, prog_data, type_util.
:- import_module int, list, map, require, std_util, term.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

ml_foreign_class(ModuleInfo, Defns) -->
	{ module_info_foreign_classes(ModuleInfo, ForeignClasses) },
	{ Defns = list__map(
			ml_foreign_class_defn(ModuleInfo),
			map__values(ForeignClasses)) }.

:- func ml_foreign_class_defn(module_info, foreign_class_defn) = mlds__defn.

ml_foreign_class_defn(ModuleInfo, ForeignClassDefn)
	= mlds__defn(Name, Context, DeclFlags, Defn) :-
	Name = export(ForeignClassDefn ^ foreign_name),
	Context = mlds__make_context(ForeignClassDefn ^ context),
	DeclFlags = init_decl_flags(public, per_instance, non_virtual,
			overridable, modifiable, concrete),
	Defn = mlds__class(gen_class_defn(ModuleInfo, ForeignClassDefn)).

:- func gen_class_defn(module_info, foreign_class_defn) = mlds__class_defn.

gen_class_defn(ModuleInfo, ForeignClass)
	= mlds__class_defn(Kind, Imports,
			Inherits, Implements, Ctors, Members) :-
	Kind = mlds__class,
	Imports = [],

	Inherits = [foreign_type_to_inherit_from(ModuleInfo, ForeignClass)],

	Implements = [],
	Ctors = list__map(construct_ctor(ModuleInfo, ForeignClass),
			ForeignClass ^ constructors),
	Members = [internal_state_of_class(ModuleInfo, ForeignClass) |
			construct_methods(ModuleInfo, ForeignClass)].

%-----------------------------------------------------------------------------%

:- func foreign_type_to_inherit_from(module_info,
		foreign_class_defn) = mlds__type.

foreign_type_to_inherit_from(ModuleInfo, ForeignClass) = ForeignType :-
	(
		superclass(ModuleInfo, class_id(ForeignClass ^ (instance), 1),
				SuperClassId)
	->
			% We need to find the type of the instance of
			% the parent which is defined as a foreign type
			% or foreign class.
		module_info_instances(ModuleInfo, InstanceTable),
		map__lookup(InstanceTable, SuperClassId, Instances),
		list__filter_map((pred(ID::in, MLDS_Type::out) is semidet :-
				ID = hlds_instance_defn(_, _, _, _,
						[Type], _, _, _, _),
				type_is_foreign_type(ModuleInfo, Type),
				MLDS_Type = mercury_type_to_mlds_type(
						ModuleInfo, Type)
			), Instances, PossibleForeignTypes),
		( PossibleForeignTypes = [ForeignType0] ->
			ForeignType = ForeignType0
		;
			error("more then one superclass instance is a foreign_type for pragma foreign_class.")
			
		)
	;
		error("more then one superclass for pragma foreign_class.")
	).

:- pred superclass(module_info::in,
		hlds_data__class_id::in, hlds_data__class_id::out) is semidet.

superclass(ModuleInfo, ClassId, SuperClassId) :-
	module_info_classes(ModuleInfo, Classes),
	map__lookup(Classes, ClassId, ClassDefn),
	ClassDefn = hlds_class_defn(_, SuperClasses, _, _, _, _, _),
	SuperClasses = [SuperClass],
	SuperClass = constraint(Name, Args),
	SuperClassId = class_id(Name, list__length(Args)).

:- func get_instance_defn(module_info, hlds_data__class_id) =
		hlds_instance_defn.

get_instance_defn(ModuleInfo, ClassId) = InstanceDefn :-
	module_info_instances(ModuleInfo, InstanceTable),
	map__lookup(InstanceTable, ClassId, Instances),
	list__filter((pred(ID::in) is semidet :-
			ID = hlds_instance_defn(_, _, _, _, [Type], _, _, _, _),
			type_is_foreign_type(ModuleInfo, Type)
		), Instances, PossibleInstances),
	( PossibleInstances = [InstanceDefn0] ->
		InstanceDefn = InstanceDefn0
	;
		error("more then one instance is defined using a foreign_type.")
	).

	

:- pred type_is_foreign_type(module_info::in, prog_data__type::in) is semidet.

type_is_foreign_type(ModuleInfo, Type) :-
	module_info_types(ModuleInfo, Types),
	type_to_type_id(Type, TypeId, _),
	map__search(Types, TypeId, TypeDefn),
	hlds_data__get_type_defn_body(TypeDefn, Body),
	Body = foreign_type(_, _).

%-----------------------------------------------------------------------------%

:- func internal_state_of_class(module_info, foreign_class_defn) = mlds__defn.

internal_state_of_class(ModuleInfo, ForeignClass)
	= mlds__defn(data(var(mlds__var_name("state", no))),
			mlds__make_context(ForeignClass ^ context),
			DeclFlags, Entity) :-
	DeclFlags = init_decl_flags(private, per_instance, non_virtual,
			overridable, modifiable, concrete),
	Entity = mlds__data(
			mercury_type_to_mlds_type(ModuleInfo,
					ForeignClass ^ (type)),
			no_initializer
		).
	
%-----------------------------------------------------------------------------%

:- func construct_ctor(module_info, foreign_class_defn, pred_id) = mlds__defn.

construct_ctor(ModuleInfo, ForeignClass, PredId)
	= mlds__defn(EntityName, Context, DeclFlags, EntityDefn) :-

	module_info_pred_info(ModuleInfo, PredId, PredInfo),
	pred_info_procids(PredInfo, ProcIds),

	(
		ProcIds = [ProcId0],
		pred_info_get_is_pred_or_func(PredInfo, function)
	->
		ProcId = ProcId0
	;
			% XXX
		error("construct_ctor: more then one proc_id or not func.")
	),

	EntityName = export("This a constructor it has no Name!"),
	Context = mlds__make_context(ForeignClass ^ context),

	DeclFlags = init_decl_flags(public, per_instance, non_virtual,
			overridable, modifiable, concrete),

		% Discard the return types.
	Params0 = ml_gen_proc_params(ModuleInfo, PredId, ProcId),
	Params0 = mlds__func_params(Args, _RetTypes),
	Params = mlds__func_params(Args, []),

	Stmt = construct_ctor_body(ModuleInfo, ForeignClass, PredId, ProcId),

	EntityDefn = mlds__function(no, Params, yes(Stmt), []).

:- func construct_ctor_body(module_info, foreign_class_defn, pred_id,
		proc_id) = mlds__statement.

construct_ctor_body(ModuleInfo, ForeignClass, PredId, ProcId) = Stmt :-

		% Compute the function signature
	Params = ml_gen_proc_params(ModuleInfo, PredId, ProcId),
	Signature = mlds__get_func_signature(Params),

		% Compute the function address
	FunctionToCall = ml_gen_proc_addr_rval(ModuleInfo, PredId, ProcId),

		% Compute the lval which refers to the internal state of
		% the object.
	Lval = state_lval(ModuleInfo, ForeignClass),

		% Set the arguments up
	Params = mlds__func_params(Args, _),
	module_info_name(ModuleInfo, Name),
	MLDS_Name = mercury_module_name_to_mlds(Name),
	Rvals = list__map((func(A) = R :-
			A = EntityName - Type,
			( EntityName = data(var(V)) ->
				Var = qual(MLDS_Name, V),
				R = lval(var(Var, Type))
			;
				error("rvals")
			)
		), Args),

	RetVals = [Lval],

		% XXX shouldn't this be tail_call
	IsTailCall = call,

	Call = call(Signature, FunctionToCall, no,
			Rvals, RetVals, IsTailCall),
	Context = mlds__make_context(ForeignClass ^ context),
	Stmt = mlds__statement(Call, Context).
	
%-----------------------------------------------------------------------------%

:- func construct_methods(module_info, foreign_class_defn) = mlds__defns.

construct_methods(ModuleInfo, ForeignClass) = Defns :-
	ClassId = class_id(ForeignClass ^ (instance), 1),
	ClassInterfaces = collect_hlds_class_procs(ModuleInfo,
			ForeignClass, ClassId),
	Defns = list__map(construct_method(ModuleInfo, ForeignClass),
			ClassInterfaces).

:- func collect_hlds_class_procs(module_info, foreign_class_defn,
		hlds_data__class_id) = list(hlds_class_proc).

collect_hlds_class_procs(ModuleInfo, ForeignClass, ClassId)
	= ClassInterfacesA ++ ClassInterfacesB :-
	module_info_instances(ModuleInfo, Instances),
	map__lookup(Instances, ClassId, InstanceDefns),
	list__filter((pred(ID::in) is semidet :-
			ID = hlds_instance_defn(_, local, _, _,
					[ForeignClass ^ (type)], _, _, _, _)
		), InstanceDefns, PossibleInstances),
	( PossibleInstances = [Instance] ->
		Instance = hlds_instance_defn(_, _, _, _, _, _,
				MaybeClassInterface, _, _),
		(
			MaybeClassInterface = yes(ClassInterfaces0)
		->
			ClassInterfacesA = ClassInterfaces0
		;
			error("ml_foreign_class: MaybeClassInterface")
		)
	;
		error("ml_foreign_class: more then one possible instance")
	),
	( superclass(ModuleInfo, ClassId, SuperClassId) ->
		ClassInterfacesB = collect_hlds_class_procs(ModuleInfo,
				ForeignClass, SuperClassId)
	;
		ClassInterfacesB = []
	).

:- func construct_method(module_info, foreign_class_defn,
		hlds_class_proc) = mlds__defn.

construct_method(ModuleInfo, ForeignClass, ClassProc)
	= mlds__defn(EntityName, Context, DeclFlags, EntityDefn) :-

	ClassProc = hlds_class_proc(PredId, ProcId, MaybeInstanceMethod),
	( MaybeInstanceMethod = yes(InstanceMethod) ->
		InstanceMethod = instance_method(_PredOrFunc, Name0,
				_InstanceProcDef, _Arity, _Context),
		( 
			Name0 = unqualified(Name) 
		;
			Name0 = qualified(_, Name)
		)
	;
		error("ml_foreign_class: unknown instance method.")
	),
	EntityName = export(Name),

	Context = mlds__make_context(ForeignClass ^ context),

	DeclFlags = init_decl_flags(public, per_instance, non_virtual,
			overridable, modifiable, concrete),

	Params = construct_proc_params(ModuleInfo, PredId, ProcId),
	EntityDefn = mlds__function(no, Params, yes(Stmt), []),

	Stmt = construct_method_body(ModuleInfo, ForeignClass, ClassProc).

:- func construct_proc_params(module_info, pred_id, proc_id)
		= mlds__func_params.

construct_proc_params(ModuleInfo, PredId, ProcId)
	= mlds__func_params(Args, RetTypes) :-
	Params = ml_gen_proc_params(ModuleInfo, PredId, ProcId),
	Params = mlds__func_params(Args0, RetTypes),
	Args = list__take_upto(list__length(Args0) - 2, Args0).

:- func rvals(module_info, pred_id, proc_id) = list(mlds__rval).

rvals(ModuleInfo, PredId, ProcId) = Rvals :-
	module_info_name(ModuleInfo, Name),
	MLDS_Name = mercury_module_name_to_mlds(Name),

	Params = construct_proc_params(ModuleInfo, PredId, ProcId),
	Params = mlds__func_params(Args, _RetTypes),
	Rvals = list__map((func(A) = R :-
			A = EntityName - Type,
			( EntityName = data(var(V)) ->
				Var = qual(MLDS_Name, V),
				R = lval(var(Var, Type))
			;
				error("rvals")
			)
		), Args).

:- func returns(module_info, mlds__context,
		mlds__type) = pair(mlds__lval, mlds__defn).

returns(ModuleInfo, Context, Type) = Lval - VarDefn :-
	module_info_name(ModuleInfo, Name),
	MLDS_Name = mercury_module_name_to_mlds(Name),
		% XXX what if there is more then one return value!
	VarName = var_name("return", no),
	Var = qual(MLDS_Name, VarName),

	VarDefn = ml_gen_mlds_var_decl(var(VarName), Type,
			no_initializer, Context),
	Lval = var(Var, Type).

	
:- func construct_method_body(module_info,
		foreign_class_defn, hlds_class_proc) = mlds__statement.

construct_method_body(ModuleInfo, ForeignClass, ClassProc) = Stmt :-
	ClassProc = hlds_class_proc(PredId, ProcId, _MaybeInstanceMethod),

		% Compute the function signature
	Params = ml_gen_proc_params(ModuleInfo, PredId, ProcId),
	Signature = mlds__get_func_signature(Params),

		% Compute the function address
	FunctionToCall = ml_gen_proc_addr_rval(ModuleInfo, PredId, ProcId),

	ForeignClassType = mercury_type_to_mlds_type(ModuleInfo,
			ForeignClass ^ (type)),
	ThisPtr = self(ForeignClassType),

		% Compute the lval which refers to the internal state of
		% the object.
	Lval = state_lval(ModuleInfo, ForeignClass),

		% Set the arguments up
	Args = rvals(ModuleInfo, PredId, ProcId) ++
			[lval(Lval), mem_addr(Lval)],

		% XXX Compute the return values.
	Params = mlds__func_params(_, ReturnTypes),
	Context = mlds__make_context(ForeignClass ^ context),
	Returns = list__map(returns(ModuleInfo, Context), ReturnTypes), 
	RetVals = list__map(fst, Returns),

		% XXX shouldn't this be tail_call
	IsTailCall = call,

	Call = call(Signature, FunctionToCall, yes(ThisPtr),
			Args, RetVals, IsTailCall),

	CallStmt = mlds__statement(Call, Context),
	( ReturnTypes = [] ->
		Stmt = CallStmt
	;
		ReturnRvals = list__map((func(L) = lval(L)), RetVals),
		ReturnStmt = mlds__statement(return(ReturnRvals), Context),
		Defns = list__map(snd, Returns),
		Stmt = mlds__statement(block(Defns, [CallStmt, ReturnStmt]),
				Context)
	).


	% Compute the lval which refers to the internal state of
	% the object.
:- func state_lval(module_info, foreign_class_defn) = mlds__lval.

state_lval(ModuleInfo, ForeignClass) = Lval :-
	ForeignClassType = mercury_type_to_mlds_type(ModuleInfo,
			ForeignClass ^ (type)),
	ThisPtr = self(ForeignClassType),
	CtorType = mlds__native_int_type,	% XXX
	PtrType = mlds__native_int_type,	% XXX
	module_info_name(ModuleInfo, Name),
	FieldName = qual(mercury_module_and_package_name_to_mlds(Name,
			qualified(Name, ForeignClass ^ foreign_name)),
			"state"),
	Lval = field(no, ThisPtr, named_field(FieldName, CtorType),
			ForeignClassType, PtrType).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
