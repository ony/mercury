%-----------------------------------------------------------------------------%
% Copyright (C) 2000-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_profile_run
% Main authors: nancy

:- module sr_profile_run.

:- interface.

% library modules. 
:- import_module io.

% XXX parent modules
:- import_module hlds.
% compiler modules. 
:- import_module hlds__hlds_module. 

:- pred structure_reuse_profiling(module_info::in, io__state::di, 
			io__state::uo) is det.

%-----------------------------------------------------------------------------%
:- implementation. 

:- import_module list, map, bool, std_util. 

% XXX parent modules
:- import_module libs, parse_tree.

:- import_module hlds__hlds_pred.
:- import_module libs__globals, libs__options, hlds__passes_aux.
:- import_module parse_tree__prog_out. 
:- import_module pa_alias_as.
:- import_module sr_profile, sr_data.
:- import_module hlds__hlds_goal.


structure_reuse_profiling(HLDS) -->
	globals__io_lookup_bool_option(very_verbose, Verbose), 
	maybe_write_string(Verbose, 
			"% Collecting reuse-profiling information... "), 

	{ collect_profiling_information(HLDS, Profiling) }, 
	{ module_info_name(HLDS, ModuleName) }, 
	{ prog_out__sym_name_to_string(ModuleName, ModuleNameString) }, 
	sr_profile__write_profiling(ModuleNameString, Profiling, HLDS), 
	maybe_write_string(Verbose, "done.\n"). 

:- pred collect_profiling_information(module_info::in, 
		profiling_info::out) is det.

collect_profiling_information(HLDS, Prof) :- 
	sr_profile__init(Prof0), 
	module_info_predids(HLDS, PredIds0), 
	module_info_get_special_pred_map(HLDS, Map), 
	map__values(Map, SpecialPredIds), 
	list__filter(
		pred(Id::in) is semidet :- 
		( \+ member(Id, SpecialPredIds), 
		  \+ hlds_module__pred_not_defined_in_this_module(HLDS, Id) 
		), 
		PredIds0,
		PredIds), 
	list__foldl(
		collect_profiling_information_2(HLDS), 
		PredIds, 
		Prof0,
		Prof).

:- pred collect_profiling_information_2(module_info::in, pred_id::in, 
			profiling_info::in, profiling_info::out) is det.
collect_profiling_information_2(HLDS, PredId, Prof0, Prof):- 
	module_info_pred_info(HLDS, PredId, PredInfo), 
	pred_info_import_status(PredInfo, ImportStatus), 
	pred_info_procedures(PredInfo, Procedures), 
	map__values(Procedures, ProcInfos), 
	list__foldl(
		collect_profiling_information_3(HLDS, ImportStatus),
		ProcInfos, 
		Prof0, 
		Prof).

:- pred collect_profiling_information_3(module_info::in,
			import_status::in, proc_info::in,
			profiling_info::in, profiling_info::out) is det.

collect_profiling_information_3(HLDS, ImportStatus, ProcInfo)  --> 
	% first record some info about the procedure in general... 
	{ 
		status_is_exported(ImportStatus, IsExported),

		proc_info_reuse_information(ProcInfo, ReuseInfo),
		(
			ReuseInfo = yes(List)
		->
			Reuse = yes,
			(
				List = []
			->
				UnconditionalReuse = yes,
				DefinedInModule =  yes
			;
				UnconditionalReuse = no,
				DefinedInModule = no
			)
		;
			Reuse = no, 
			UnconditionalReuse = no,
			DefinedInModule = yes
		),
		proc_info_possible_aliases(ProcInfo, PosAliases), 
		(
			PosAliases = yes(As)
		->
			(
				is_bottom(As)
			->
				AliasSize = 0, 
				BottomAlias = yes, 
				TopAlias = no
			;
				(
					is_top(As)
				->
					AliasSize = 0,
					BottomAlias = no, 
					TopAlias = yes
				;
					AliasSize = size(As),
					BottomAlias = no, 
					TopAlias = no
				)
			)
		;
			AliasSize = 0, 
			BottomAlias = no, 
			TopAlias = yes
		)
	}, 	
	% 1. if reuse procedure with conditions, then it was not defined in
	% this module initially. 
	maybe_increment([DefinedInModule], inc_procs_defined), 
	% 2. reuse procedure?
	maybe_increment([Reuse], inc_reuse_procs), 
	% 3. unconditional reuse procedure?
	maybe_increment([UnconditionalReuse], inc_uncond_reuse_procs),
	% 4. just count the proc
	inc_procs_counted,
	% 5. exported proc?
	maybe_increment([IsExported], inc_exported_procs), 
	% 6. exported reuse proc?
	maybe_increment([IsExported,Reuse], inc_exported_reuse_procs), 
	% 7. exported unconditional reuse proc? 
	maybe_increment([IsExported, UnconditionalReuse], 
			inc_exported_uncond_reuse_procs),
	% 8. aliases?
	inc_aliases(AliasSize),
	% 9. alias bottom?
	maybe_increment([BottomAlias], inc_bottom_procs), 
	% 10. alias top?
	maybe_increment([TopAlias], inc_top_procs),

	{ proc_info_goal(ProcInfo, Goal) }, 
	collect_profiling_information_4(HLDS, Goal).

:- pred collect_profiling_information_4(module_info::in, hlds_goal::in, 
		profiling_info::in, profiling_info::out) is det.

collect_profiling_information_4(HLDS, Expr - _Info, Prof0, Prof) :- 
	Expr = conj(Goals),
	list__foldl(collect_profiling_information_4(HLDS),
			Goals, Prof0, Prof). 
collect_profiling_information_4(HLDS, Expr - Info, Prof0, Prof) :- 
	Expr = call(PredId, ProcId, _, _, _, _), 
	inc_pred_calls(Prof0, Prof1),
	goal_info_get_reuse(Info, Reuse),
	(
		Reuse = reuse(ShortReuse),
		ShortReuse = reuse_call(_)
	->
		inc_reuse_calls(Prof1, Prof)
	;
		module_info_structure_reuse_info(HLDS, ReuseInfo),
		ReuseInfo = structure_reuse_info(ReuseMap),
		(
			map__contains(ReuseMap, proc(PredId, ProcId))
		->
			inc_no_reuse_calls(Prof1, Prof)
		;
			Prof = Prof1
		)
	).
collect_profiling_information_4(_HLDS, Expr - _Info, Prof, Prof) :- 
	Expr = generic_call(_, _, _, _). 
collect_profiling_information_4(HLDS, Expr - _Info, Prof0, Prof) :- 
	Expr = switch(_, _, Cases), 
	list__foldl(
		pred(C::in, P0::in, P::out) is det :-
		(	
			C = case(_, G),
			collect_profiling_information_4(HLDS, G, P0, P)
		), 
		Cases,
		Prof0, 
		Prof).
collect_profiling_information_4(_HLDS, Expr - Info, Prof0, Prof) :- 
	Expr = unify(_, _, _, Unification, _), 
	(
		Unification = deconstruct(_, _, _, _, _, _)
	-> 
		inc_deconstructs(Prof0, Prof1),
		goal_info_get_reuse(Info, Reuse), 
		(
			Reuse = reuse(ShortReuse), 
			ShortReuse = cell_died
		->
			inc_direct_reuses(Prof1, Prof)
		;
			Prof = Prof1
		)
	;
		Prof = Prof0
	).
collect_profiling_information_4(HLDS, Expr - _Info, Prof0, Prof) :- 
	Expr = disj(Goals),
	list__foldl(collect_profiling_information_4(HLDS), 
			Goals, Prof0, Prof). 
collect_profiling_information_4(HLDS, Expr - _Info, Prof0, Prof) :- 
	Expr = not(Goal), 
	collect_profiling_information_4(HLDS, Goal, Prof0, Prof). 
collect_profiling_information_4(HLDS, Expr - _Info, Prof0, Prof) :- 
	Expr = some(_, _, Goal), 
	collect_profiling_information_4(HLDS, Goal, Prof0, Prof). 
collect_profiling_information_4(HLDS, Expr - _Info, Prof0, Prof) :- 
	Expr = if_then_else(_, If, Then, Else), 
	collect_profiling_information_4(HLDS, If, Prof0, Prof1), 
	collect_profiling_information_4(HLDS, Then, Prof1, Prof2), 
	collect_profiling_information_4(HLDS, Else, Prof2, Prof). 
collect_profiling_information_4(_HLDS, Expr - _Info, Prof, Prof) :- 
	Expr = foreign_proc(_, _, _, _, _, _, _). 
collect_profiling_information_4(_HLDS, Expr - _Info, Prof, Prof) :- 
	Expr = par_conj(_).
collect_profiling_information_4(_HLDS, Expr - _Info, Prof, Prof) :- 
	Expr = shorthand(_).

		
		
:- pred maybe_increment(list(bool), pred(profiling_info, profiling_info), 
			profiling_info, profiling_info).
:- mode maybe_increment(in, pred(in, out) is det, in, out) is det.

maybe_increment(Bools, IncOp, Prof0, Prof) :- 
	bool__and_list(Bools, Result), 
	(
		Result = yes
	->
		IncOp(Prof0, Prof)
	;
		Prof = Prof0
	).

