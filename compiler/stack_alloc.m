%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%-----------------------------------------------------------------------------%
% Copyright (C) 2002-2007, 2010-2011 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
% 
% File stack_alloc.m.
% Authors: zs, conway.
% 
% This module allocates stack slots to the variables that need to be saved
% across a call, across a goal that may fail, or in a parallel conjunction.
% 
% The jobs is done in two steps. First we traverse the predicate definition
% looking for sets of variables that must be saved on the stack at the same
% time. If --optimize-stack-slots is set, then this phase is done by
% stack_opt.m; if --optimize-stack-slots is not set, then it is done by this
% module. Then we use a graph colouring algorithm to find an allocation of
% stack slots (colours) to variables such that in each set of variables that
% must be saved at the same time, each variable has a different colour.
% 
%-----------------------------------------------------------------------------%

:- module ll_backend.stack_alloc.
:- interface.

:- import_module hlds.hlds_module.
:- import_module hlds.hlds_pred.

%-----------------------------------------------------------------------------%

:- pred allocate_stack_slots_in_proc(module_info::in, pred_proc_id::in,
    proc_info::in, proc_info::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module check_hlds.type_util.
:- import_module hlds.code_model.
:- import_module hlds.hlds_goal.
:- import_module hlds.hlds_llds.
:- import_module libs.globals.
:- import_module libs.options.
:- import_module libs.trace_params.
:- import_module ll_backend.live_vars.
:- import_module ll_backend.liveness.
:- import_module ll_backend.trace_gen.
:- import_module parse_tree.prog_data.
:- import_module parse_tree.set_of_var.

:- import_module array.
:- import_module bool.
:- import_module enum.
:- import_module int.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module pair.
:- import_module set.

%-----------------------------------------------------------------------------%

allocate_stack_slots_in_proc(ModuleInfo, proc(PredId, _ProcId), !ProcInfo) :-
    initial_liveness(!.ProcInfo, PredId, ModuleInfo, Liveness0),
    module_info_pred_info(ModuleInfo, PredId, PredInfo),
    module_info_get_globals(ModuleInfo, Globals),
    globals.get_trace_level(Globals, TraceLevel),
    (
        eff_trace_level_needs_fail_vars(ModuleInfo, PredInfo, !.ProcInfo,
            TraceLevel) = yes
    ->
        trace_fail_vars(ModuleInfo, !.ProcInfo, FailVars)
    ;
        FailVars = set_of_var.init
    ),
    body_should_use_typeinfo_liveness(PredInfo, Globals, TypeInfoLiveness),
    globals.lookup_bool_option(Globals, opt_no_return_calls,
        OptNoReturnCalls),
    proc_info_get_vartypes(!.ProcInfo, VarTypes),
    build_dummy_type_array(ModuleInfo, VarTypes, DummyTypeArray, DummyVars),
    AllocData = alloc_data(ModuleInfo, !.ProcInfo, TypeInfoLiveness,
        OptNoReturnCalls, DummyTypeArray),
    NondetLiveness0 = set_of_var.init,
    SimpleStackAlloc0 = stack_alloc(set.make_singleton_set(FailVars)),
    proc_info_get_goal(!.ProcInfo, Goal0),
    build_live_sets_in_goal_no_par_stack(Goal0, Goal, FailVars, AllocData,
        SimpleStackAlloc0, SimpleStackAlloc, Liveness0, _Liveness,
        NondetLiveness0, _NondetLiveness),
    proc_info_set_goal(Goal, !ProcInfo),
    SimpleStackAlloc = stack_alloc(LiveSets0),

    do_we_need_maxfr_slot(Globals, ModuleInfo, PredInfo, !ProcInfo),
    trace_reserved_slots(ModuleInfo, PredInfo, !.ProcInfo, Globals,
        NumReservedSlots, MaybeReservedVarInfo),
    (
        MaybeReservedVarInfo = yes(ResVar - _),
        ResVarSet = set_of_var.make_singleton(ResVar),
        set.insert(ResVarSet, LiveSets0, LiveSets)
    ;
        MaybeReservedVarInfo = no,
        LiveSets = LiveSets0
    ),
    graph_colour_group_elements(LiveSets, ColourSets),
    set.to_sorted_list(ColourSets, ColourList),

    CodeModel = proc_info_interface_code_model(!.ProcInfo),
    allocate_stack_slots(ColourList, CodeModel, NumReservedSlots,
        MaybeReservedVarInfo, StackSlots1),
    allocate_dummy_stack_slots(DummyVars, CodeModel, -1,
        StackSlots1, StackSlots),
    proc_info_set_stack_slots(StackSlots, !ProcInfo).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- type stack_alloc
    --->    stack_alloc(
                % The sets of vars that need to be on the stack
                % at the same time.
                set(set_of_progvar)
            ).

:- instance stack_alloc_info(stack_alloc) where [
    pred(at_call_site/4) is alloc_at_call_site,
    pred(at_resume_site/4) is alloc_at_resume_site,
    pred(at_par_conj/4) is alloc_at_par_conj
].

:- pred alloc_at_call_site(need_across_call::in, alloc_data::in,
    stack_alloc::in, stack_alloc::out) is det.

alloc_at_call_site(NeedAtCall, AllocData, !StackAlloc) :-
    NeedAtCall = need_across_call(ForwardVars, ResumeVars, NondetLiveVars),
    LiveSet0 = set_of_var.union_list([ForwardVars, ResumeVars, NondetLiveVars]),
    filter_out_dummy_vars(AllocData, LiveSet0, LiveSet),

    !.StackAlloc = stack_alloc(LiveSets0),
    LiveSets = set.insert(LiveSets0, LiveSet),
    !:StackAlloc = stack_alloc(LiveSets).

:- pred alloc_at_resume_site(need_in_resume::in, alloc_data::in,
    stack_alloc::in, stack_alloc::out) is det.

alloc_at_resume_site(NeedAtResume, AllocData, !StackAlloc) :-
    NeedAtResume = need_in_resume(ResumeOnStack, ResumeVars, NondetLiveVars),
    (
        ResumeOnStack = no
    ;
        ResumeOnStack = yes,
        LiveSet0 = set_of_var.union(ResumeVars, NondetLiveVars),
        filter_out_dummy_vars(AllocData, LiveSet0, LiveSet),

        !.StackAlloc = stack_alloc(LiveSets0),
        LiveSets = set.insert(LiveSets0, LiveSet),
        !:StackAlloc = stack_alloc(LiveSets)
    ).

:- pred alloc_at_par_conj(need_in_par_conj::in, alloc_data::in,
    stack_alloc::in, stack_alloc::out) is det.

alloc_at_par_conj(NeedParConj, AllocData, !StackAlloc) :-
    NeedParConj = need_in_par_conj(StackVars0),
    filter_out_dummy_vars(AllocData, StackVars0, StackVars),

    !.StackAlloc = stack_alloc(LiveSets0),
    LiveSets = set.insert(LiveSets0, StackVars),
    !:StackAlloc = stack_alloc(LiveSets).

:- pred filter_out_dummy_vars(alloc_data::in,
    set_of_progvar::in, set_of_progvar::out) is det.

filter_out_dummy_vars(AllocData, Vars, NonDummyVars) :-
    DummyVarArray = AllocData ^ ad_dummy_var_array,
    set_of_var.filter(var_is_not_dummy(DummyVarArray), Vars, NonDummyVars).

:- pred var_is_not_dummy(array(is_dummy_type)::in, prog_var::in) is semidet.

var_is_not_dummy(DummyVarArray, Var) :-
    VarNum = to_int(Var),
    array.lookup(DummyVarArray, VarNum, IsDummy),
    IsDummy = is_not_dummy_type.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred allocate_stack_slots(list(set_of_progvar)::in, code_model::in, int::in,
    maybe(pair(prog_var, int))::in, stack_slots::out) is det.

allocate_stack_slots(ColourList, CodeModel, NumReservedSlots,
        MaybeReservedVarInfo, StackSlots) :-
    % The reserved slots are referred to by fixed number
    % (e.g. framevar(1)) in trace.setup.
    FirstVarSlot = NumReservedSlots + 1,
    allocate_stack_slots_2(ColourList, CodeModel, FirstVarSlot,
        MaybeReservedVarInfo, map.init, StackSlots).

:- pred allocate_stack_slots_2(list(set_of_progvar)::in, code_model::in,
    int::in, maybe(pair(prog_var, int))::in,
    stack_slots::in, stack_slots::out) is det.

allocate_stack_slots_2([], _, _, _, !StackSlots).
allocate_stack_slots_2([Vars | VarSets], CodeModel, N0, MaybeReservedVarInfo,
        !StackSlots) :-
    (
        MaybeReservedVarInfo = yes(ResVar - ResSlotNum),
        set_of_var.member(Vars, ResVar)
    ->
        SlotNum = ResSlotNum,
        N1 = N0
    ;
        SlotNum = N0,
        N1 = N0 + 1
    ),
    VarList = set_of_var.to_sorted_list(Vars),
    allocate_same_stack_slot(VarList, CodeModel, SlotNum, !StackSlots),
    allocate_stack_slots_2(VarSets, CodeModel, N1, MaybeReservedVarInfo,
        !StackSlots).

:- pred allocate_same_stack_slot(list(prog_var)::in, code_model::in, int::in,
    stack_slots::in, stack_slots::out) is det.

allocate_same_stack_slot([], _CodeModel, _Slot, !StackSlots).
allocate_same_stack_slot([Var | Vars], CodeModel, Slot, !StackSlots) :-
    (
        CodeModel = model_non,
        Locn = nondet_slot(Slot)
    ;
        ( CodeModel = model_det
        ; CodeModel = model_semi
        ),
        Locn = det_slot(Slot)
    ),
    map.det_insert(Var, Locn, !StackSlots),
    allocate_same_stack_slot(Vars, CodeModel, Slot, !StackSlots).

    % We must not allocate the same stack slot to dummy variables. If we do,
    % then the code that saves variables on the stack at calls will get
    % confused. After saving one dummy variable on the stack, it will try
    % to save the next in the same stack slot; believing the first variable
    % to still be live, it will move it away.
    %
    % In ordinary grades, it is possible to have one value of type io.state
    % and another of type store.store live at the same time; in debugging
    % grades, due to our policy of extending variable lifetimes, more than
    % one io.state may be live at the same time.
    %
:- pred allocate_dummy_stack_slots(list(prog_var)::in, code_model::in,
    int::in, stack_slots::in, stack_slots::out) is det.

allocate_dummy_stack_slots([], _, _, !StackSlots).
allocate_dummy_stack_slots([Var | Vars], CodeModel, N0, !StackSlots) :-
    allocate_same_stack_slot([Var], CodeModel, N0, !StackSlots),
    allocate_dummy_stack_slots(Vars, CodeModel, N0 - 1, !StackSlots).

%-----------------------------------------------------------------------------%
:- end_module stack_alloc.
%-----------------------------------------------------------------------------%
