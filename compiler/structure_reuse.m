%-----------------------------------------------------------------------------%
% Copyright (C) 2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
% Module:	structure_reuse
% Main authors: nancy
%-----------------------------------------------------------------------------%

:- module structure_reuse.
:- interface.

:- include_module sr_choice.
:- include_module sr_choice_graphing.
:- include_module sr_choice_util.
:- include_module sr_data.
:- include_module sr_dead.
:- include_module sr_direct.
:- include_module sr_fixpoint_table.
:- include_module sr_indirect.
:- include_module sr_lbu.
:- include_module sr_lfu.
:- include_module sr_live.
:- include_module sr_profile.
:- include_module sr_profile_run.
:- include_module sr_split.
:- include_module sr_top.
:- include_module sr_util.

:- import_module parse_tree.
:- import_module hlds.
:- import_module check_hlds.
:- import_module possible_alias.
:- import_module libs.
:- import_module transform_hlds.
:- import_module ll_backend.
