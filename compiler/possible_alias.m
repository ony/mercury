%-----------------------------------------------------------------------------%
% Copyright (C) 2004 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
% Module:	possible_alias
% Main authors: nancy
%-----------------------------------------------------------------------------%

:- module possible_alias.
:- interface. 

:- include_module pa_alias.
:- include_module pa_alias_as.
:- include_module pa_datastruct.
:- include_module pa_prelim_run.
:- include_module pa_run.
:- include_module pa_selector.
:- include_module pa_sr_util.
:- include_module pa_util.

:- import_module check_hlds.
:- import_module hlds.
:- import_module libs.
:- import_module ll_backend.
:- import_module parse_tree.
:- import_module structure_reuse.
:- import_module transform_hlds.

