%---------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: xrobdd.m.
% Main author: dmo

:- module xrobdd.
:- interface.

:- include_module xrobdd__r_robdd.
:- include_module xrobdd__tfr_robdd.
:- include_module xrobdd__tfer_robdd.
:- include_module xrobdd__tfeir_robdd.
:- include_module xrobdd__tfeirn_robdd.

:- include_module xrobdd__check_robdd.

%:- import_module xrobdd__check_robdd.
%:- type xrobdd(T) == check_robdd(T).

:- import_module xrobdd__tfeirn_robdd.
:- type xrobdd(T) == tfeirn(T).

:- implementation.

:- include_module xrobdd__equiv_vars.
:- include_module xrobdd__implications.
