%---------------------------------------------------------------------------%
% Copyright (C) 2001-2002 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%

% File: xrobdd.m.
% Main author: dmo

:- module xrobdd.
:- interface.

:- include_module r_robdd.
:- include_module tfr_robdd.
:- include_module tfer_robdd.
:- include_module tfeir_robdd.
:- include_module tfeirn_robdd.

:- include_module check_robdd.

:- include_module equiv_vars.
:- include_module implications.

%:- import_module xrobdd__check_robdd.
%:- type xrobdd(T) == check_robdd(T).

:- import_module xrobdd__tfeirn_robdd.
:- type xrobdd(T) == tfeirn(T).

:- implementation.
