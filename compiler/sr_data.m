%-----------------------------------------------------------------------------%
% Copyright (C) 2000 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% Module:	sr_data
% Main authors: nancy
% 
% The data structures which are shared between the various phases of the
% structure reuse analysis.
%
%-----------------------------------------------------------------------------%

:- module sr_data.
:- interface.

:- import_module pa_alias_as, pa_datastruct, prog_data.
:- import_module list, set.

	% A reuse, whether direct or indirect, is only allowed as long
	% as the caller fulfills some conditions.  This type keeps track
	% of the information needed to verify whether the condition for
	% reuse is met or not. 
:- type reuse_condition
	--->	always
	;	condition(
		   nodes 		:: list(pa_datastruct__datastruct),
		   local_use_headvars 	:: set(prog_var),
		   local_alias_headvars :: alias_as 
		).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
