%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne.
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Mercury distribution.
%-----------------------------------------------------------------------------%

% This module defines the types of the terms that the CGI program (cgi.m)
% and the profiling server (deep.m) pass between them, for now at least
% in printable form.

:- module cgi_interface.

:- interface.

:- type cmd
	--->	quit
	;	timeout(int)
	;	menu
	;	root(fields)
	;	clique(int, fields)
	;	proc(int, fields)
	;	top_procs(sort_measurement, include_descendants,
			display_limit, fields)
	;	proc_static(int)
	;	proc_dynamic(int)
	;	call_site_static(int)
	;	call_site_dynamic(int)
	;	raw_clique(int)
	;	num_proc_statics
	;	num_call_site_statics
	;	num_proc_dynamics
	;	num_call_site_dynamics.

:- type sort_measurement
	--->	calls
	;	time
	;	allocs
	;	words.

:- type include_descendants
	--->	self
	;	self_and_desc.

:- type display_limit
	--->	rank_range(int, int)
	;	threshold(float).

:- type resp
	--->	html(string).

:- type fields	==	string.		% some subset of "pqtaw", meaning
					% p: port counts
					% q: quanta
					% t: times
					% a: memory allocations
					% w: memory words
					% The characters must be sorted.

:- func default_fields = string.

:- func all_fields = string.

:- implementation.

default_fields = "pqw".

all_fields = "apqtw".
