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
	;	menu
	;	root(fields)
	;	clique(int, fields)
	;	procs(sort, fields, int, int)
	;	proc(int, fields)
	.

:- type sort
	--->	self
	;	self_and_desc.

:- type resp
	--->	html(string).

:- type fields	==	string.		% some subset of "pqtaw", meaning
					% p: port counts
					% q: quanta
					% t: times
					% a: memory allocations
					% w: memory words
					% The characters must be sorted.
