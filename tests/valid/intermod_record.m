% This is a regression test for a bug in inter-module optimization of
% field access functions which resulted in the following error message:
%
% intermod_record2.opt:005: In clause for function `intermod_record2:field/1':
% intermod_record2.opt:005:   in argument 1 of clause head:
% intermod_record2.opt:005:   error: wrong number of arguments (1; should be 1)
% intermod_record2.opt:005:   in use of constructor `intermod_record2:record'.
%
%
% The problem was that the compiler expects the clauses automatically
% introduced for field access functions to only contain a call to the field
% access function which will later be expanded into unifications, The
% clauses written to `.opt' files are already expanded.
%
:- module intermod_record.

:- interface.

:- import_module intermod_record2.

:- func use_field(record) = int.

:- implementation.

use_field(R) = field(R).

