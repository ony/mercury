%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%-----------------------------------------------------------------------------%
% Copyright (C) 2006 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% File: string_buffer.m.
% Authors: maclarty, juliensf.
%
%-----------------------------------------------------------------------------%

:- module string_buffer.
:- interface.

:- import_module char.
:- import_module stream.
:- import_module string.

%-----------------------------------------------------------------------------%

:- type string_buffer(T).

:- type string_buffer_stream(T).

:- type string_buffer_error
    --->    string_buffer_error(string).
    
    % init(InitialContents, Name, Size, State, Handle).
    %
    % Create a new string_buffer handle and state setting the initial
    % contents of the buffer to `InitialContents'.
    %
    % XXX Why do we need the size argument?
    %
:- some [T] pred init(string::di, string::in, int::in,
    string_buffer(T)::uo, string_buffer_stream(T)::out) is det.

    % Once the buffer is clobbered, the stream also becomes useless.
    %
    % XXX Perhaps the stream should also be passed in as a di argument
    % then?
    %
:- pred to_string(string_buffer(T)::di, string::out) is det.

%----------------------------------------------------------------------------%

:- instance stream.stream(string_buffer_stream(T), string_buffer(T)).

:- instance stream.output(string_buffer_stream(T), string_buffer(T)).

:- instance stream.output(string_buffer_stream(T), char, string_buffer(T)).
:- instance stream.output(string_buffer_stream(T), string, string_buffer(T)).

:- instance stream.error(string_buffer_error).

%----------------------------------------------------------------------------%
%----------------------------------------------------------------------------%

:- implementation.

:- import_module unit.

%----------------------------------------------------------------------------%

:- type string_buffer(T)
    --->    string_buffer(string).

:- type string_buffer_stream(T)
    --->    string_buffer_stream(string).

init(InitialString, Name, _InitialSize, Buffer, Stream) :-
    Buffer:string_buffer(unit) = string_buffer(InitialString),
    Stream:string_buffer_stream(unit) = string_buffer_stream(Name).

to_string(string_buffer(Str), Str).

:- instance stream.stream(string_buffer_stream(T), string_buffer(T)) where 
[
    name(string_buffer_stream(Name), Name, !State)
].

:- instance stream.output(string_buffer_stream(T), string_buffer(T)) where
[
    flush(_, !State)
].

:- instance stream.output(string_buffer_stream(T), char, string_buffer(T))
    where
[
    put(_Stream, Chr, string_buffer(Buffer0),
        string_buffer(Buffer0 ++ string.from_char(Chr)))
].

:- instance stream.output(string_buffer_stream(T), string, string_buffer(T))
    where
[
    put(_Stream, Str, string_buffer(Buffer0), string_buffer(Buffer0 ++ Str))
].

:- instance stream.error(string_buffer_error) where
[
    error_message(string_buffer_error(Message)) = Message
].
