%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%-----------------------------------------------------------------------------%
% Copyright (C) 2006 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
%
% File: stream.m.
% Authors: juliensf, maclarty.
%
%-----------------------------------------------------------------------------%

:- module stream.
:- interface.

:- import_module string.

%-----------------------------------------------------------------------------%
%
% Stream errors
%

:- type stream.name == string.

:- type stream.result(T, E)
    --->    ok(T)
    ;       eof
    ;       error(E).

:- typeclass stream.error(Error) where
[
    % Convert a stream error into a human-readable format.
    % e.g. for use in error messages.
    %
    func error_message(Error) = string
].

%-----------------------------------------------------------------------------%
%
% Streams
%

    % A stream consists of a base, a state to update and an error type.
    %
:- typeclass stream.stream(Stream, State, Error)
    <= (stream.error(Error), (Stream -> State, Error)) where
[ 
        % A human readable name describing the stream, for use in 
        % error messages etc.
        %
        pred name(Stream::in, stream.name::out, State::di, State::uo) is det
].

%-----------------------------------------------------------------------------%
%
% Input streams
%

:- typeclass stream.input(Stream, Unit, State, Error)
    <= stream(Stream, State, Error) where
[
    pred get(Stream::in, stream.result(Unit, Error)::out, State::di, State::uo)
        is det
].

%-----------------------------------------------------------------------------%
%
% Output streams
%

:- typeclass stream.output(Stream, Unit, State, Error)
    <= stream(Stream, State, Error) where
[
    pred put(Stream::in, Unit::in, State::di, State::uo) is det
].

%-----------------------------------------------------------------------------%
%
% Duplex streams
%

:- typeclass stream.duplex(Stream, Unit, State, Error)
    <= ( stream.input(Stream,  Unit, State, Error),
         stream.output(Stream, Unit, State, Error)
       ) where [].

%----------------------------------------------------------------------------%
%
% Putback streams
%

:- typeclass stream.putback(Stream, Unit, State, Error)
    <= stream.input(Stream, Unit, State, Error) where
[
    pred unget(Stream::in, Unit::in, State::di, State::uo) is det
]. 

:- typeclass stream.unbounded_putback(Stream, Unit, State, Error)
    <= stream.putback(Stream, Unit, State, Error) where [].

%----------------------------------------------------------------------------%
%
% Buffered streams
%

% XXX What about streams where we can control the buffering?

:- typeclass stream.buffered(Stream, State, Error)
    <= stream(Stream, State, Error) where
[
     pred flush(Stream::in, State::di, State::uo) is det
].

% :- typeclass stream.buffered_output(Stream, State, Error)
%   <= stream.output(Stream, State, Error) where
% [
%   pred flush(Stream::in, State::di, State::uo) is det
% ].

% :- typeclass stream.buffered_input(Stream, State, Error)
%   <= stream.input(Stream, State, Error) where
% [
%   pred fill(Stream::in, State::di, State::uo) is det
% ].

%----------------------------------------------------------------------------%
%
% Seekable streams
%

:- type stream.whence
    --->    set
    ;       cur
    ;       end.

    % XXX call this random_access?
    %
:- typeclass stream.seekable(Stream, State, Error)
         <= stream(Stream, State, Error) where [
     pred seek(Stream::in, stream.whence::in, int::in, State::di, State::uo)
         is det
].

%----------------------------------------------------------------------------%
%
% Line oriented streams
%

:- typeclass stream.text(Stream, State, Error)
    <= stream(Stream, State, Error) where
[
    pred get_line(Stream::in, int::out, State::di, State::uo) is det,
    pred set_line(Stream::in, int::in,  State::di, State::uo) is det
].

%-----------------------------------------------------------------------------%

% It would probably also be useful to have something like the following.

% :- typeclass stream.standard_reader(Stream, Unit, State) 
%         <= ( stream.input(Stream, Unit, State),
%              stream.buffered(Stream, State),
%              stream.text(Stream, State)) where [].
%     
% :- typeclass stream.standard_writer(Stream, Unit, State)
%         <= ( stream.output(Stream, Unit, State),
%              stream.putback(Stream, Unit, State),
%              stream.text(Stream, State)) where [].

%-----------------------------------------------------------------------------%
%
% Generic stream operations
%

:- type stream.maybe_partial_res(T, Error)
    --->    ok(T)
    ;       error(T, Error).

    % Applies the given closure to each Unit read from the input stream
    % in turn, until eof or error.
    %
:- pred stream.input_stream_fold(Stream, pred(Unit, T, T), T,
    stream.maybe_partial_res(T, Error), State, State)
    <= stream.input(Stream, Unit, State, Error).
:- mode stream.input_stream_fold(in, in(pred(in, in, out) is det),
    in, out, di, uo) is det.
:- mode stream.input_stream_fold(in, in(pred(in, in, out) is cc_multi),
    in, out, di, uo) is cc_multi.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------------%
%
% Folds over input streams
%

stream.input_stream_fold(Stream, Pred, T0, Res, !S) :-
    get(Stream, Result, !S),
    (
        Result = ok(Unit),
        Pred(Unit, T0, T1),
        stream.input_stream_fold(Stream, Pred, T1, Res, !S)
    ;
        Result = eof,
        Res = ok(T0)
    ;
        Result = error(Error),
        Res = error(T0, Error)
    ).


%-----------------------------------------------------------------------------%
:- end_module stream.
%-----------------------------------------------------------------------------%
