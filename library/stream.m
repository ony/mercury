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
% TODO:
%   - non-blocking streams.
%   - thread-safety (really an issue for the instances).
%   - add more generic operations.
%   - where do the flush and fill operations belong?
%   - what about resizable buffers?
%
%-----------------------------------------------------------------------------%

:- module stream.
:- interface.

:- import_module bool.
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

    % A stream consists of a handle type, a unique state type and an
    % error type.  The handle allows us to refer to different instances
    % of a stream type.  The state type is threaded through the stream
    % operations, while the error type encapsulates errors that might
    % be produced by the underlying stream instances.
    %
:- typeclass stream.stream(Stream, State, Error)
    <= (stream.error(Error), (Stream -> State, Error)) where
[ 
        % Returns a descriptive name for the stream.
        % Intended for use in error messages.
        %
        pred name(Stream::in, stream.name::out, State::di, State::uo) is det
].

%-----------------------------------------------------------------------------%
%
% Input streams
%

    % An input stream is a stream from which we can read things(?) of
    % type Unit.
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

    % An output stream is a stream to which we can write things(?) of
    % type Unit.
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

    % A duplex stream is one to which we can both read and write.
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
% Generic folds over input streams
%

:- type stream.res(Error)
    --->    ok
    ;       error(Error).

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

    % Applies the given closure to each Unit read from the input stream
    % in turn, until eof or error.
    %
:- pred stream.input_stream_fold_state(Stream, pred(Unit, State, State),
    stream.res(Error), State, State)
    <= stream.input(Stream, Unit, State, Error).
:- mode stream.input_stream_fold_state(in, in(pred(in, di, uo) is det),
    out, di, uo) is det.
:- mode stream.input_stream_fold_state(in, in(pred(in, di, uo) is cc_multi),
    out, di, uo) is cc_multi.
    
    % Applies the given closure to each Unit read from the inpu stream
    % in turn, until eof or error.
    %
:- pred stream.input_stream_fold2_state(Stream,
    pred(Unit, T, T, State, State), T, stream.maybe_partial_res(T, Error),
    State, State) <= stream.input(Stream, Unit, State, Error).
:- mode stream.input_stream_fold2_state(in,
    in(pred(in, in, out, di, uo) is det),
    in, out, di, uo) is det.
:- mode stream.input_stream_fold2_state(in,
    in(pred(in, in, out, di, uo) is cc_multi),
    in, out, di, uo) is cc_multi.

    % Applies the given closure to each Unit read from the input stream
    % in turn, until eof or error, or the closure returns `no' as its
    % second argument.
    %
:- pred stream.input_stream_fold2_state_maybe_stop(Stream,
    pred(Unit, bool, T, T, State, State),
    T, stream.maybe_partial_res(T, Error), State, State)
    <= stream.input(Stream, Unit, State, Error).
:- mode stream.input_stream_fold2_state_maybe_stop(in,
    in(pred(in, out, in, out, di, uo) is det), in, out, di, uo) is det.
:- mode stream.input_stream_fold2_state_maybe_stop(in,
    in(pred(in, out, in, out, di, uo) is cc_multi), in, out, di, uo)
    is cc_multi.

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

stream.input_stream_fold_state(Stream, Pred, Res, !S) :-
    get(Stream, Result0, !S),
    (
        Result0 = ok(Result),
        Pred(Result, !S),
        stream.input_stream_fold_state(Stream, Pred, Res, !S)
    ;
        Result0 = eof,
        Res = ok
    ;
        Result0 = error(Error),
        Res = error(Error)
    ).

stream.input_stream_fold2_state(Stream, Pred, T0, Res, !S) :-
    get(Stream, Result0, !S),
    (
        Result0 = ok(Result),
        Pred(Result, T0, T1, !S),
        stream.input_stream_fold2_state(Stream, Pred, T1, Res, !S)
    ;
        Result0 = eof,
        Res = ok(T0)
    ;
        Result0 = error(Error),
        Res = error(T0, Error)
    ).

stream.input_stream_fold2_state_maybe_stop(Stream, Pred, T0, Res, !S) :-
    get(Stream, Result0, !S),
    (
        Result0 = ok(Result),
        Pred(Result, Continue, T0, T1, !S),
        (
            Continue = no,
            Res = ok(T1)
        ;
            Continue = yes,
            stream.input_stream_fold2_state_maybe_stop(Stream, Pred, T1, Res,
                !S)
        )
    ;
        Result0 = eof,
        Res = ok(T0)
    ;
        Result0 = error(Error),
        Res = error(T0, Error)
    ).

%-----------------------------------------------------------------------------%
:- end_module stream.
%-----------------------------------------------------------------------------%
