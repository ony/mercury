:- module string_buffer.

:- interface.

:- import_module char.
:- import_module stream.
:- import_module string.

:- type string_buffer(T).

:- type string_buffer_stream(T).

:- type string_buffer_error --->
	string_buffer_error(string).

:- some[T] pred init(string::di, string::in, int::in,
	string_buffer(T)::uo, string_buffer_stream(T)::out) is det.

	% Once the buffer is clobbered, the stream also becomes useless.
	%
:- pred to_string(string_buffer(T)::di, string::out) is det.

:- instance stream.stream(string_buffer_stream(T), string_buffer(T),
	string_buffer_error).

:- instance stream.output(string_buffer_stream(T), char, string_buffer(T),
	string_buffer_error).
:- instance stream.output(string_buffer_stream(T), string, string_buffer(T),
	string_buffer_error).

:- instance stream.error(string_buffer_error).

%----------------------------------------------------------------------------%

:- implementation.

:- import_module unit.

:- type string_buffer(T) --->
	string_buffer(string).

:- type string_buffer_stream(T) --->
	string_buffer_stream(string).

init(InitialString, Name, _InitialSize, Buffer, Stream) :-
	Buffer:string_buffer(unit) = string_buffer(InitialString),
	Stream:string_buffer_stream(unit) = string_buffer_stream(Name).

to_string(string_buffer(Str), Str).

:- instance stream.stream(string_buffer_stream(T), string_buffer(T),
	string_buffer_error) where 
[
	name(string_buffer_stream(Name), Name, !State)
].

:- instance stream.output(string_buffer_stream(T), char, string_buffer(T),
	string_buffer_error) where
[
	put(_Stream, Chr, string_buffer(Buffer0),
		string_buffer(Buffer0 ++ string.from_char(Chr)))
].

:- instance stream.output(string_buffer_stream(T), string, string_buffer(T),
	string_buffer_error) where
[
	put(_Stream, Str, string_buffer(Buffer0), string_buffer(
		Buffer0 ++ Str))
].

:- instance stream.error(string_buffer_error) where
[
	error_message(string_buffer_error(Message)) = Message
].
