:- module string_buffer_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module stream.
:- import_module string.
:- import_module string_buffer.

main(!IO) :-
	some [!Ian, !Julien] (
		string_buffer.init("Ian", "Ian's string buffer", 20, !:Ian,
			IanStream),
		string_buffer.init("Julien", "Julien's string buffer",
			20, !:Julien, JulienStream),
		put(JulienStream, ' ', !Julien),
		put(JulienStream, "Fischer", !Julien),
		put(IanStream, ' ', !Ian),
		put(IanStream, "MacLarty", !Ian),
		string_buffer.to_string(!.Ian, IanFinal),
		string_buffer.to_string(!.Julien, JulienFinal)
	),
	io.format("Julien = \"%s\"\n", [s(JulienFinal)], !IO),
	io.format("Ian = \"%s\"\n", [s(IanFinal)], !IO),
	nl(!IO).
