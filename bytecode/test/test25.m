
:- module test05.
:- interface.
:- import_module io.

:- pred main(io__state::di, io__state::uo) is det.

:- implementation.

:- import_module int, list.

main --> 
	io__write_string("Bonjour, le monde!.\n"),
	io__write_string(
	"8-bit: Molière et il niño ont donné aux guêpes chinois ein bißchen\
Torte ohne von die Wespen gestochen zu werden. \
«Xièxie. Ob unsere Freunde ein stückchen eßen möchten?», \
ont-dit les guêpes.\\\n").

:- pred alef(float::out) is det.

alef(X) :-
	X = 3.14159265358979323.

:- pred bet(int::out) is det.
bet(X) :-
	X = 12345678.

:- pred gimel(int::out) is det.
gimel(12345678901234567890).

:- pred tamago(string::out).
tamago("egg").
tamago("oeuf").
tamago("Ei").


:- func fac(int) = int.
:- mode fac(in) = out is det.

fac(X) =
	(
	if X =< 0
	then
		1
	else
		X * fac(X-1)
	).


:- pred not_cool(string::in) is semidet.

not_cool(Str) :-
	not cool(Str).

:- pred cool(string::in) is semidet.
cool("choice").
cool("wicked").
cool("vicious").
cool("jammin").
cool("righteous").

:- pred rev(list(T), list(T)).
:- mode rev(in, out) is det.
:- mode rev(out, in) is nondet.
:- mode rev(in, in) is semidet.
%:- mode rev(out, out) is multi.

rev([],[]).
rev([X|Xs],App) :-
	rev(Xs,RXs),
	app(RXs,[X],App).

:- pred app(list(T), list(T), list(T)).
:- mode app(in, in, out) is det.
:- mode app(out, out, in) is multi.
:- mode app(in, in, in) is semidet.
:- mode app(in, out, in) is nondet.
:- mode app(out, in, in) is semidet.
%:- mode app(out, out, out) is multi.

app(Xs,[],Xs).
app(Xs,[Y|Ys], [Y|App]) :-
	app(Xs,Ys,App).


%:- pred mymap(pred(T::in,S::out) is det, list(T)::in, list(S)::out) is det.
:- pred mymap(pred(T,S)::pred(in,out) is det, list(T)::in, list(S)::out) is det.
mymap(P,[],[]).
mymap(P,[X|Xs],[PX|Map]) :-
	P(X,PX),
	mymap(P,Xs,Map).

:- pred just_fail is failure.
just_fail :-
	fail.


:- pred pickabox(string::out) is cc_multi.
pickabox("a new car").
pickabox("Selangor pewter decanters").
pickabox("Jason recliner").


:- pred nada(T::in, T::out) is det.
:- pragma c_code(nada(X::in, Y::out), will_not_call_mercury,"
	Y = X;
").

