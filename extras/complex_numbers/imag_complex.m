%---------------------------------------------------------------------------%
% Copyright (C) 1997 University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%---------------------------------------------------------------------------%
%
% File: imag_complex.m.
% Main author: fjh.
% Stability: medium.
%
% This module provides binary operators on (imag, complex).
%
% See also:
%	complex.m, imag.m, complex_imag.m.
%
%---------------------------------------------------------------------------%

:- module imag_complex.
:- interface.
:- import_module imag, complex.

	% addition
:- func imag + complex = complex.
:- mode in   + in   = uo  is det.
:- mode uo   + in   = in  is semidet.
:- mode in   + uo   = in  is det.

	% subtraction
:- func imag - complex = complex.
:- mode in   - in   = uo  is det.
:- mode uo   - in   = in  is semidet.
:- mode in   - uo   = in  is det.

	% multiplication
:- func imag * complex = complex.
:- mode in   * in   = uo  is det.

	% division
:- func imag / complex = complex.
:- mode in   / in   = uo  is det.

%---------------------------------------------------------------------------%

:- implementation.
:- import_module float.

im(XI) + cmplx(YR, YI) = cmplx(0.0 + YR, XI + YI).
im(XI) - cmplx(YR, YI) = cmplx(0.0 - YR, XI - YI).
im(XI) * cmplx(YR, YI) = cmplx(-XI * YI, XI * YR).
im(XI) / cmplx(YR, YI) = cmplx((XI * YI) / Div, (XI * YR) / Div) :-
	Div = (YR * YR + YI * YI).

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

% Division of imag / complex formula obtained by simplifying this one:
% cmplx(Xr, Xi) / cmplx(Yr, Yi) =
%		cmplx((Xr * Yr + Xi * Yi) / Div, (Xi * Yr - Xr * Yi) / Div) :-
%	Div = (Yr * Yr + Yi * Yi).

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%
