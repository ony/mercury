
/*
** Copyright (C) 1997 University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: lineedit.h,v 1.1.2.1 1997-09-29 09:13:05 aet Exp $
*/


#ifndef MB_LINEEDIT_H
#define	MB_LINEEDIT_H

#ifdef USE_READLINE

#include	<readline/readline.h>
#include	<readline/history.h>

#else /* not USE_READLINE */

/*
** Behaves the same way as GNU readline's readline() function. That is:
** Read a line a return it. Caller is responsible for freeing the line.
*/
char *
readline(char *prompt);

/*
** Behaves like GNU readline's add_history().
*/
void
add_history(char *line);

#endif /* not USE_READLINE */


#endif	/* MB_LINEEDIT_H */
