
/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: slist.h,v 1.2.4.1 1997-09-29 09:13:27 aet Exp $
*/

/*
**	Minimal linked list implementation.
**
**	The exported type is named `SList' rather than `List' since
**	a) there's already a List type in runtime/dlist.h 
**	b) the lists are `S'ingly linked.
**
**	Note types and fields whose name is prefixed with "MB_p_" are
**	private and client code should not refer to them.
*/


#ifndef MB_LIST_H
#define	MB_LIST_H

#include	"util.h" /* for MB_Bool */

typedef struct MB_p_SList_Node {
	void			*p_head;
	struct MB_p_SList_Node	*p_tail;
} MB_p_SList_Node;

typedef struct MB_p_SList_Node
	*MB_SList;

MB_SList
MB_slist_nil(void);

MB_Bool
MB_slist_null(MB_SList list);

MB_SList
MB_slist_cons(void *head, MB_SList tail);

void *
MB_slist_head(MB_SList list);

MB_SList
MB_slist_tail(MB_SList list);

#endif	/* MB_LIST_H */
