/*
** Copyright (C) 1997 The University of Melbourne.
** This file may only be copied under the terms of the GNU Library General
** Public License - see the file COPYING.LIB in the Mercury distribution.
**
** $Id: dict.h,v 1.3.4.1 1997-09-29 09:12:57 aet Exp $
*/


#ifndef MB_DICT_H
#define	MB_DICT_H

#include	"util.h"	/* for MB_Bool */

/*
**	A simple abstract data type for a key-value dictionary.
**
**	Note that this type is ABSTRACT. Client code must not refer to
**	any types or fields prefixed with "MB_p_" since they are private 
**	(part of the implementation, not of the interface) and may be
**	changed or removed if the implementation changes. ADTs in C
**	are never pretty.
**
**	Given how slow the current implementation is, you can be sure
**	it will change. 8^)
**
**	Note: The "_p" -suffix- denotes a pointer, not a private type or data.
*/

typedef int (*MB_KeyComparison)(const void *, const void *);
/*
** typedef int (*MB_KeyComparison)(void *, void *);
*/

typedef struct MB_p_Dict_Item {
	void			*p_key;
	void			*p_val;
	struct MB_p_Dict_Item	*p_next;
} MB_p_Dict_Item;
	

typedef struct Dict {
	MB_KeyComparison	p_key_cmp;
	MB_p_Dict_Item		*p_items;
} MB_Dict;

/*
** Create a new dictionary that uses a given comparison function.
** The comparsion function works like strcmp. Specifically, key_cmp(x1,x2)
** returns negative if x1 < x2, zero if x1==x2, positive if x1>x2.
** XXX: Should also pass in some sort of string to identify the dictionary?
*/
MB_Dict
MB_dict_new(MB_KeyComparison key_cmp);

/*
** Initialise a dictionary that has already been allocated in memory.
** Give a key comparison function and start with no items.
*/
void
MB_dict_init(MB_KeyComparison key_cmp, MB_Dict *dict_p);

/*
** Return TRUE if a dictionary is empty, false otherwise.
*/
MB_Bool
MB_dict_is_empty(MB_Dict dict);

/*
** Insert key-value pair into dictionary.
*/
void
MB_dict_insert(const void *key, void *val, MB_Dict *dict_p);

/*
** Lookup value corresponding to key. Returns TRUE if lookup succeeded,
** FALSE if it failed.
*/
MB_Bool
MB_dict_lookup(void *key, MB_Dict dict, void **val_p);

/*
** Delete key-value pair corresponding to key.
*/
void
MB_dict_delete(void *key, MB_Dict *dict_p);

/*
** Return the key comparison function used by a dictionary.
*/
MB_KeyComparison
MB_dict_key_compare(MB_Dict dict);

/*
** Return the `first' key in the dictionary. In fact, this simply
** returns -any- key in the dictionary. This allows us to iterate
** over all elements in the dictionary. Procedure returns FALSE
** if there is no first key (dict is empty) and TRUE otherwise.
** The first key itself is returned through first_key_p.
*/
MB_Bool
MB_dict_first_key(MB_Dict dict, void **first_key_p);

/*
** In the given dictionary, returns the key following this_key.
** The next key is returned through next_key_p. Returns FALSE if
** there is no next key or this_key doesn't exist, TRUE otherwise.
*/
MB_Bool
MB_dict_next_key(MB_Dict dict, void *this_key, void **next_key_p);

#endif	/* MB_DICT_H */


