/* this code automatically generated - do not edit.*/

/*
INIT list_module0
INIT list_module1
INIT list_module2
INIT list_module3
INIT list_module4
INIT list_module5
INIT list_module6
INIT list_module7
INIT list_module8
INIT list_module9
INIT list_module10
INIT list_module11
INIT list_module12
INIT list_module13
INIT list_module14
INIT list_module15
INIT list_module16
INIT list_module17
INIT list_module18
INIT list_module19
INIT list_module20
INIT list_module21
INIT list_module22
INIT list_module23
INIT list_module24
INIT list_module25
INIT list_module26
INIT list_module27
INIT list_module28
INIT list_module29
INIT list_module30
INIT list_module31
INIT list_module32
INIT list_module33
INIT list_module34
INIT list_module35
INIT list_module36
INIT list_module37
INIT list_module38
INIT list_module39
INIT list_module40
INIT list_module41
INIT list_module42
INIT list_module43
INIT list_module44
INIT list_module45
INIT list_module46
INIT list_module47
INIT list_module48
INIT list_module49
INIT list_module50
INIT list_module51
ENDINIT
*/

#include "imp.h"

Define_extern_entry(mercury__list__append_3_3);
Declare_label(mercury__list__append_3_3_i2);
Declare_label(mercury__list__append_3_3_i4);

BEGIN_MODULE(mercury__list_module0)
	init_entry(mercury__list__append_3_3);
	init_label(mercury__list__append_3_3_i2);
	init_label(mercury__list__append_3_3_i4);
BEGIN_CODE

/* code for predicate list__append/3 in mode 3 */
Define_entry(mercury__list__append_3_3);
	{ mkframe("list__append/3", 2, ENTRY(do_fail)); }
	{ framevar(0) = (Integer) r1; }
	{ framevar(1) = (Integer) r4; }
	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) LABEL(mercury__list__append_3_3_i2); }
	{ r3 = (Integer) r4; }
	{ static const Word mercury_const_3[] = {
		0
	  };
	  r2 = mkword(mktag(0), mercury_const_3); }

	{ succeed(); }
Define_label(mercury__list__append_3_3_i2);
	update_prof_current_proc(LABEL(mercury__list__append_3_3));

	{ modframe(ENTRY(do_fail)); }
	{ if (((tag((Integer) framevar(1)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) framevar(1), 0) == 0)))
		fail(); }
	{ r1 = (Integer) framevar(0); }
	{ framevar(0) = (Integer) field(mktag(0), (Integer) framevar(1), 1); }
	{ r4 = (Integer) field(mktag(0), (Integer) framevar(1), 2); }

	{ localcall(mercury__list__append_3_3,
		LABEL(mercury__list__append_3_3_i4),
		LABEL(mercury__list__append_3_3)); }

Define_label(mercury__list__append_3_3_i4);
	update_prof_current_proc(LABEL(mercury__list__append_3_3));

	{ r1 = (Integer) r2; }
	{ tag_incr_hp(r2, mktag(0), 3); }
	{ field(mktag(0), (Integer) r2, 0) = 1; }
	{ field(mktag(0), (Integer) r2, 1) = (Integer) framevar(0); }
	{ field(mktag(0), (Integer) r2, 2) = (Integer) r1; }

	{ succeed(); }
END_MODULE

Define_extern_entry(mercury__list__append_3_0);
Declare_label(mercury__list__append_3_0_i4);
Declare_label(mercury__list__append_3_0_i5);
Declare_label(mercury__list__append_3_0_i1);

BEGIN_MODULE(mercury__list_module1)
	init_entry(mercury__list__append_3_0);
	init_label(mercury__list__append_3_0_i4);
	init_label(mercury__list__append_3_0_i5);
	init_label(mercury__list__append_3_0_i1);
BEGIN_CODE

/* code for predicate list__append/3 in mode 0 */
Define_entry(mercury__list__append_3_0);
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__append_3_0_i1); }
	{ r5 = (Integer) sp; }
Define_label(mercury__list__append_3_0_i4);
	incr_sp(1);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r4, 2); }

	{ if (!(((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0))))
		GOTO_LABEL(mercury__list__append_3_0_i4); }
	{ r4 = (Integer) r3; }
Define_label(mercury__list__append_3_0_i5);
	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	decr_sp(1);
	{ if (((Integer) sp > (Integer) r5))
		GOTO_LABEL(mercury__list__append_3_0_i5); }

	{ proceed(); }
Define_label(mercury__list__append_3_0_i1);
	{ r4 = (Integer) r3; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__append_3_2);
Declare_label(mercury__list__append_3_2_i1001);
Declare_label(mercury__list__append_3_2_i3);
Declare_label(mercury__list__append_3_2_i4);
Declare_label(mercury__list__append_3_2_i1);

BEGIN_MODULE(mercury__list_module2)
	init_entry(mercury__list__append_3_2);
	init_label(mercury__list__append_3_2_i1001);
	init_label(mercury__list__append_3_2_i3);
	init_label(mercury__list__append_3_2_i4);
	init_label(mercury__list__append_3_2_i1);
BEGIN_CODE

/* code for predicate list__append/3 in mode 2 */
Define_entry(mercury__list__append_3_2);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__append_3_2_i1001); }
	incr_sp(4);
	{ GOTO_LABEL(mercury__list__append_3_2_i3); }
Define_label(mercury__list__append_3_2_i1001);
	update_prof_current_proc(LABEL(mercury__list__append_3_2));

	{ r4 = (Integer) r5; }
	{ r1 = TRUE; }

	{ proceed(); }
Define_label(mercury__list__append_3_2_i3);
	{ if (((tag((Integer) r5) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r5, 0) == 0)))
		GOTO_LABEL(mercury__list__append_3_2_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r5, 2); }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r1, 1); }
	{ r4 = (Integer) field(mktag(0), (Integer) r5, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__append_3_2_i4),
		LABEL(mercury__list__append_3_2)); }

Define_label(mercury__list__append_3_2_i4);
	update_prof_current_proc(LABEL(mercury__list__append_3_2));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__append_3_2_i1); }
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(3); }
	{ r5 = (Integer) detstackvar(1); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ localtailcall(mercury__list__append_3_2,
		LABEL(mercury__list__append_3_2)); }
Define_label(mercury__list__append_3_2_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__append_3_1);
Declare_label(mercury__list__append_3_1_i1001);
Declare_label(mercury__list__append_3_1_i3);
Declare_label(mercury__list__append_3_1_i6);
Declare_label(mercury__list__append_3_1_i1);

BEGIN_MODULE(mercury__list_module3)
	init_entry(mercury__list__append_3_1);
	init_label(mercury__list__append_3_1_i1001);
	init_label(mercury__list__append_3_1_i3);
	init_label(mercury__list__append_3_1_i6);
	init_label(mercury__list__append_3_1_i1);
BEGIN_CODE

/* code for predicate list__append/3 in mode 1 */
Define_entry(mercury__list__append_3_1);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__append_3_1_i1001); }
	incr_sp(5);
	{ GOTO_LABEL(mercury__list__append_3_1_i3); }
Define_label(mercury__list__append_3_1_i1001);
	update_prof_current_proc(LABEL(mercury__list__append_3_1));

	{ r3 = (Integer) r5; }

	{ Declare_entry(mercury____Unify___list_1_0);
	  tailcall(ENTRY(mercury____Unify___list_1_0),
		LABEL(mercury__list__append_3_1)); }
Define_label(mercury__list__append_3_1_i3);
	{ if (((tag((Integer) r5) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r5, 0) == 0)))
		GOTO_LABEL(mercury__list__append_3_1_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r5, 2); }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ detstackvar(4) = (Integer) r4; }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r1, 1); }
	{ r6 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r5, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__append_3_1_i6),
		LABEL(mercury__list__append_3_1)); }

Define_label(mercury__list__append_3_1_i6);
	update_prof_current_proc(LABEL(mercury__list__append_3_1));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__append_3_1_i1); }
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(3); }
	{ r4 = (Integer) detstackvar(4); }
	{ r5 = (Integer) detstackvar(1); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ localtailcall(mercury__list__append_3_1,
		LABEL(mercury__list__append_3_1)); }
Define_label(mercury__list__append_3_1_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__remove_suffix_3_0);
Declare_label(mercury__list__remove_suffix_3_0_i2);
Declare_label(mercury__list__remove_suffix_3_0_i3);
Declare_label(mercury__list__remove_suffix_3_0_i4);
Declare_label(mercury__list__remove_suffix_3_0_i6);
Declare_label(mercury__list__remove_suffix_3_0_i1);

BEGIN_MODULE(mercury__list_module4)
	init_entry(mercury__list__remove_suffix_3_0);
	init_label(mercury__list__remove_suffix_3_0_i2);
	init_label(mercury__list__remove_suffix_3_0_i3);
	init_label(mercury__list__remove_suffix_3_0_i4);
	init_label(mercury__list__remove_suffix_3_0_i6);
	init_label(mercury__list__remove_suffix_3_0_i1);
BEGIN_CODE

/* code for predicate list__remove_suffix/3 in mode 0 */
Define_entry(mercury__list__remove_suffix_3_0);
	incr_sp(5);
	{ detstackvar(5) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) r4; }
	{ detstackvar(3) = (Integer) r2; }
	{ r1 = (Integer) r2; }
	{ r5 = (Integer) r2; }
	{ r2 = (Integer) r3; }

	{ Declare_entry(mercury__list__length_2_0);
	  call(ENTRY(mercury__list__length_2_0),
		LABEL(mercury__list__remove_suffix_3_0_i2),
		LABEL(mercury__list__remove_suffix_3_0)); }

Define_label(mercury__list__remove_suffix_3_0_i2);
	update_prof_current_proc(LABEL(mercury__list__remove_suffix_3_0));

	{ detstackvar(4) = (Integer) r3; }
	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__list__length_2_0);
	  call(ENTRY(mercury__list__length_2_0),
		LABEL(mercury__list__remove_suffix_3_0_i3),
		LABEL(mercury__list__remove_suffix_3_0)); }

Define_label(mercury__list__remove_suffix_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__remove_suffix_3_0));

	{ r2 = (Integer) detstackvar(3); }
	{ r1 = (Integer) r3; }
	{ r3 = ((Integer) detstackvar(4) - (Integer) r1); }
	{ r4 = (Integer) detstackvar(1); }

	{ Declare_entry(mercury__list__split_list_4_0);
	  call(ENTRY(mercury__list__split_list_4_0),
		LABEL(mercury__list__remove_suffix_3_0_i4),
		LABEL(mercury__list__remove_suffix_3_0)); }

Define_label(mercury__list__remove_suffix_3_0_i4);
	update_prof_current_proc(LABEL(mercury__list__remove_suffix_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__remove_suffix_3_0_i1); }
	{ detstackvar(1) = (Integer) r5; }
	{ r2 = (Integer) detstackvar(3); }
	{ r3 = (Integer) detstackvar(2); }
	{ r4 = (Integer) r6; }

	{ Declare_entry(mercury____Unify___list_1_0);
	  call(ENTRY(mercury____Unify___list_1_0),
		LABEL(mercury__list__remove_suffix_3_0_i6),
		LABEL(mercury__list__remove_suffix_3_0)); }

Define_label(mercury__list__remove_suffix_3_0_i6);
	update_prof_current_proc(LABEL(mercury__list__remove_suffix_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__remove_suffix_3_0_i1); }
	{ r5 = (Integer) detstackvar(1); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__remove_suffix_3_0_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__merge_3_0);
Declare_label(mercury__list__merge_3_0_i4);
Declare_label(mercury__list__merge_3_0_i5);
Declare_label(mercury__list__merge_3_0_i3);
Declare_label(mercury__list__merge_3_0_i7);
Declare_label(mercury__list__merge_3_0_i2);
Declare_label(mercury__list__merge_3_0_i10);
Declare_label(mercury__list__merge_3_0_i1);

BEGIN_MODULE(mercury__list_module5)
	init_entry(mercury__list__merge_3_0);
	init_label(mercury__list__merge_3_0_i4);
	init_label(mercury__list__merge_3_0_i5);
	init_label(mercury__list__merge_3_0_i3);
	init_label(mercury__list__merge_3_0_i7);
	init_label(mercury__list__merge_3_0_i2);
	init_label(mercury__list__merge_3_0_i10);
	init_label(mercury__list__merge_3_0_i1);
BEGIN_CODE

/* code for predicate list__merge/3 in mode 0 */
Define_entry(mercury__list__merge_3_0);
	incr_sp(9);
	{ detstackvar(9) = (Integer) succip; }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(5) = (Integer) r3; }
	{ detstackvar(8) = (Integer) r1; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__merge_3_0_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(7) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__merge_3_0_i2); }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ detstackvar(6) = 1; }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(7); }
	{ r5 = (Integer) r4; }
	{ r4 = (Integer) detstackvar(4); }

	{ Declare_entry(mercury__compare_3_0);
	  call(ENTRY(mercury__compare_3_0),
		LABEL(mercury__list__merge_3_0_i4),
		LABEL(mercury__list__merge_3_0)); }

Define_label(mercury__list__merge_3_0_i4);
	update_prof_current_proc(LABEL(mercury__list__merge_3_0));

	{ if ((1 != (Integer) r2))
		GOTO_LABEL(mercury__list__merge_3_0_i3); }
	{ r1 = (Integer) detstackvar(1); }
	{ detstackvar(1) = (Integer) detstackvar(7); }
	{ r2 = (Integer) r1; }
	{ r1 = (Integer) detstackvar(8); }
	{ r3 = (Integer) detstackvar(5); }

	{ localcall(mercury__list__merge_3_0,
		LABEL(mercury__list__merge_3_0_i5),
		LABEL(mercury__list__merge_3_0)); }

Define_label(mercury__list__merge_3_0_i5);
	update_prof_current_proc(LABEL(mercury__list__merge_3_0));

	{ tag_incr_hp(r1, mktag(0), 3); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ field(mktag(0), (Integer) r1, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r1, 2) = (Integer) r4; }
	{ GOTO_LABEL(mercury__list__merge_3_0_i10); }
Define_label(mercury__list__merge_3_0_i3);
	{ detstackvar(1) = (Integer) detstackvar(4); }
	{ r1 = (Integer) detstackvar(8); }
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(3); }

	{ localcall(mercury__list__merge_3_0,
		LABEL(mercury__list__merge_3_0_i7),
		LABEL(mercury__list__merge_3_0)); }

Define_label(mercury__list__merge_3_0_i7);
	update_prof_current_proc(LABEL(mercury__list__merge_3_0));

	{ tag_incr_hp(r1, mktag(0), 3); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ field(mktag(0), (Integer) r1, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r1, 2) = (Integer) r4; }
	{ GOTO_LABEL(mercury__list__merge_3_0_i10); }
Define_label(mercury__list__merge_3_0_i2);
	{ r1 = (Integer) detstackvar(2); }
Define_label(mercury__list__merge_3_0_i10);
	{ r4 = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(9); }
	decr_sp(9);

	{ proceed(); }
Define_label(mercury__list__merge_3_0_i1);
	{ r4 = (Integer) detstackvar(5); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(9); }
	decr_sp(9);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__merge_and_remove_dups_3_0);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i3);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i5);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i4);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i8);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i7);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i10);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i2);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i13);
Declare_label(mercury__list__merge_and_remove_dups_3_0_i1);

BEGIN_MODULE(mercury__list_module6)
	init_entry(mercury__list__merge_and_remove_dups_3_0);
	init_label(mercury__list__merge_and_remove_dups_3_0_i3);
	init_label(mercury__list__merge_and_remove_dups_3_0_i5);
	init_label(mercury__list__merge_and_remove_dups_3_0_i4);
	init_label(mercury__list__merge_and_remove_dups_3_0_i8);
	init_label(mercury__list__merge_and_remove_dups_3_0_i7);
	init_label(mercury__list__merge_and_remove_dups_3_0_i10);
	init_label(mercury__list__merge_and_remove_dups_3_0_i2);
	init_label(mercury__list__merge_and_remove_dups_3_0_i13);
	init_label(mercury__list__merge_and_remove_dups_3_0_i1);
BEGIN_CODE

/* code for predicate list__merge_and_remove_dups/3 in mode 0 */
Define_entry(mercury__list__merge_and_remove_dups_3_0);
	incr_sp(9);
	{ detstackvar(9) = (Integer) succip; }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(5) = (Integer) r3; }
	{ detstackvar(6) = (Integer) r1; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(8) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i2); }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(8); }
	{ r5 = (Integer) r4; }
	{ r4 = (Integer) detstackvar(4); }

	{ Declare_entry(mercury__compare_3_0);
	  call(ENTRY(mercury__compare_3_0),
		LABEL(mercury__list__merge_and_remove_dups_3_0_i3),
		LABEL(mercury__list__merge_and_remove_dups_3_0)); }

Define_label(mercury__list__merge_and_remove_dups_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__merge_and_remove_dups_3_0));

	{ detstackvar(7) = (Integer) r2; }
	{ if (((Integer) r2 != 1))
		GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i4); }
	{ r1 = (Integer) detstackvar(6); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) detstackvar(5); }

	{ localcall(mercury__list__merge_and_remove_dups_3_0,
		LABEL(mercury__list__merge_and_remove_dups_3_0_i5),
		LABEL(mercury__list__merge_and_remove_dups_3_0)); }

Define_label(mercury__list__merge_and_remove_dups_3_0_i5);
	update_prof_current_proc(LABEL(mercury__list__merge_and_remove_dups_3_0));

	{ tag_incr_hp(r1, mktag(0), 3); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ field(mktag(0), (Integer) r1, 1) = (Integer) detstackvar(8); }
	{ field(mktag(0), (Integer) r1, 2) = (Integer) r4; }
	{ GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i13); }
Define_label(mercury__list__merge_and_remove_dups_3_0_i4);
	{ if (((Integer) detstackvar(7) != 2))
		GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i7); }
	{ r1 = (Integer) detstackvar(6); }
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(3); }

	{ localcall(mercury__list__merge_and_remove_dups_3_0,
		LABEL(mercury__list__merge_and_remove_dups_3_0_i8),
		LABEL(mercury__list__merge_and_remove_dups_3_0)); }

Define_label(mercury__list__merge_and_remove_dups_3_0_i8);
	update_prof_current_proc(LABEL(mercury__list__merge_and_remove_dups_3_0));

	{ tag_incr_hp(r1, mktag(0), 3); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ field(mktag(0), (Integer) r1, 1) = (Integer) detstackvar(4); }
	{ field(mktag(0), (Integer) r1, 2) = (Integer) r4; }
	{ GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i13); }
Define_label(mercury__list__merge_and_remove_dups_3_0_i7);
	{ r1 = (Integer) detstackvar(6); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) detstackvar(5); }

	{ localcall(mercury__list__merge_and_remove_dups_3_0,
		LABEL(mercury__list__merge_and_remove_dups_3_0_i10),
		LABEL(mercury__list__merge_and_remove_dups_3_0)); }

Define_label(mercury__list__merge_and_remove_dups_3_0_i10);
	update_prof_current_proc(LABEL(mercury__list__merge_and_remove_dups_3_0));

	{ r1 = (Integer) r4; }
	{ GOTO_LABEL(mercury__list__merge_and_remove_dups_3_0_i13); }
Define_label(mercury__list__merge_and_remove_dups_3_0_i2);
	{ r1 = (Integer) detstackvar(2); }
Define_label(mercury__list__merge_and_remove_dups_3_0_i13);
	{ r4 = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(9); }
	decr_sp(9);

	{ proceed(); }
Define_label(mercury__list__merge_and_remove_dups_3_0_i1);
	{ r4 = (Integer) detstackvar(5); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(9); }
	decr_sp(9);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__remove_adjacent_dups_2_0);
Declare_label(mercury__list__remove_adjacent_dups_2_0_i4);
Declare_label(mercury__list__remove_adjacent_dups_2_0_i1001);

BEGIN_MODULE(mercury__list_module7)
	init_entry(mercury__list__remove_adjacent_dups_2_0);
	init_label(mercury__list__remove_adjacent_dups_2_0_i4);
	init_label(mercury__list__remove_adjacent_dups_2_0_i1001);
BEGIN_CODE

/* code for predicate list__remove_adjacent_dups/2 in mode 0 */
Define_entry(mercury__list__remove_adjacent_dups_2_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__remove_adjacent_dups_2_0_i1001); }
	{ r3 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r4, 1); }

	incr_sp(1);
	{ Declare_entry(mercury__list__remove_adjacent_dups_2_3_0);
	  call(ENTRY(mercury__list__remove_adjacent_dups_2_3_0),
		LABEL(mercury__list__remove_adjacent_dups_2_0_i4),
		LABEL(mercury__list__remove_adjacent_dups_2_0)); }

Define_label(mercury__list__remove_adjacent_dups_2_0_i4);
	update_prof_current_proc(LABEL(mercury__list__remove_adjacent_dups_2_0));

	{ r3 = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(1); }
	decr_sp(1);

	{ proceed(); }
Define_label(mercury__list__remove_adjacent_dups_2_0_i1001);
	update_prof_current_proc(LABEL(mercury__list__remove_adjacent_dups_2_0));

	{ static const Word mercury_const_3[] = {
		0
	  };
	  r3 = mkword(mktag(0), mercury_const_3); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__remove_dups_2_0);
Declare_label(mercury__list__remove_dups_2_0_i1);
Declare_label(mercury__list__remove_dups_2_0_i2);

BEGIN_MODULE(mercury__list_module8)
	init_entry(mercury__list__remove_dups_2_0);
	init_label(mercury__list__remove_dups_2_0_i1);
	init_label(mercury__list__remove_dups_2_0_i2);
BEGIN_CODE

/* code for predicate list__remove_dups/2 in mode 0 */
Define_entry(mercury__list__remove_dups_2_0);
	incr_sp(3);
	{ detstackvar(3) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r1; }
	{ detstackvar(2) = (Integer) r2; }

	{ Declare_entry(mercury__bintree_set__init_1_0);
	  call(ENTRY(mercury__bintree_set__init_1_0),
		LABEL(mercury__list__remove_dups_2_0_i1),
		LABEL(mercury__list__remove_dups_2_0)); }

Define_label(mercury__list__remove_dups_2_0_i1);
	update_prof_current_proc(LABEL(mercury__list__remove_dups_2_0));

	{ r1 = (Integer) detstackvar(1); }
	{ r3 = (Integer) r2; }
	{ r2 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__list__remove_dups_2_3_0);
	  call(ENTRY(mercury__list__remove_dups_2_3_0),
		LABEL(mercury__list__remove_dups_2_0_i2),
		LABEL(mercury__list__remove_dups_2_0)); }

Define_label(mercury__list__remove_dups_2_0_i2);
	update_prof_current_proc(LABEL(mercury__list__remove_dups_2_0));

	{ r3 = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(3); }
	decr_sp(3);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__member_2_1);
Declare_label(mercury__list__member_2_1_i2);
Declare_label(mercury__list__member_2_1_i1);

BEGIN_MODULE(mercury__list_module9)
	init_entry(mercury__list__member_2_1);
	init_label(mercury__list__member_2_1_i2);
	init_label(mercury__list__member_2_1_i1);
BEGIN_CODE

/* code for predicate list__member/2 in mode 1 */
Define_entry(mercury__list__member_2_1);
	{ mkframe("list__member/2", 2, ENTRY(do_fail)); }
	{ framevar(0) = (Integer) r1; }
	{ framevar(1) = (Integer) r3; }
	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) LABEL(mercury__list__member_2_1_i2); }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__member_2_1_i2); }
	{ r2 = (Integer) field(mktag(0), (Integer) r3, 1); }

	{ succeed(); }
Define_label(mercury__list__member_2_1_i2);
	update_prof_current_proc(LABEL(mercury__list__member_2_1));

	{ modframe(ENTRY(do_fail)); }
	{ if (((tag((Integer) framevar(1)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) framevar(1), 0) == 0)))
		fail(); }
	{ r1 = (Integer) framevar(0); }
	{ r3 = (Integer) field(mktag(0), (Integer) framevar(1), 2); }

	{ localcall(mercury__list__member_2_1,
		LABEL(mercury__list__member_2_1_i1),
		LABEL(mercury__list__member_2_1)); }

Define_label(mercury__list__member_2_1_i1);
	update_prof_current_proc(LABEL(mercury__list__member_2_1));


	{ succeed(); }
END_MODULE

Define_extern_entry(mercury__list__member_2_0);
Declare_label(mercury__list__member_2_0_i4);
Declare_label(mercury__list__member_2_0_i3);
Declare_label(mercury__list__member_2_0_i7);
Declare_label(mercury__list__member_2_0_i6);
Declare_label(mercury__list__member_2_0_i2);
Declare_label(mercury__list__member_2_0_i12);

BEGIN_MODULE(mercury__list_module10)
	init_entry(mercury__list__member_2_0);
	init_label(mercury__list__member_2_0_i4);
	init_label(mercury__list__member_2_0_i3);
	init_label(mercury__list__member_2_0_i7);
	init_label(mercury__list__member_2_0_i6);
	init_label(mercury__list__member_2_0_i2);
	init_label(mercury__list__member_2_0_i12);
BEGIN_CODE

/* code for predicate list__member/2 in mode 0 */
Define_entry(mercury__list__member_2_0);
	incr_sp(6);
	{ detstackvar(6) = (Integer) succip; }
	{ detstackvar(4) = (Integer) curfr; }
	{ LVALUE_CAST(Word,curfr) = (Integer) maxfr; }
	{ detstackvar(5) = (Integer) bt_redoip((Integer) curfr); }
	{ LVALUE_CAST(Word,bt_redoip((Integer) curfr)) = (Integer) LABEL(mercury__list__member_2_0_i2); }
	{ detstackvar(1) = (Integer) r4; }
	{ detstackvar(2) = (Integer) r3; }
	{ detstackvar(3) = (Integer) r2; }
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__member_2_0_i3); }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) r1; }
	{ r5 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r5, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__member_2_0_i4),
		LABEL(mercury__list__member_2_0)); }

Define_label(mercury__list__member_2_0_i4);
	update_prof_current_proc(LABEL(mercury__list__member_2_0));

	{ if ((Integer) r1)
		GOTO_LABEL(mercury__list__member_2_0_i12); }
Define_label(mercury__list__member_2_0_i3);
	{ if (((tag((Integer) detstackvar(1)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(1), 0) == 0)))
		GOTO_LABEL(mercury__list__member_2_0_i6); }
	{ r2 = (Integer) detstackvar(3); }
	{ r3 = (Integer) detstackvar(2); }
	{ r4 = (Integer) field(mktag(0), (Integer) detstackvar(1), 2); }

	{ localcall(mercury__list__member_2_0,
		LABEL(mercury__list__member_2_0_i7),
		LABEL(mercury__list__member_2_0)); }

Define_label(mercury__list__member_2_0_i7);
	update_prof_current_proc(LABEL(mercury__list__member_2_0));

	{ if ((Integer) r1)
		GOTO_LABEL(mercury__list__member_2_0_i12); }
Define_label(mercury__list__member_2_0_i6);
Define_label(mercury__list__member_2_0_i2);
	update_prof_current_proc(LABEL(mercury__list__member_2_0));

	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) detstackvar(5); }
	{ LVALUE_CAST(Word,curfr) = (Integer) detstackvar(4); }
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(6); }
	decr_sp(6);

	{ proceed(); }
Define_label(mercury__list__member_2_0_i12);
	update_prof_current_proc(LABEL(mercury__list__member_2_0));

	{ LVALUE_CAST(Word,maxfr) = (Integer) curfr; }
	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) detstackvar(5); }
	{ LVALUE_CAST(Word,curfr) = (Integer) detstackvar(4); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(6); }
	decr_sp(6);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__member_3_0);
Declare_label(mercury__list__member_3_0_i1);

BEGIN_MODULE(mercury__list_module11)
	init_entry(mercury__list__member_3_0);
	init_label(mercury__list__member_3_0_i1);
BEGIN_CODE

/* code for predicate list__member/3 in mode 0 */
Define_entry(mercury__list__member_3_0);
	{ mkframe("list__member/3", 1, ENTRY(do_fail)); }
	{ r4 = (Integer) r3; }

	{ Declare_entry(mercury__list__append_3_3);
	  call(ENTRY(mercury__list__append_3_3),
		LABEL(mercury__list__member_3_0_i1),
		LABEL(mercury__list__member_3_0)); }

Define_label(mercury__list__member_3_0_i1);
	update_prof_current_proc(LABEL(mercury__list__member_3_0));

	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		redo(); }
	{ r1 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ r4 = (Integer) r3; }

	{ succeed(); }
END_MODULE

Define_extern_entry(mercury__list__length_2_0);
Declare_label(mercury__list__length_2_0_i1);

BEGIN_MODULE(mercury__list_module12)
	init_entry(mercury__list__length_2_0);
	init_label(mercury__list__length_2_0_i1);
BEGIN_CODE

/* code for predicate list__length/2 in mode 0 */
Define_entry(mercury__list__length_2_0);
	{ r3 = 0; }

	incr_sp(1);
	{ detstackvar(1) = (Integer) succip; }
	{ Declare_entry(mercury__list__length_2_3_0);
	  call(ENTRY(mercury__list__length_2_3_0),
		LABEL(mercury__list__length_2_0_i1),
		LABEL(mercury__list__length_2_0)); }

Define_label(mercury__list__length_2_0_i1);
	update_prof_current_proc(LABEL(mercury__list__length_2_0));

	{ r3 = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(1); }
	decr_sp(1);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__length_2_1);

BEGIN_MODULE(mercury__list_module13)
	init_entry(mercury__list__length_2_1);
BEGIN_CODE

/* code for predicate list__length/2 in mode 1 */
Define_entry(mercury__list__length_2_1);
	{ r1 = (Integer) r4; }
	{ r4 = 0; }
	{ r5 = (Integer) r1; }

	{ Declare_entry(mercury__list__length_2_3_1);
	  tailcall(ENTRY(mercury__list__length_2_3_1),
		LABEL(mercury__list__length_2_1)); }
END_MODULE

Define_extern_entry(mercury__list__condense_2_0);
Declare_label(mercury__list__condense_2_0_i4);
Declare_label(mercury__list__condense_2_0_i5);
Declare_label(mercury__list__condense_2_0_i1001);

BEGIN_MODULE(mercury__list_module14)
	init_entry(mercury__list__condense_2_0);
	init_label(mercury__list__condense_2_0_i4);
	init_label(mercury__list__condense_2_0_i5);
	init_label(mercury__list__condense_2_0_i1001);
BEGIN_CODE

/* code for predicate list__condense/2 in mode 0 */
Define_entry(mercury__list__condense_2_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__condense_2_0_i1001); }
	incr_sp(3);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(2) = (Integer) r1; }
	{ r3 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r3, 2); }

	{ localcall(mercury__list__condense_2_0,
		LABEL(mercury__list__condense_2_0_i4),
		LABEL(mercury__list__condense_2_0)); }

Define_label(mercury__list__condense_2_0_i4);
	update_prof_current_proc(LABEL(mercury__list__condense_2_0));

	{ r1 = (Integer) detstackvar(2); }
	{ r2 = (Integer) detstackvar(1); }

	{ Declare_entry(mercury__list__append_3_0);
	  call(ENTRY(mercury__list__append_3_0),
		LABEL(mercury__list__condense_2_0_i5),
		LABEL(mercury__list__condense_2_0)); }

Define_label(mercury__list__condense_2_0_i5);
	update_prof_current_proc(LABEL(mercury__list__condense_2_0));

	{ r3 = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(3); }
	decr_sp(3);

	{ proceed(); }
Define_label(mercury__list__condense_2_0_i1001);
	update_prof_current_proc(LABEL(mercury__list__condense_2_0));

	{ static const Word mercury_const_3[] = {
		0
	  };
	  r3 = mkword(mktag(0), mercury_const_3); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__same_length_2_1);
Declare_label(mercury__list__same_length_2_1_i5);
Declare_label(mercury__list__same_length_2_1_i6);
Declare_label(mercury__list__same_length_2_1_i1);

BEGIN_MODULE(mercury__list_module15)
	init_entry(mercury__list__same_length_2_1);
	init_label(mercury__list__same_length_2_1_i5);
	init_label(mercury__list__same_length_2_1_i6);
	init_label(mercury__list__same_length_2_1_i1);
BEGIN_CODE

/* code for predicate list__same_length/2 in mode 1 */
Define_entry(mercury__list__same_length_2_1);
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__same_length_2_1_i1); }
	{ r5 = 0; }
Define_label(mercury__list__same_length_2_1_i5);
	{ r5 = ((Integer) r5 + 1); }
	{ r3 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r3, 2); }

	{ if (!(((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0))))
		GOTO_LABEL(mercury__list__same_length_2_1_i5); }
	{ static const Word mercury_const_2[] = {
		0
	  };
	  r3 = mkword(mktag(0), mercury_const_2); }
Define_label(mercury__list__same_length_2_1_i6);
	{ r1 = (Integer) r3; }
	{ tag_incr_hp(r3, mktag(0), 3); }
	{ field(mktag(0), (Integer) r3, 0) = 1; }
	{ field(mktag(0), (Integer) r3, 2) = (Integer) r1; }
	{ r5 = ((Integer) r5 - 1); }
	{ if (((Integer) r5 > 0))
		GOTO_LABEL(mercury__list__same_length_2_1_i6); }

	{ proceed(); }
Define_label(mercury__list__same_length_2_1_i1);
	{ static const Word mercury_const_2[] = {
		0
	  };
	  r3 = mkword(mktag(0), mercury_const_2); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__same_length_2_0);
Declare_label(mercury__list__same_length_2_0_i5);
Declare_label(mercury__list__same_length_2_0_i6);
Declare_label(mercury__list__same_length_2_0_i1);

BEGIN_MODULE(mercury__list_module16)
	init_entry(mercury__list__same_length_2_0);
	init_label(mercury__list__same_length_2_0_i5);
	init_label(mercury__list__same_length_2_0_i6);
	init_label(mercury__list__same_length_2_0_i1);
BEGIN_CODE

/* code for predicate list__same_length/2 in mode 0 */
Define_entry(mercury__list__same_length_2_0);
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__same_length_2_0_i1); }
	{ r5 = 0; }
Define_label(mercury__list__same_length_2_0_i5);
	{ r5 = ((Integer) r5 + 1); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r4, 2); }

	{ if (!(((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0))))
		GOTO_LABEL(mercury__list__same_length_2_0_i5); }
	{ static const Word mercury_const_2[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_2); }
Define_label(mercury__list__same_length_2_0_i6);
	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ r5 = ((Integer) r5 - 1); }
	{ if (((Integer) r5 > 0))
		GOTO_LABEL(mercury__list__same_length_2_0_i6); }

	{ proceed(); }
Define_label(mercury__list__same_length_2_0_i1);
	{ static const Word mercury_const_2[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_2); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__same_length_2_2);
Declare_label(mercury__list__same_length_2_2_i1001);
Declare_label(mercury__list__same_length_2_2_i3);
Declare_label(mercury__list__same_length_2_2_i1000);

BEGIN_MODULE(mercury__list_module17)
	init_entry(mercury__list__same_length_2_2);
	init_label(mercury__list__same_length_2_2_i1001);
	init_label(mercury__list__same_length_2_2_i3);
	init_label(mercury__list__same_length_2_2_i1000);
BEGIN_CODE

/* code for predicate list__same_length/2 in mode 2 */
Define_entry(mercury__list__same_length_2_2);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r5) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r5, 0) == 0)))
		GOTO_LABEL(mercury__list__same_length_2_2_i1001); }
	incr_sp(1);
	{ GOTO_LABEL(mercury__list__same_length_2_2_i3); }
Define_label(mercury__list__same_length_2_2_i1001);
	update_prof_current_proc(LABEL(mercury__list__same_length_2_2));

	{ if (!(((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0))))
		GOTO_LABEL(mercury__list__same_length_2_2_i1000); }
	{ r1 = TRUE; }

	{ proceed(); }
Define_label(mercury__list__same_length_2_2_i3);
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(1); }
	decr_sp(1);
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__same_length_2_2_i1000); }
	{ r1 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r1, 2); }
	{ r1 = (Integer) r5; }
	{ r5 = (Integer) field(mktag(0), (Integer) r1, 2); }

	{ localtailcall(mercury__list__same_length_2_2,
		LABEL(mercury__list__same_length_2_2)); }
Define_label(mercury__list__same_length_2_2_i1000);
	update_prof_current_proc(LABEL(mercury__list__same_length_2_2));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__split_list_4_0);
Declare_label(mercury__list__split_list_4_0_i2);
Declare_label(mercury__list__split_list_4_0_i4);
Declare_label(mercury__list__split_list_4_0_i1);

BEGIN_MODULE(mercury__list_module18)
	init_entry(mercury__list__split_list_4_0);
	init_label(mercury__list__split_list_4_0_i2);
	init_label(mercury__list__split_list_4_0_i4);
	init_label(mercury__list__split_list_4_0_i1);
BEGIN_CODE

/* code for predicate list__split_list/4 in mode 0 */
Define_entry(mercury__list__split_list_4_0);
	incr_sp(4);
	{ detstackvar(4) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r4; }
	{ detstackvar(2) = (Integer) r3; }
	{ detstackvar(3) = (Integer) r2; }
	{ if (((Integer) r3 != 0))
		GOTO_LABEL(mercury__list__split_list_4_0_i2); }
	{ r6 = (Integer) r4; }
	{ static const Word mercury_const_3[] = {
		0
	  };
	  r5 = mkword(mktag(0), mercury_const_3); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury__list__split_list_4_0_i2);
	{ if (((Integer) detstackvar(2) <= 0))
		GOTO_LABEL(mercury__list__split_list_4_0_i1); }
	{ if (((tag((Integer) detstackvar(1)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(1), 0) == 0)))
		GOTO_LABEL(mercury__list__split_list_4_0_i1); }
	{ r1 = (Integer) detstackvar(1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r1, 1); }
	{ r2 = (Integer) detstackvar(3); }
	{ r3 = ((Integer) detstackvar(2) - 1); }
	{ r4 = (Integer) field(mktag(0), (Integer) r1, 2); }

	{ localcall(mercury__list__split_list_4_0,
		LABEL(mercury__list__split_list_4_0_i4),
		LABEL(mercury__list__split_list_4_0)); }

Define_label(mercury__list__split_list_4_0_i4);
	update_prof_current_proc(LABEL(mercury__list__split_list_4_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__split_list_4_0_i1); }
	{ r1 = (Integer) r5; }
	{ tag_incr_hp(r5, mktag(0), 3); }
	{ field(mktag(0), (Integer) r5, 0) = 1; }
	{ field(mktag(0), (Integer) r5, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r5, 2) = (Integer) r1; }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury__list__split_list_4_0_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__reverse_2_0);
Declare_label(mercury__list__reverse_2_0_i2);

BEGIN_MODULE(mercury__list_module19)
	init_entry(mercury__list__reverse_2_0);
	init_label(mercury__list__reverse_2_0_i2);
BEGIN_CODE

/* code for predicate list__reverse/2 in mode 0 */
Define_entry(mercury__list__reverse_2_0);
	{ static const Word mercury_const_1[] = {
		0
	  };
	  r3 = mkword(mktag(0), mercury_const_1); }

	incr_sp(1);
	{ detstackvar(1) = (Integer) succip; }
	{ Declare_entry(mercury__list__reverse_2_3_0);
	  call(ENTRY(mercury__list__reverse_2_3_0),
		LABEL(mercury__list__reverse_2_0_i2),
		LABEL(mercury__list__reverse_2_0)); }

Define_label(mercury__list__reverse_2_0_i2);
	update_prof_current_proc(LABEL(mercury__list__reverse_2_0));

	{ r3 = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(1); }
	decr_sp(1);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__delete_3_2);
Declare_label(mercury__list__delete_3_2_i2);
Declare_label(mercury__list__delete_3_2_i3);

BEGIN_MODULE(mercury__list_module20)
	init_entry(mercury__list__delete_3_2);
	init_label(mercury__list__delete_3_2_i2);
	init_label(mercury__list__delete_3_2_i3);
BEGIN_CODE

/* code for predicate list__delete/3 in mode 2 */
Define_entry(mercury__list__delete_3_2);
	{ mkframe("list__delete/3", 2, ENTRY(do_fail)); }
	{ framevar(0) = (Integer) r1; }
	{ framevar(1) = (Integer) r2; }
	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) LABEL(mercury__list__delete_3_2_i2); }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__delete_3_2_i2); }
	{ r3 = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ r4 = (Integer) field(mktag(0), (Integer) r2, 2); }

	{ succeed(); }
Define_label(mercury__list__delete_3_2_i2);
	update_prof_current_proc(LABEL(mercury__list__delete_3_2));

	{ modframe(ENTRY(do_fail)); }
	{ if (((tag((Integer) framevar(1)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) framevar(1), 0) == 0)))
		fail(); }
	{ r1 = (Integer) framevar(0); }
	{ framevar(0) = (Integer) field(mktag(0), (Integer) framevar(1), 1); }
	{ r2 = (Integer) field(mktag(0), (Integer) framevar(1), 2); }

	{ localcall(mercury__list__delete_3_2,
		LABEL(mercury__list__delete_3_2_i3),
		LABEL(mercury__list__delete_3_2)); }

Define_label(mercury__list__delete_3_2_i3);
	update_prof_current_proc(LABEL(mercury__list__delete_3_2));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) framevar(0); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }

	{ succeed(); }
END_MODULE

Define_extern_entry(mercury__list__delete_3_1);
Declare_label(mercury__list__delete_3_1_i3);
Declare_label(mercury__list__delete_3_1_i2);
Declare_label(mercury__list__delete_3_1_i5);

BEGIN_MODULE(mercury__list_module21)
	init_entry(mercury__list__delete_3_1);
	init_label(mercury__list__delete_3_1_i3);
	init_label(mercury__list__delete_3_1_i2);
	init_label(mercury__list__delete_3_1_i5);
BEGIN_CODE

/* code for predicate list__delete/3 in mode 1 */
Define_entry(mercury__list__delete_3_1);
	{ mkframe("list__delete/3", 3, ENTRY(do_fail)); }
	{ framevar(0) = (Integer) r3; }
	{ framevar(1) = (Integer) r1; }
	{ framevar(2) = (Integer) r2; }
	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) LABEL(mercury__list__delete_3_1_i2); }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__delete_3_1_i2); }
	{ r4 = (Integer) framevar(0); }
	{ framevar(0) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ r5 = (Integer) r2; }
	{ r2 = (Integer) r1; }
	{ r4 = (Integer) field(mktag(0), (Integer) r5, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__delete_3_1_i3),
		LABEL(mercury__list__delete_3_1)); }

Define_label(mercury__list__delete_3_1_i3);
	update_prof_current_proc(LABEL(mercury__list__delete_3_1));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__delete_3_1_i2); }
	{ r4 = (Integer) framevar(0); }

	{ succeed(); }
Define_label(mercury__list__delete_3_1_i2);
	update_prof_current_proc(LABEL(mercury__list__delete_3_1));

	{ modframe(ENTRY(do_fail)); }
	{ if (((tag((Integer) framevar(2)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) framevar(2), 0) == 0)))
		fail(); }
	{ r1 = (Integer) framevar(0); }
	{ framevar(0) = (Integer) field(mktag(0), (Integer) framevar(2), 1); }
	{ r2 = (Integer) r1; }
	{ r1 = (Integer) framevar(1); }
	{ r3 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) framevar(2), 2); }

	{ localcall(mercury__list__delete_3_1,
		LABEL(mercury__list__delete_3_1_i5),
		LABEL(mercury__list__delete_3_1)); }

Define_label(mercury__list__delete_3_1_i5);
	update_prof_current_proc(LABEL(mercury__list__delete_3_1));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) framevar(0); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }

	{ succeed(); }
END_MODULE

Define_extern_entry(mercury__list__delete_3_0);
Declare_label(mercury__list__delete_3_0_i4);
Declare_label(mercury__list__delete_3_0_i6);
Declare_label(mercury__list__delete_3_0_i3);
Declare_label(mercury__list__delete_3_0_i9);
Declare_label(mercury__list__delete_3_0_i11);
Declare_label(mercury__list__delete_3_0_i8);
Declare_label(mercury__list__delete_3_0_i2);
Declare_label(mercury__list__delete_3_0_i16);

BEGIN_MODULE(mercury__list_module22)
	init_entry(mercury__list__delete_3_0);
	init_label(mercury__list__delete_3_0_i4);
	init_label(mercury__list__delete_3_0_i6);
	init_label(mercury__list__delete_3_0_i3);
	init_label(mercury__list__delete_3_0_i9);
	init_label(mercury__list__delete_3_0_i11);
	init_label(mercury__list__delete_3_0_i8);
	init_label(mercury__list__delete_3_0_i2);
	init_label(mercury__list__delete_3_0_i16);
BEGIN_CODE

/* code for predicate list__delete/3 in mode 0 */
Define_entry(mercury__list__delete_3_0);
	incr_sp(8);
	{ detstackvar(8) = (Integer) succip; }
	{ detstackvar(6) = (Integer) curfr; }
	{ LVALUE_CAST(Word,curfr) = (Integer) maxfr; }
	{ detstackvar(7) = (Integer) bt_redoip((Integer) curfr); }
	{ LVALUE_CAST(Word,bt_redoip((Integer) curfr)) = (Integer) LABEL(mercury__list__delete_3_0_i2); }
	{ detstackvar(1) = (Integer) r4; }
	{ detstackvar(2) = (Integer) r3; }
	{ detstackvar(4) = (Integer) r5; }
	{ detstackvar(5) = (Integer) r2; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__delete_3_0_i3); }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) r4; }
	{ r6 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r1, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__delete_3_0_i4),
		LABEL(mercury__list__delete_3_0)); }

Define_label(mercury__list__delete_3_0_i4);
	update_prof_current_proc(LABEL(mercury__list__delete_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__delete_3_0_i3); }
	{ r2 = (Integer) detstackvar(5); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = (Integer) detstackvar(3); }

	{ Declare_entry(mercury____Unify___list_1_0);
	  call(ENTRY(mercury____Unify___list_1_0),
		LABEL(mercury__list__delete_3_0_i6),
		LABEL(mercury__list__delete_3_0)); }

Define_label(mercury__list__delete_3_0_i6);
	update_prof_current_proc(LABEL(mercury__list__delete_3_0));

	{ if ((Integer) r1)
		GOTO_LABEL(mercury__list__delete_3_0_i16); }
Define_label(mercury__list__delete_3_0_i3);
	{ if (((tag((Integer) detstackvar(2)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(2), 0) == 0)))
		GOTO_LABEL(mercury__list__delete_3_0_i8); }
	{ if (((tag((Integer) detstackvar(4)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(4), 0) == 0)))
		GOTO_LABEL(mercury__list__delete_3_0_i8); }
	{ r1 = (Integer) detstackvar(2); }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) detstackvar(4), 2); }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r1, 2); }
	{ r2 = (Integer) detstackvar(5); }
	{ r3 = (Integer) field(mktag(0), (Integer) r1, 1); }
	{ r4 = (Integer) field(mktag(0), (Integer) detstackvar(4), 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__delete_3_0_i9),
		LABEL(mercury__list__delete_3_0)); }

Define_label(mercury__list__delete_3_0_i9);
	update_prof_current_proc(LABEL(mercury__list__delete_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__delete_3_0_i8); }
	{ r2 = (Integer) detstackvar(5); }
	{ r3 = (Integer) detstackvar(3); }
	{ r4 = (Integer) detstackvar(1); }
	{ r5 = (Integer) detstackvar(2); }

	{ localcall(mercury__list__delete_3_0,
		LABEL(mercury__list__delete_3_0_i11),
		LABEL(mercury__list__delete_3_0)); }

Define_label(mercury__list__delete_3_0_i11);
	update_prof_current_proc(LABEL(mercury__list__delete_3_0));

	{ if ((Integer) r1)
		GOTO_LABEL(mercury__list__delete_3_0_i16); }
Define_label(mercury__list__delete_3_0_i8);
Define_label(mercury__list__delete_3_0_i2);
	update_prof_current_proc(LABEL(mercury__list__delete_3_0));

	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) detstackvar(7); }
	{ LVALUE_CAST(Word,curfr) = (Integer) detstackvar(6); }
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(8); }
	decr_sp(8);

	{ proceed(); }
Define_label(mercury__list__delete_3_0_i16);
	update_prof_current_proc(LABEL(mercury__list__delete_3_0));

	{ LVALUE_CAST(Word,maxfr) = (Integer) curfr; }
	{ LVALUE_CAST(Word,bt_redoip((Integer) maxfr)) = (Integer) detstackvar(7); }
	{ LVALUE_CAST(Word,curfr) = (Integer) detstackvar(6); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(8); }
	decr_sp(8);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__delete_first_3_0);
Declare_label(mercury__list__delete_first_3_0_i3);
Declare_label(mercury__list__delete_first_3_0_i2);
Declare_label(mercury__list__delete_first_3_0_i5);
Declare_label(mercury__list__delete_first_3_0_i1);
Declare_label(mercury__list__delete_first_3_0_i1000);

BEGIN_MODULE(mercury__list_module23)
	init_entry(mercury__list__delete_first_3_0);
	init_label(mercury__list__delete_first_3_0_i3);
	init_label(mercury__list__delete_first_3_0_i2);
	init_label(mercury__list__delete_first_3_0_i5);
	init_label(mercury__list__delete_first_3_0_i1);
	init_label(mercury__list__delete_first_3_0_i1000);
BEGIN_CODE

/* code for predicate list__delete_first/3 in mode 0 */
Define_entry(mercury__list__delete_first_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__delete_first_3_0_i1000); }
	incr_sp(5);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ detstackvar(2) = (Integer) r4; }
	{ detstackvar(3) = (Integer) r2; }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__delete_first_3_0_i3),
		LABEL(mercury__list__delete_first_3_0)); }

Define_label(mercury__list__delete_first_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__delete_first_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__delete_first_3_0_i2); }
	{ r5 = (Integer) detstackvar(4); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__delete_first_3_0_i2);
	{ r2 = (Integer) detstackvar(3); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = (Integer) detstackvar(2); }

	{ localcall(mercury__list__delete_first_3_0,
		LABEL(mercury__list__delete_first_3_0_i5),
		LABEL(mercury__list__delete_first_3_0)); }

Define_label(mercury__list__delete_first_3_0_i5);
	update_prof_current_proc(LABEL(mercury__list__delete_first_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__delete_first_3_0_i1); }
	{ r1 = (Integer) r5; }
	{ tag_incr_hp(r5, mktag(0), 3); }
	{ field(mktag(0), (Integer) r5, 0) = 1; }
	{ field(mktag(0), (Integer) r5, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r5, 2) = (Integer) r1; }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__delete_first_3_0_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__delete_first_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__delete_first_3_0));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__delete_all_3_0);
Declare_label(mercury__list__delete_all_3_0_i5);
Declare_label(mercury__list__delete_all_3_0_i4);
Declare_label(mercury__list__delete_all_3_0_i8);
Declare_label(mercury__list__delete_all_3_0_i1000);

BEGIN_MODULE(mercury__list_module24)
	init_entry(mercury__list__delete_all_3_0);
	init_label(mercury__list__delete_all_3_0_i5);
	init_label(mercury__list__delete_all_3_0_i4);
	init_label(mercury__list__delete_all_3_0_i8);
	init_label(mercury__list__delete_all_3_0_i1000);
BEGIN_CODE

/* code for predicate list__delete_all/3 in mode 0 */
Define_entry(mercury__list__delete_all_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__delete_all_3_0_i1000); }
	incr_sp(5);
	{ detstackvar(1) = (Integer) r1; }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(3) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(4) = (Integer) r3; }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) r1; }
	{ r5 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(3); }
	{ r6 = (Integer) r4; }
	{ r4 = (Integer) r5; }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__delete_all_3_0_i5),
		LABEL(mercury__list__delete_all_3_0)); }

Define_label(mercury__list__delete_all_3_0_i5);
	update_prof_current_proc(LABEL(mercury__list__delete_all_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__delete_all_3_0_i4); }
	{ r1 = (Integer) detstackvar(1); }
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(4); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ localtailcall(mercury__list__delete_all_3_0,
		LABEL(mercury__list__delete_all_3_0)); }
Define_label(mercury__list__delete_all_3_0_i4);
	{ r1 = (Integer) detstackvar(1); }
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(4); }

	{ localcall(mercury__list__delete_all_3_0,
		LABEL(mercury__list__delete_all_3_0_i8),
		LABEL(mercury__list__delete_all_3_0)); }

Define_label(mercury__list__delete_all_3_0_i8);
	update_prof_current_proc(LABEL(mercury__list__delete_all_3_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(3); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__delete_all_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__delete_all_3_0));

	{ static const Word mercury_const_3[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_3); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__delete_elems_3_0);
Declare_label(mercury__list__delete_elems_3_0_i3);
Declare_label(mercury__list__delete_elems_3_0_i1000);

BEGIN_MODULE(mercury__list_module25)
	init_entry(mercury__list__delete_elems_3_0);
	init_label(mercury__list__delete_elems_3_0_i3);
	init_label(mercury__list__delete_elems_3_0_i1000);
BEGIN_CODE

/* code for predicate list__delete_elems/3 in mode 0 */
Define_entry(mercury__list__delete_elems_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__delete_elems_3_0_i1000); }
	incr_sp(3);
	{ detstackvar(1) = (Integer) r1; }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r4, 1); }

	{ Declare_entry(mercury__list__delete_all_3_0);
	  call(ENTRY(mercury__list__delete_all_3_0),
		LABEL(mercury__list__delete_elems_3_0_i3),
		LABEL(mercury__list__delete_elems_3_0)); }

Define_label(mercury__list__delete_elems_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__delete_elems_3_0));

	{ r1 = (Integer) detstackvar(1); }
	{ r2 = (Integer) r4; }
	{ r3 = (Integer) detstackvar(2); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(3); }
	decr_sp(3);

	{ localtailcall(mercury__list__delete_elems_3_0,
		LABEL(mercury__list__delete_elems_3_0)); }
Define_label(mercury__list__delete_elems_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__delete_elems_3_0));

	{ r4 = (Integer) r2; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__sort_2_0);
Declare_label(mercury__list__sort_2_0_i2);

BEGIN_MODULE(mercury__list_module26)
	init_entry(mercury__list__sort_2_0);
	init_label(mercury__list__sort_2_0_i2);
BEGIN_CODE

/* code for predicate list__sort/2 in mode 0 */
Define_entry(mercury__list__sort_2_0);
	incr_sp(2);
	{ detstackvar(2) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r1; }
	{ static const Word mercury_const_1[] = {
		0
	  };
	  r3 = mkword(mktag(0), mercury_const_1); }

	{ Declare_entry(mercury__list__qsort_3_0);
	  call(ENTRY(mercury__list__qsort_3_0),
		LABEL(mercury__list__sort_2_0_i2),
		LABEL(mercury__list__sort_2_0)); }

Define_label(mercury__list__sort_2_0_i2);
	update_prof_current_proc(LABEL(mercury__list__sort_2_0));

	{ r1 = (Integer) detstackvar(1); }
	{ r2 = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(2); }
	decr_sp(2);

	{ Declare_entry(mercury__list__remove_adjacent_dups_2_0);
	  tailcall(ENTRY(mercury__list__remove_adjacent_dups_2_0),
		LABEL(mercury__list__sort_2_0)); }
END_MODULE

Define_extern_entry(mercury__list__nth_member_search_3_0);
Declare_label(mercury__list__nth_member_search_3_0_i3);
Declare_label(mercury__list__nth_member_search_3_0_i2);
Declare_label(mercury__list__nth_member_search_3_0_i5);
Declare_label(mercury__list__nth_member_search_3_0_i1000);

BEGIN_MODULE(mercury__list_module27)
	init_entry(mercury__list__nth_member_search_3_0);
	init_label(mercury__list__nth_member_search_3_0_i3);
	init_label(mercury__list__nth_member_search_3_0_i2);
	init_label(mercury__list__nth_member_search_3_0_i5);
	init_label(mercury__list__nth_member_search_3_0_i1000);
BEGIN_CODE

/* code for predicate list__nth_member_search/3 in mode 0 */
Define_entry(mercury__list__nth_member_search_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__nth_member_search_3_0_i1000); }
	incr_sp(5);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(3) = (Integer) r4; }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__nth_member_search_3_0_i3),
		LABEL(mercury__list__nth_member_search_3_0)); }

Define_label(mercury__list__nth_member_search_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__nth_member_search_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__nth_member_search_3_0_i2); }
	{ r5 = 1; }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__nth_member_search_3_0_i2);
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = (Integer) detstackvar(3); }

	{ localcall(mercury__list__nth_member_search_3_0,
		LABEL(mercury__list__nth_member_search_3_0_i5),
		LABEL(mercury__list__nth_member_search_3_0)); }

Define_label(mercury__list__nth_member_search_3_0_i5);
	update_prof_current_proc(LABEL(mercury__list__nth_member_search_3_0));

	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);
	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__nth_member_search_3_0_i1000); }
	{ r1 = (Integer) r5; }
	{ r5 = ((Integer) r1 + 1); }
	{ r1 = TRUE; }

	{ proceed(); }
Define_label(mercury__list__nth_member_search_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__nth_member_search_3_0));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__index0_3_0);
Declare_label(mercury__list__index0_3_0_i2);
Declare_label(mercury__list__index0_3_0_i1000);

BEGIN_MODULE(mercury__list_module28)
	init_entry(mercury__list__index0_3_0);
	init_label(mercury__list__index0_3_0_i2);
	init_label(mercury__list__index0_3_0_i1000);
BEGIN_CODE

/* code for predicate list__index0/3 in mode 0 */
Define_entry(mercury__list__index0_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__index0_3_0_i1000); }
	incr_sp(5);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(3) = (Integer) r4; }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ if (((Integer) r4 != 0))
		GOTO_LABEL(mercury__list__index0_3_0_i2); }
	{ r5 = (Integer) detstackvar(1); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__index0_3_0_i2);
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = ((Integer) detstackvar(3) - 1); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ localtailcall(mercury__list__index0_3_0,
		LABEL(mercury__list__index0_3_0)); }
Define_label(mercury__list__index0_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__index0_3_0));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__index1_3_0);

BEGIN_MODULE(mercury__list_module29)
	init_entry(mercury__list__index1_3_0);
BEGIN_CODE

/* code for predicate list__index1/3 in mode 0 */
Define_entry(mercury__list__index1_3_0);
	{ r1 = (Integer) r4; }
	{ r4 = ((Integer) r1 - 1); }

	{ Declare_entry(mercury__list__index0_3_0);
	  tailcall(ENTRY(mercury__list__index0_3_0),
		LABEL(mercury__list__index1_3_0)); }
END_MODULE

Define_extern_entry(mercury__list__index0_det_3_0);
Declare_label(mercury__list__index0_det_3_0_i2);
Declare_label(mercury__list__index0_det_3_0_i1000);

BEGIN_MODULE(mercury__list_module30)
	init_entry(mercury__list__index0_det_3_0);
	init_label(mercury__list__index0_det_3_0_i2);
	init_label(mercury__list__index0_det_3_0_i1000);
BEGIN_CODE

/* code for predicate list__index0_det/3 in mode 0 */
Define_entry(mercury__list__index0_det_3_0);
	incr_sp(4);
	{ detstackvar(4) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r2; }
	{ detstackvar(2) = (Integer) r1; }
	{ detstackvar(3) = (Integer) r3; }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) r1; }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) r4; }
	{ r4 = (Integer) r1; }

	{ Declare_entry(mercury__list__index0_3_0);
	  call(ENTRY(mercury__list__index0_3_0),
		LABEL(mercury__list__index0_det_3_0_i2),
		LABEL(mercury__list__index0_det_3_0)); }

Define_label(mercury__list__index0_det_3_0_i2);
	update_prof_current_proc(LABEL(mercury__list__index0_det_3_0));

	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);
	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__index0_det_3_0_i1000); }
	{ r4 = (Integer) r5; }

	{ proceed(); }
Define_label(mercury__list__index0_det_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__index0_det_3_0));

	{ r1 = string_const("list__index: index out of range", 31); }

	{ Declare_entry(mercury__error_1_0);
	  tailcall(ENTRY(mercury__error_1_0),
		LABEL(mercury__list__index0_det_3_0)); }
END_MODULE

Define_extern_entry(mercury__list__index1_det_3_0);

BEGIN_MODULE(mercury__list_module31)
	init_entry(mercury__list__index1_det_3_0);
BEGIN_CODE

/* code for predicate list__index1_det/3 in mode 0 */
Define_entry(mercury__list__index1_det_3_0);
	{ r4 = (Integer) r3; }
	{ r3 = ((Integer) r4 - 1); }

	{ Declare_entry(mercury__list__index0_det_3_0);
	  tailcall(ENTRY(mercury__list__index0_det_3_0),
		LABEL(mercury__list__index1_det_3_0)); }
END_MODULE

Define_extern_entry(mercury__list__zip_3_0);
Declare_label(mercury__list__zip_3_0_i3);
Declare_label(mercury__list__zip_3_0_i1000);

BEGIN_MODULE(mercury__list_module32)
	init_entry(mercury__list__zip_3_0);
	init_label(mercury__list__zip_3_0_i3);
	init_label(mercury__list__zip_3_0_i1000);
BEGIN_CODE

/* code for predicate list__zip/3 in mode 0 */
Define_entry(mercury__list__zip_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__zip_3_0_i1000); }
	incr_sp(2);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r4, 2); }

	{ Declare_entry(mercury__list__zip2_3_0);
	  call(ENTRY(mercury__list__zip2_3_0),
		LABEL(mercury__list__zip_3_0_i3),
		LABEL(mercury__list__zip_3_0)); }

Define_label(mercury__list__zip_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__zip_3_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(2); }
	decr_sp(2);

	{ proceed(); }
Define_label(mercury__list__zip_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__zip_3_0));

	{ r4 = (Integer) r3; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__split3_4_0);
Declare_label(mercury__list__split3_4_0_i2);
Declare_label(mercury__list__split3_4_0_i3);
Declare_label(mercury__list__split3_4_0_i4);
Declare_label(mercury__list__split3_4_0_i5);
Declare_label(mercury__list__split3_4_0_i7);
Declare_label(mercury__list__split3_4_0_i9);
Declare_label(mercury__list__split3_4_0_i11);
Declare_label(mercury__list__split3_4_0_i1);
Declare_label(mercury__list__split3_4_0_i1000);

BEGIN_MODULE(mercury__list_module33)
	init_entry(mercury__list__split3_4_0);
	init_label(mercury__list__split3_4_0_i2);
	init_label(mercury__list__split3_4_0_i3);
	init_label(mercury__list__split3_4_0_i4);
	init_label(mercury__list__split3_4_0_i5);
	init_label(mercury__list__split3_4_0_i7);
	init_label(mercury__list__split3_4_0_i9);
	init_label(mercury__list__split3_4_0_i11);
	init_label(mercury__list__split3_4_0_i1);
	init_label(mercury__list__split3_4_0_i1000);
BEGIN_CODE

/* code for predicate list__split3/4 in mode 0 */
Define_entry(mercury__list__split3_4_0);
	incr_sp(7);
	{ detstackvar(7) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r2; }
	{ detstackvar(2) = (Integer) r6; }
	{ detstackvar(5) = (Integer) r3; }
	{ detstackvar(6) = (Integer) r5; }
	{ r1 = (Integer) r2; }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) r3; }

	{ Declare_entry(mercury__list__length_2_0);
	  call(ENTRY(mercury__list__length_2_0),
		LABEL(mercury__list__split3_4_0_i2),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i2);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ detstackvar(4) = (Integer) r3; }
	{ r1 = (Integer) detstackvar(1); }
	{ r2 = (Integer) detstackvar(6); }

	{ Declare_entry(mercury__list__length_2_0);
	  call(ENTRY(mercury__list__length_2_0),
		LABEL(mercury__list__split3_4_0_i3),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i3);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ detstackvar(3) = (Integer) r3; }
	{ r1 = (Integer) detstackvar(1); }
	{ r2 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__list__length_2_0);
	  call(ENTRY(mercury__list__length_2_0),
		LABEL(mercury__list__split3_4_0_i4),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i4);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ r1 = (Integer) detstackvar(3); }
	{ r2 = ((Integer) r3 - ((Integer) detstackvar(4) + (Integer) r1)); }
	{ detstackvar(3) = ((Integer) detstackvar(4) + (Integer) r2); }
	{ r4 = (Integer) detstackvar(5); }
	{ detstackvar(5) = (Integer) r2; }
	{ r5 = (Integer) r2; }
	{ r2 = (Integer) detstackvar(1); }
	{ r6 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(4); }
	{ r7 = (Integer) r4; }
	{ r4 = (Integer) detstackvar(2); }
	{ r8 = (Integer) r5; }
	{ r5 = (Integer) r7; }

	{ Declare_entry(mercury__list__take_3_0);
	  call(ENTRY(mercury__list__take_3_0),
		LABEL(mercury__list__split3_4_0_i5),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i5);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__split3_4_0_i1); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) detstackvar(3); }
	{ r4 = (Integer) detstackvar(2); }
	{ r5 = (Integer) detstackvar(6); }

	{ Declare_entry(mercury__list__drop_3_0);
	  call(ENTRY(mercury__list__drop_3_0),
		LABEL(mercury__list__split3_4_0_i7),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i7);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__split3_4_0_i1); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__list__drop_3_1);
	  call(ENTRY(mercury__list__drop_3_1),
		LABEL(mercury__list__split3_4_0_i9),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i9);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__split3_4_0_i1); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) detstackvar(5); }
	{ r4 = (Integer) r5; }

	{ Declare_entry(mercury__list__take_3_1);
	  call(ENTRY(mercury__list__take_3_1),
		LABEL(mercury__list__split3_4_0_i11),
		LABEL(mercury__list__split3_4_0)); }

Define_label(mercury__list__split3_4_0_i11);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(7); }
	decr_sp(7);
	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__split3_4_0_i1000); }
	{ r4 = (Integer) r5; }
	{ r1 = TRUE; }

	{ proceed(); }
Define_label(mercury__list__split3_4_0_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(7); }
	decr_sp(7);

	{ proceed(); }
Define_label(mercury__list__split3_4_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__split3_4_0));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__duplicate_3_0);
Declare_label(mercury__list__duplicate_3_0_i2);
Declare_label(mercury__list__duplicate_3_0_i1);

BEGIN_MODULE(mercury__list_module34)
	init_entry(mercury__list__duplicate_3_0);
	init_label(mercury__list__duplicate_3_0_i2);
	init_label(mercury__list__duplicate_3_0_i1);
BEGIN_CODE

/* code for predicate list__duplicate/3 in mode 0 */
Define_entry(mercury__list__duplicate_3_0);
	incr_sp(4);
	{ detstackvar(4) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r2; }
	{ detstackvar(2) = (Integer) r3; }
	{ detstackvar(3) = (Integer) r1; }
	{ if (((Integer) r2 <= 0))
		GOTO_LABEL(mercury__list__duplicate_3_0_i1); }
	{ r4 = (Integer) r2; }
	{ r2 = ((Integer) r4 - 1); }

	{ localcall(mercury__list__duplicate_3_0,
		LABEL(mercury__list__duplicate_3_0_i2),
		LABEL(mercury__list__duplicate_3_0)); }

Define_label(mercury__list__duplicate_3_0_i2);
	update_prof_current_proc(LABEL(mercury__list__duplicate_3_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury__list__duplicate_3_0_i1);
	{ static const Word mercury_const_4[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_4); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__chunk_3_0);
Declare_label(mercury__list__chunk_3_0_i2);

BEGIN_MODULE(mercury__list_module35)
	init_entry(mercury__list__chunk_3_0);
	init_label(mercury__list__chunk_3_0_i2);
BEGIN_CODE

/* code for predicate list__chunk/3 in mode 0 */
Define_entry(mercury__list__chunk_3_0);
	{ static const Word mercury_const_1[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_1); }
	{ r5 = (Integer) r3; }

	incr_sp(1);
	{ detstackvar(1) = (Integer) succip; }
	{ Declare_entry(mercury__list__chunk_2_5_0);
	  call(ENTRY(mercury__list__chunk_2_5_0),
		LABEL(mercury__list__chunk_3_0_i2),
		LABEL(mercury__list__chunk_3_0)); }

Define_label(mercury__list__chunk_3_0_i2);
	update_prof_current_proc(LABEL(mercury__list__chunk_3_0));

	{ r4 = (Integer) r6; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(1); }
	decr_sp(1);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__length_2_3_0);
Declare_label(mercury__list__length_2_3_0_i3);
Declare_label(mercury__list__length_2_3_0_i4);
Declare_label(mercury__list__length_2_3_0_i1);

BEGIN_MODULE(mercury__list_module36)
	init_entry(mercury__list__length_2_3_0);
	init_label(mercury__list__length_2_3_0_i3);
	init_label(mercury__list__length_2_3_0_i4);
	init_label(mercury__list__length_2_3_0_i1);
BEGIN_CODE

/* code for predicate list__length_2/3 in mode 0 */
Define_entry(mercury__list__length_2_3_0);
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__length_2_3_0_i1); }
	{ r5 = 0; }
Define_label(mercury__list__length_2_3_0_i3);
	{ r5 = ((Integer) r5 + 1); }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r4, 2); }
	{ r4 = (Integer) r3; }
	{ r3 = ((Integer) r4 + 1); }

	{ if (!(((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0))))
		GOTO_LABEL(mercury__list__length_2_3_0_i3); }
	{ r4 = (Integer) r3; }
Define_label(mercury__list__length_2_3_0_i4);
	{ r5 = ((Integer) r5 - 1); }
	{ if (((Integer) r5 > 0))
		GOTO_LABEL(mercury__list__length_2_3_0_i4); }

	{ proceed(); }
Define_label(mercury__list__length_2_3_0_i1);
	{ r4 = (Integer) r3; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__length_2_3_1);
Declare_label(mercury__list__length_2_3_1_i1000);
Declare_label(mercury__list__length_2_3_1_i1001);

BEGIN_MODULE(mercury__list_module37)
	init_entry(mercury__list__length_2_3_1);
	init_label(mercury__list__length_2_3_1_i1000);
	init_label(mercury__list__length_2_3_1_i1001);
BEGIN_CODE

/* code for predicate list__length_2/3 in mode 1 */
Define_entry(mercury__list__length_2_3_1);
	{ detstackvar(0) = (Integer) succip; }
	{ if (!(((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0))))
		GOTO_LABEL(mercury__list__length_2_3_1_i1000); }
	{ if (((Integer) r5 != (Integer) r4))
		GOTO_LABEL(mercury__list__length_2_3_1_i1001); }
	{ r1 = TRUE; }

	{ proceed(); }
Define_label(mercury__list__length_2_3_1_i1000);
	update_prof_current_proc(LABEL(mercury__list__length_2_3_1));

	{ r1 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r1, 2); }
	{ r1 = (Integer) r4; }
	{ r4 = ((Integer) r1 + 1); }

	{ localtailcall(mercury__list__length_2_3_1,
		LABEL(mercury__list__length_2_3_1)); }
Define_label(mercury__list__length_2_3_1_i1001);
	update_prof_current_proc(LABEL(mercury__list__length_2_3_1));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__reverse_2_3_0);
Declare_label(mercury__list__reverse_2_3_0_i4);
Declare_label(mercury__list__reverse_2_3_0_i5);
Declare_label(mercury__list__reverse_2_3_0_i1);

BEGIN_MODULE(mercury__list_module38)
	init_entry(mercury__list__reverse_2_3_0);
	init_label(mercury__list__reverse_2_3_0_i4);
	init_label(mercury__list__reverse_2_3_0_i5);
	init_label(mercury__list__reverse_2_3_0_i1);
BEGIN_CODE

/* code for predicate list__reverse_2/3 in mode 0 */
Define_entry(mercury__list__reverse_2_3_0);
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__reverse_2_3_0_i1); }
	{ r6 = 0; }
Define_label(mercury__list__reverse_2_3_0_i4);
	{ r6 = ((Integer) r6 + 1); }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r4, 2); }
	{ r5 = (Integer) r3; }
	{ tag_incr_hp(r3, mktag(0), 3); }
	{ field(mktag(0), (Integer) r3, 0) = 1; }
	{ field(mktag(0), (Integer) r3, 1) = (Integer) field(mktag(0), (Integer) r4, 1); }
	{ field(mktag(0), (Integer) r3, 2) = (Integer) r5; }

	{ if (!(((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0))))
		GOTO_LABEL(mercury__list__reverse_2_3_0_i4); }
	{ r4 = (Integer) r3; }
Define_label(mercury__list__reverse_2_3_0_i5);
	{ r6 = ((Integer) r6 - 1); }
	{ if (((Integer) r6 > 0))
		GOTO_LABEL(mercury__list__reverse_2_3_0_i5); }

	{ proceed(); }
Define_label(mercury__list__reverse_2_3_0_i1);
	{ r4 = (Integer) r3; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__qsort_3_0);
Declare_label(mercury__list__qsort_3_0_i3);
Declare_label(mercury__list__qsort_3_0_i4);
Declare_label(mercury__list__qsort_3_0_i1000);

BEGIN_MODULE(mercury__list_module39)
	init_entry(mercury__list__qsort_3_0);
	init_label(mercury__list__qsort_3_0_i3);
	init_label(mercury__list__qsort_3_0_i4);
	init_label(mercury__list__qsort_3_0_i1000);
BEGIN_CODE

/* code for predicate list__qsort/3 in mode 0 */
Define_entry(mercury__list__qsort_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__qsort_3_0_i1000); }
	incr_sp(4);
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(3) = (Integer) r1; }
	{ detstackvar(1) = (Integer) r3; }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) field(mktag(0), (Integer) r4, 2); }
	{ r5 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__list__partition_4_0);
	  call(ENTRY(mercury__list__partition_4_0),
		LABEL(mercury__list__qsort_3_0_i3),
		LABEL(mercury__list__qsort_3_0)); }

Define_label(mercury__list__qsort_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__qsort_3_0));

	{ r1 = (Integer) detstackvar(1); }
	{ detstackvar(1) = (Integer) r4; }
	{ r2 = (Integer) r1; }
	{ r1 = (Integer) detstackvar(3); }
	{ r3 = (Integer) r2; }
	{ r2 = (Integer) r5; }

	{ localcall(mercury__list__qsort_3_0,
		LABEL(mercury__list__qsort_3_0_i4),
		LABEL(mercury__list__qsort_3_0)); }

Define_label(mercury__list__qsort_3_0_i4);
	update_prof_current_proc(LABEL(mercury__list__qsort_3_0));

	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(1); }
	{ tag_incr_hp(r3, mktag(0), 3); }
	{ field(mktag(0), (Integer) r3, 0) = 1; }
	{ field(mktag(0), (Integer) r3, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r3, 2) = (Integer) r4; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ localtailcall(mercury__list__qsort_3_0,
		LABEL(mercury__list__qsort_3_0)); }
Define_label(mercury__list__qsort_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__qsort_3_0));

	{ r4 = (Integer) r3; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__partition_4_0);
Declare_label(mercury__list__partition_4_0_i6);
Declare_label(mercury__list__partition_4_0_i7);
Declare_label(mercury__list__partition_4_0_i5);
Declare_label(mercury__list__partition_4_0_i9);
Declare_label(mercury__list__partition_4_0_i1000);

BEGIN_MODULE(mercury__list_module40)
	init_entry(mercury__list__partition_4_0);
	init_label(mercury__list__partition_4_0_i6);
	init_label(mercury__list__partition_4_0_i7);
	init_label(mercury__list__partition_4_0_i5);
	init_label(mercury__list__partition_4_0_i9);
	init_label(mercury__list__partition_4_0_i1000);
BEGIN_CODE

/* code for predicate list__partition/4 in mode 0 */
Define_entry(mercury__list__partition_4_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__partition_4_0_i1000); }
	incr_sp(6);
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(5) = (Integer) r1; }
	{ detstackvar(3) = 1; }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__compare_3_0);
	  call(ENTRY(mercury__compare_3_0),
		LABEL(mercury__list__partition_4_0_i6),
		LABEL(mercury__list__partition_4_0)); }

Define_label(mercury__list__partition_4_0_i6);
	update_prof_current_proc(LABEL(mercury__list__partition_4_0));

	{ if ((1 != (Integer) r2))
		GOTO_LABEL(mercury__list__partition_4_0_i5); }
	{ r1 = (Integer) detstackvar(5); }
	{ r2 = (Integer) detstackvar(4); }
	{ r3 = (Integer) detstackvar(1); }

	{ localcall(mercury__list__partition_4_0,
		LABEL(mercury__list__partition_4_0_i7),
		LABEL(mercury__list__partition_4_0)); }

Define_label(mercury__list__partition_4_0_i7);
	update_prof_current_proc(LABEL(mercury__list__partition_4_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(6); }
	decr_sp(6);

	{ proceed(); }
Define_label(mercury__list__partition_4_0_i5);
	{ r1 = (Integer) detstackvar(5); }
	{ r2 = (Integer) detstackvar(4); }
	{ r3 = (Integer) detstackvar(1); }

	{ localcall(mercury__list__partition_4_0,
		LABEL(mercury__list__partition_4_0_i9),
		LABEL(mercury__list__partition_4_0)); }

Define_label(mercury__list__partition_4_0_i9);
	update_prof_current_proc(LABEL(mercury__list__partition_4_0));

	{ r1 = (Integer) r5; }
	{ tag_incr_hp(r5, mktag(0), 3); }
	{ field(mktag(0), (Integer) r5, 0) = 1; }
	{ field(mktag(0), (Integer) r5, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r5, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(6); }
	decr_sp(6);

	{ proceed(); }
Define_label(mercury__list__partition_4_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__partition_4_0));

	{ static const Word mercury_const_4[] = {
		0
	  };
	  r5 = mkword(mktag(0), mercury_const_4); }
	{ static const Word mercury_const_3[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_3); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__remove_dups_2_3_0);
Declare_label(mercury__list__remove_dups_2_3_0_i5);
Declare_label(mercury__list__remove_dups_2_3_0_i4);
Declare_label(mercury__list__remove_dups_2_3_0_i8);
Declare_label(mercury__list__remove_dups_2_3_0_i9);
Declare_label(mercury__list__remove_dups_2_3_0_i1000);

BEGIN_MODULE(mercury__list_module41)
	init_entry(mercury__list__remove_dups_2_3_0);
	init_label(mercury__list__remove_dups_2_3_0_i5);
	init_label(mercury__list__remove_dups_2_3_0_i4);
	init_label(mercury__list__remove_dups_2_3_0_i8);
	init_label(mercury__list__remove_dups_2_3_0_i9);
	init_label(mercury__list__remove_dups_2_3_0_i1000);
BEGIN_CODE

/* code for predicate list__remove_dups_2/3 in mode 0 */
Define_entry(mercury__list__remove_dups_2_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__remove_dups_2_3_0_i1000); }
	incr_sp(5);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(3) = (Integer) r1; }
	{ detstackvar(4) = (Integer) r3; }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) r1; }
	{ r5 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(2); }
	{ r6 = (Integer) r4; }
	{ r4 = (Integer) r5; }

	{ Declare_entry(mercury__bintree_set__member_2_0);
	  call(ENTRY(mercury__bintree_set__member_2_0),
		LABEL(mercury__list__remove_dups_2_3_0_i5),
		LABEL(mercury__list__remove_dups_2_3_0)); }

Define_label(mercury__list__remove_dups_2_3_0_i5);
	update_prof_current_proc(LABEL(mercury__list__remove_dups_2_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__remove_dups_2_3_0_i4); }
	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) detstackvar(4); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ localtailcall(mercury__list__remove_dups_2_3_0,
		LABEL(mercury__list__remove_dups_2_3_0)); }
Define_label(mercury__list__remove_dups_2_3_0_i4);
	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(4); }
	{ r3 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__bintree_set__insert_3_0);
	  call(ENTRY(mercury__bintree_set__insert_3_0),
		LABEL(mercury__list__remove_dups_2_3_0_i8),
		LABEL(mercury__list__remove_dups_2_3_0)); }

Define_label(mercury__list__remove_dups_2_3_0_i8);
	update_prof_current_proc(LABEL(mercury__list__remove_dups_2_3_0));

	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(1); }
	{ r3 = (Integer) r4; }

	{ localcall(mercury__list__remove_dups_2_3_0,
		LABEL(mercury__list__remove_dups_2_3_0_i9),
		LABEL(mercury__list__remove_dups_2_3_0)); }

Define_label(mercury__list__remove_dups_2_3_0_i9);
	update_prof_current_proc(LABEL(mercury__list__remove_dups_2_3_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__remove_dups_2_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__remove_dups_2_3_0));

	{ static const Word mercury_const_3[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_3); }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__remove_adjacent_dups_2_3_0);
Declare_label(mercury__list__remove_adjacent_dups_2_3_0_i6);
Declare_label(mercury__list__remove_adjacent_dups_2_3_0_i5);
Declare_label(mercury__list__remove_adjacent_dups_2_3_0_i9);
Declare_label(mercury__list__remove_adjacent_dups_2_3_0_i2);

BEGIN_MODULE(mercury__list_module42)
	init_entry(mercury__list__remove_adjacent_dups_2_3_0);
	init_label(mercury__list__remove_adjacent_dups_2_3_0_i6);
	init_label(mercury__list__remove_adjacent_dups_2_3_0_i5);
	init_label(mercury__list__remove_adjacent_dups_2_3_0_i9);
	init_label(mercury__list__remove_adjacent_dups_2_3_0_i2);
BEGIN_CODE

/* code for predicate list__remove_adjacent_dups_2/3 in mode 0 */
Define_entry(mercury__list__remove_adjacent_dups_2_3_0);
	incr_sp(5);
	{ detstackvar(5) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__remove_adjacent_dups_2_3_0_i2); }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(3) = (Integer) r1; }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ r4 = (Integer) r2; }
	{ r2 = (Integer) r1; }
	{ r5 = (Integer) r4; }
	{ r4 = (Integer) detstackvar(2); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__remove_adjacent_dups_2_3_0_i6),
		LABEL(mercury__list__remove_adjacent_dups_2_3_0)); }

Define_label(mercury__list__remove_adjacent_dups_2_3_0_i6);
	update_prof_current_proc(LABEL(mercury__list__remove_adjacent_dups_2_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__remove_adjacent_dups_2_3_0_i5); }
	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(4); }
	{ r3 = (Integer) detstackvar(2); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ localtailcall(mercury__list__remove_adjacent_dups_2_3_0,
		LABEL(mercury__list__remove_adjacent_dups_2_3_0)); }
Define_label(mercury__list__remove_adjacent_dups_2_3_0_i5);
	{ r1 = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(4); }
	{ r3 = (Integer) detstackvar(2); }

	{ localcall(mercury__list__remove_adjacent_dups_2_3_0,
		LABEL(mercury__list__remove_adjacent_dups_2_3_0_i9),
		LABEL(mercury__list__remove_adjacent_dups_2_3_0)); }

Define_label(mercury__list__remove_adjacent_dups_2_3_0_i9);
	update_prof_current_proc(LABEL(mercury__list__remove_adjacent_dups_2_3_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__remove_adjacent_dups_2_3_0_i2);
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) r3; }
	{ tag_incr_hp(field(mktag(0), (Integer) r4, 2), mktag(0), 1); }
	{ field(mktag(0), (Integer) field(mktag(0), (Integer) r4, 2), 0) = 0; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__zip2_3_0);
Declare_label(mercury__list__zip2_3_0_i3);
Declare_label(mercury__list__zip2_3_0_i1000);

BEGIN_MODULE(mercury__list_module43)
	init_entry(mercury__list__zip2_3_0);
	init_label(mercury__list__zip2_3_0_i3);
	init_label(mercury__list__zip2_3_0_i1000);
BEGIN_CODE

/* code for predicate list__zip2/3 in mode 0 */
Define_entry(mercury__list__zip2_3_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury__list__zip2_3_0_i1000); }
	incr_sp(2);
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r3, 1); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r4, 2); }

	{ Declare_entry(mercury__list__zip_3_0);
	  call(ENTRY(mercury__list__zip_3_0),
		LABEL(mercury__list__zip2_3_0_i3),
		LABEL(mercury__list__zip2_3_0)); }

Define_label(mercury__list__zip2_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__zip2_3_0));

	{ r1 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(2); }
	decr_sp(2);

	{ proceed(); }
Define_label(mercury__list__zip2_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__zip2_3_0));

	{ r4 = (Integer) r2; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__take_3_1);
Declare_label(mercury__list__take_3_1_i3);
Declare_label(mercury__list__take_3_1_i2);
Declare_label(mercury__list__take_3_1_i1);

BEGIN_MODULE(mercury__list_module44)
	init_entry(mercury__list__take_3_1);
	init_label(mercury__list__take_3_1_i3);
	init_label(mercury__list__take_3_1_i2);
	init_label(mercury__list__take_3_1_i1);
BEGIN_CODE

/* code for predicate list__take/3 in mode 1 */
Define_entry(mercury__list__take_3_1);
	incr_sp(4);
	{ detstackvar(4) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) r4; }
	{ detstackvar(3) = (Integer) r2; }
	{ if (((Integer) r3 <= 0))
		GOTO_LABEL(mercury__list__take_3_1_i2); }
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__take_3_1_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r4, 1); }
	{ r1 = (Integer) r3; }
	{ r3 = ((Integer) r1 - 1); }
	{ r1 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r1, 2); }

	{ localcall(mercury__list__take_3_1,
		LABEL(mercury__list__take_3_1_i3),
		LABEL(mercury__list__take_3_1)); }

Define_label(mercury__list__take_3_1_i3);
	update_prof_current_proc(LABEL(mercury__list__take_3_1));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__take_3_1_i1); }
	{ r1 = (Integer) r5; }
	{ tag_incr_hp(r5, mktag(0), 3); }
	{ field(mktag(0), (Integer) r5, 0) = 1; }
	{ field(mktag(0), (Integer) r5, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r5, 2) = (Integer) r1; }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury__list__take_3_1_i2);
	{ static const Word mercury_const_6[] = {
		0
	  };
	  r5 = mkword(mktag(0), mercury_const_6); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury__list__take_3_1_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__take_3_0);
Declare_label(mercury__list__take_3_0_i3);
Declare_label(mercury__list__take_3_0_i2);
Declare_label(mercury__list__take_3_0_i1);

BEGIN_MODULE(mercury__list_module45)
	init_entry(mercury__list__take_3_0);
	init_label(mercury__list__take_3_0_i3);
	init_label(mercury__list__take_3_0_i2);
	init_label(mercury__list__take_3_0_i1);
BEGIN_CODE

/* code for predicate list__take/3 in mode 0 */
Define_entry(mercury__list__take_3_0);
	incr_sp(5);
	{ detstackvar(5) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) r5; }
	{ detstackvar(3) = (Integer) r2; }
	{ detstackvar(4) = (Integer) r4; }
	{ if (((Integer) r3 <= 0))
		GOTO_LABEL(mercury__list__take_3_0_i2); }
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__take_3_0_i1); }
	{ if (((tag((Integer) r5) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r5, 0) == 0)))
		GOTO_LABEL(mercury__list__take_3_0_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r5, 2); }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r4, 2); }
	{ detstackvar(4) = ((Integer) r3 - 1); }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r4, 1); }
	{ r6 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r5, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury__list__take_3_0_i3),
		LABEL(mercury__list__take_3_0)); }

Define_label(mercury__list__take_3_0_i3);
	update_prof_current_proc(LABEL(mercury__list__take_3_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury__list__take_3_0_i1); }
	{ r2 = (Integer) detstackvar(3); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = (Integer) detstackvar(2); }
	{ r5 = (Integer) detstackvar(1); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ localtailcall(mercury__list__take_3_0,
		LABEL(mercury__list__take_3_0)); }
Define_label(mercury__list__take_3_0_i2);
	{ if (!(((tag((Integer) detstackvar(2)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(2), 0) == 0))))
		GOTO_LABEL(mercury__list__take_3_0_i1); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
Define_label(mercury__list__take_3_0_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__drop_3_1);
Declare_label(mercury__list__drop_3_1_i2);
Declare_label(mercury__list__drop_3_1_i1000);

BEGIN_MODULE(mercury__list_module46)
	init_entry(mercury__list__drop_3_1);
	init_label(mercury__list__drop_3_1_i2);
	init_label(mercury__list__drop_3_1_i1000);
BEGIN_CODE

/* code for predicate list__drop/3 in mode 1 */
Define_entry(mercury__list__drop_3_1);
	incr_sp(4);
	{ detstackvar(4) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(3) = (Integer) r4; }
	{ if (((Integer) r3 <= 0))
		GOTO_LABEL(mercury__list__drop_3_1_i2); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__drop_3_1_i1000); }
	{ r1 = (Integer) r3; }
	{ r3 = ((Integer) r1 - 1); }
	{ r1 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r1, 2); }

	{ localtailcall(mercury__list__drop_3_1,
		LABEL(mercury__list__drop_3_1)); }
Define_label(mercury__list__drop_3_1_i2);
	{ r5 = (Integer) detstackvar(3); }
	{ r1 = TRUE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury__list__drop_3_1_i1000);
	update_prof_current_proc(LABEL(mercury__list__drop_3_1));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__drop_3_0);
Declare_label(mercury__list__drop_3_0_i2);
Declare_label(mercury__list__drop_3_0_i1000);

BEGIN_MODULE(mercury__list_module47)
	init_entry(mercury__list__drop_3_0);
	init_label(mercury__list__drop_3_0_i2);
	init_label(mercury__list__drop_3_0_i1000);
BEGIN_CODE

/* code for predicate list__drop/3 in mode 0 */
Define_entry(mercury__list__drop_3_0);
	incr_sp(5);
	{ detstackvar(5) = (Integer) succip; }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(2) = (Integer) r2; }
	{ detstackvar(3) = (Integer) r5; }
	{ detstackvar(4) = (Integer) r4; }
	{ if (((Integer) r3 <= 0))
		GOTO_LABEL(mercury__list__drop_3_0_i2); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury__list__drop_3_0_i1000); }
	{ r1 = (Integer) r3; }
	{ r3 = ((Integer) r1 - 1); }
	{ r1 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r1, 2); }

	{ localtailcall(mercury__list__drop_3_0,
		LABEL(mercury__list__drop_3_0)); }
Define_label(mercury__list__drop_3_0_i2);
	{ r2 = (Integer) detstackvar(2); }
	{ r3 = (Integer) detstackvar(4); }
	{ r4 = (Integer) detstackvar(3); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(5); }
	decr_sp(5);

	{ Declare_entry(mercury____Unify___list_1_0);
	  tailcall(ENTRY(mercury____Unify___list_1_0),
		LABEL(mercury__list__drop_3_0)); }
Define_label(mercury__list__drop_3_0_i1000);
	update_prof_current_proc(LABEL(mercury__list__drop_3_0));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury__list__chunk_2_5_0);
Declare_label(mercury__list__chunk_2_5_0_i9);
Declare_label(mercury__list__chunk_2_5_0_i13);
Declare_label(mercury__list__chunk_2_5_0_i15);
Declare_label(mercury__list__chunk_2_5_0_i2);
Declare_label(mercury__list__chunk_2_5_0_i3);
Declare_label(mercury__list__chunk_2_5_0_i5);

BEGIN_MODULE(mercury__list_module48)
	init_entry(mercury__list__chunk_2_5_0);
	init_label(mercury__list__chunk_2_5_0_i9);
	init_label(mercury__list__chunk_2_5_0_i13);
	init_label(mercury__list__chunk_2_5_0_i15);
	init_label(mercury__list__chunk_2_5_0_i2);
	init_label(mercury__list__chunk_2_5_0_i3);
	init_label(mercury__list__chunk_2_5_0_i5);
BEGIN_CODE

/* code for predicate list__chunk_2/5 in mode 0 */
Define_entry(mercury__list__chunk_2_5_0);
	incr_sp(7);
	{ detstackvar(7) = (Integer) succip; }
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury__list__chunk_2_5_0_i2); }
	{ detstackvar(1) = (Integer) r5; }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(3) = (Integer) r3; }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(5) = (Integer) r1; }
	{ detstackvar(6) = (Integer) r4; }
	{ if (((Integer) r5 <= 1))
		GOTO_LABEL(mercury__list__chunk_2_5_0_i9); }
	{ r6 = (Integer) r2; }
	{ r2 = (Integer) detstackvar(4); }
	{ r6 = (Integer) r4; }
	{ tag_incr_hp(r4, mktag(0), 3); }
	{ field(mktag(0), (Integer) r4, 0) = 1; }
	{ field(mktag(0), (Integer) r4, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r4, 2) = (Integer) r6; }
	{ r6 = (Integer) r5; }
	{ r5 = ((Integer) r6 - 1); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(7); }
	decr_sp(7);

	{ localtailcall(mercury__list__chunk_2_5_0,
		LABEL(mercury__list__chunk_2_5_0)); }
Define_label(mercury__list__chunk_2_5_0_i9);
	{ r1 = (Integer) detstackvar(5); }
	{ tag_incr_hp(r2, mktag(0), 3); }
	{ field(mktag(0), (Integer) r2, 0) = 1; }
	{ field(mktag(0), (Integer) r2, 1) = (Integer) detstackvar(2); }
	{ field(mktag(0), (Integer) r2, 2) = (Integer) detstackvar(6); }

	{ Declare_entry(mercury__list__reverse_2_0);
	  call(ENTRY(mercury__list__reverse_2_0),
		LABEL(mercury__list__chunk_2_5_0_i13),
		LABEL(mercury__list__chunk_2_5_0)); }

Define_label(mercury__list__chunk_2_5_0_i13);
	update_prof_current_proc(LABEL(mercury__list__chunk_2_5_0));

	{ detstackvar(1) = (Integer) r3; }
	{ r1 = (Integer) detstackvar(5); }
	{ r2 = (Integer) detstackvar(4); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(3); }
	{ r5 = (Integer) r4; }
	{ static const Word mercury_const_14[] = {
		0
	  };
	  r4 = mkword(mktag(0), mercury_const_14); }
	{ r6 = (Integer) r5; }
	{ r5 = (Integer) r3; }

	{ localcall(mercury__list__chunk_2_5_0,
		LABEL(mercury__list__chunk_2_5_0_i15),
		LABEL(mercury__list__chunk_2_5_0)); }

Define_label(mercury__list__chunk_2_5_0_i15);
	update_prof_current_proc(LABEL(mercury__list__chunk_2_5_0));

	{ r1 = (Integer) r6; }
	{ tag_incr_hp(r6, mktag(0), 3); }
	{ field(mktag(0), (Integer) r6, 0) = 1; }
	{ field(mktag(0), (Integer) r6, 1) = (Integer) detstackvar(1); }
	{ field(mktag(0), (Integer) r6, 2) = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(7); }
	decr_sp(7);

	{ proceed(); }
Define_label(mercury__list__chunk_2_5_0_i2);
	{ detstackvar(5) = (Integer) r1; }
	{ detstackvar(1) = (Integer) r4; }
	{ if (!(((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0))))
		GOTO_LABEL(mercury__list__chunk_2_5_0_i3); }
	{ static const Word mercury_const_4[] = {
		0
	  };
	  r6 = mkword(mktag(0), mercury_const_4); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(7); }
	decr_sp(7);

	{ proceed(); }
Define_label(mercury__list__chunk_2_5_0_i3);
	{ r1 = (Integer) detstackvar(5); }
	{ r2 = (Integer) detstackvar(1); }

	{ Declare_entry(mercury__list__reverse_2_0);
	  call(ENTRY(mercury__list__reverse_2_0),
		LABEL(mercury__list__chunk_2_5_0_i5),
		LABEL(mercury__list__chunk_2_5_0)); }

Define_label(mercury__list__chunk_2_5_0_i5);
	update_prof_current_proc(LABEL(mercury__list__chunk_2_5_0));

	{ tag_incr_hp(r6, mktag(0), 3); }
	{ field(mktag(0), (Integer) r6, 0) = 1; }
	{ field(mktag(0), (Integer) r6, 1) = (Integer) r3; }
	{ tag_incr_hp(field(mktag(0), (Integer) r6, 2), mktag(0), 1); }
	{ field(mktag(0), (Integer) field(mktag(0), (Integer) r6, 2), 0) = 0; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(7); }
	decr_sp(7);

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury____Unify___list_1_0);
Declare_label(mercury____Unify___list_1_0_i1001);
Declare_label(mercury____Unify___list_1_0_i3);
Declare_label(mercury____Unify___list_1_0_i4);
Declare_label(mercury____Unify___list_1_0_i1);
Declare_label(mercury____Unify___list_1_0_i1000);

BEGIN_MODULE(mercury__list_module49)
	init_entry(mercury____Unify___list_1_0);
	init_label(mercury____Unify___list_1_0_i1001);
	init_label(mercury____Unify___list_1_0_i3);
	init_label(mercury____Unify___list_1_0_i4);
	init_label(mercury____Unify___list_1_0_i1);
	init_label(mercury____Unify___list_1_0_i1000);
BEGIN_CODE

/* code for predicate __Unify__/2 in mode 0 */
Define_entry(mercury____Unify___list_1_0);
	{ detstackvar(0) = (Integer) succip; }
	{ if (((tag((Integer) r4) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r4, 0) == 0)))
		GOTO_LABEL(mercury____Unify___list_1_0_i1001); }
	incr_sp(4);
	{ GOTO_LABEL(mercury____Unify___list_1_0_i3); }
Define_label(mercury____Unify___list_1_0_i1001);
	update_prof_current_proc(LABEL(mercury____Unify___list_1_0));

	{ if (!(((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0))))
		GOTO_LABEL(mercury____Unify___list_1_0_i1000); }
	{ r1 = TRUE; }

	{ proceed(); }
Define_label(mercury____Unify___list_1_0_i3);
	{ if (((tag((Integer) r3) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r3, 0) == 0)))
		GOTO_LABEL(mercury____Unify___list_1_0_i1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r3, 2); }
	{ detstackvar(2) = (Integer) field(mktag(0), (Integer) r4, 2); }
	{ detstackvar(3) = (Integer) r2; }
	{ r1 = (Integer) r3; }
	{ r3 = (Integer) field(mktag(0), (Integer) r1, 1); }
	{ r5 = (Integer) r4; }
	{ r4 = (Integer) field(mktag(0), (Integer) r5, 1); }

	{ Declare_entry(mercury__unify_2_0);
	  call(ENTRY(mercury__unify_2_0),
		LABEL(mercury____Unify___list_1_0_i4),
		LABEL(mercury____Unify___list_1_0)); }

Define_label(mercury____Unify___list_1_0_i4);
	update_prof_current_proc(LABEL(mercury____Unify___list_1_0));

	{ if (!((Integer) r1))
		GOTO_LABEL(mercury____Unify___list_1_0_i1); }
	{ r2 = (Integer) detstackvar(3); }
	{ r3 = (Integer) detstackvar(1); }
	{ r4 = (Integer) detstackvar(2); }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ localtailcall(mercury____Unify___list_1_0,
		LABEL(mercury____Unify___list_1_0)); }
Define_label(mercury____Unify___list_1_0_i1);
	{ r1 = FALSE; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(4); }
	decr_sp(4);

	{ proceed(); }
Define_label(mercury____Unify___list_1_0_i1000);
	update_prof_current_proc(LABEL(mercury____Unify___list_1_0));

	{ r1 = FALSE; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury____Index___list_1_0);
Declare_label(mercury____Index___list_1_0_i2);

BEGIN_MODULE(mercury__list_module50)
	init_entry(mercury____Index___list_1_0);
	init_label(mercury____Index___list_1_0_i2);
BEGIN_CODE

/* code for predicate __Index__/2 in mode 0 */
Define_entry(mercury____Index___list_1_0);
	{ if (((tag((Integer) r2) == mktag(0)) && ((Integer) field(mktag(0), (Integer) r2, 0) == 0)))
		GOTO_LABEL(mercury____Index___list_1_0_i2); }
	{ r3 = 1; }

	{ proceed(); }
Define_label(mercury____Index___list_1_0_i2);
	{ r3 = 0; }

	{ proceed(); }
END_MODULE

Define_extern_entry(mercury____Compare___list_1_0);
Declare_label(mercury____Compare___list_1_0_i2);
Declare_label(mercury____Compare___list_1_0_i4);
Declare_label(mercury____Compare___list_1_0_i5);
Declare_label(mercury____Compare___list_1_0_i6);
Declare_label(mercury____Compare___list_1_0_i9);
Declare_label(mercury____Compare___list_1_0_i11);
Declare_label(mercury____Compare___list_1_0_i10);
Declare_label(mercury____Compare___list_1_0_i14);
Declare_label(mercury____Compare___list_1_0_i8);
Declare_label(mercury____Compare___list_1_0_i7);

BEGIN_MODULE(mercury__list_module51)
	init_entry(mercury____Compare___list_1_0);
	init_label(mercury____Compare___list_1_0_i2);
	init_label(mercury____Compare___list_1_0_i4);
	init_label(mercury____Compare___list_1_0_i5);
	init_label(mercury____Compare___list_1_0_i6);
	init_label(mercury____Compare___list_1_0_i9);
	init_label(mercury____Compare___list_1_0_i11);
	init_label(mercury____Compare___list_1_0_i10);
	init_label(mercury____Compare___list_1_0_i14);
	init_label(mercury____Compare___list_1_0_i8);
	init_label(mercury____Compare___list_1_0_i7);
BEGIN_CODE

/* code for predicate __Compare__/3 in mode 0 */
Define_entry(mercury____Compare___list_1_0);
	incr_sp(8);
	{ detstackvar(8) = (Integer) succip; }
	{ detstackvar(3) = (Integer) r1; }
	{ detstackvar(1) = (Integer) r3; }
	{ detstackvar(4) = (Integer) r4; }
	{ r2 = (Integer) r1; }
	{ tag_incr_hp(r1, mktag(0), 5); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ Declare_entry(mercury____Unify___list_1_0);
	  field(mktag(0), (Integer) r1, 1) = (Integer) ENTRY(mercury____Unify___list_1_0); }
	{ Declare_entry(mercury____Index___list_1_0);
	  field(mktag(0), (Integer) r1, 2) = (Integer) ENTRY(mercury____Index___list_1_0); }
	{ field(mktag(0), (Integer) r1, 3) = (Integer) LABEL(mercury____Compare___list_1_0); }
	{ field(mktag(0), (Integer) r1, 4) = (Integer) r2; }
	{ r5 = (Integer) r2; }
	{ r2 = (Integer) r3; }

	{ Declare_entry(mercury__index_2_0);
	  call(ENTRY(mercury__index_2_0),
		LABEL(mercury____Compare___list_1_0_i2),
		LABEL(mercury____Compare___list_1_0)); }

Define_label(mercury____Compare___list_1_0_i2);
	update_prof_current_proc(LABEL(mercury____Compare___list_1_0));

	{ detstackvar(2) = (Integer) r3; }
	{ tag_incr_hp(r1, mktag(0), 5); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ Declare_entry(mercury____Unify___list_1_0);
	  field(mktag(0), (Integer) r1, 1) = (Integer) ENTRY(mercury____Unify___list_1_0); }
	{ Declare_entry(mercury____Index___list_1_0);
	  field(mktag(0), (Integer) r1, 2) = (Integer) ENTRY(mercury____Index___list_1_0); }
	{ field(mktag(0), (Integer) r1, 3) = (Integer) LABEL(mercury____Compare___list_1_0); }
	{ field(mktag(0), (Integer) r1, 4) = (Integer) detstackvar(3); }
	{ r2 = (Integer) detstackvar(4); }

	{ Declare_entry(mercury__index_2_0);
	  call(ENTRY(mercury__index_2_0),
		LABEL(mercury____Compare___list_1_0_i4),
		LABEL(mercury____Compare___list_1_0)); }

Define_label(mercury____Compare___list_1_0_i4);
	update_prof_current_proc(LABEL(mercury____Compare___list_1_0));

	{ detstackvar(6) = (Integer) r3; }
	{ if (((Integer) detstackvar(2) >= (Integer) r3))
		GOTO_LABEL(mercury____Compare___list_1_0_i5); }
	{ r2 = 1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(8); }
	decr_sp(8);

	{ proceed(); }
Define_label(mercury____Compare___list_1_0_i5);
	{ if (((Integer) detstackvar(2) <= (Integer) detstackvar(6)))
		GOTO_LABEL(mercury____Compare___list_1_0_i6); }
	{ r2 = 2; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(8); }
	decr_sp(8);

	{ proceed(); }
Define_label(mercury____Compare___list_1_0_i6);
	{ if (!(((tag((Integer) detstackvar(1)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(1), 0) == 0))))
		GOTO_LABEL(mercury____Compare___list_1_0_i9); }
	{ if (!(((tag((Integer) detstackvar(4)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(4), 0) == 0))))
		GOTO_LABEL(mercury____Compare___list_1_0_i7); }
	{ r1 = 0; }
	{ GOTO_LABEL(mercury____Compare___list_1_0_i8); }
Define_label(mercury____Compare___list_1_0_i9);
	{ if (((tag((Integer) detstackvar(4)) == mktag(0)) && ((Integer) field(mktag(0), (Integer) detstackvar(4), 0) == 0)))
		GOTO_LABEL(mercury____Compare___list_1_0_i7); }
	{ r1 = (Integer) detstackvar(1); }
	{ detstackvar(1) = (Integer) field(mktag(0), (Integer) r1, 2); }
	{ r2 = (Integer) detstackvar(4); }
	{ detstackvar(4) = (Integer) field(mktag(0), (Integer) r2, 2); }
	{ detstackvar(5) = (Integer) field(mktag(0), (Integer) r2, 1); }
	{ detstackvar(7) = (Integer) field(mktag(0), (Integer) r1, 1); }
	{ r3 = (Integer) r1; }
	{ r1 = (Integer) detstackvar(3); }
	{ r4 = (Integer) r3; }
	{ r3 = (Integer) detstackvar(7); }
	{ r5 = (Integer) r4; }
	{ r4 = (Integer) detstackvar(5); }

	{ Declare_entry(mercury__compare_3_0);
	  call(ENTRY(mercury__compare_3_0),
		LABEL(mercury____Compare___list_1_0_i11),
		LABEL(mercury____Compare___list_1_0)); }

Define_label(mercury____Compare___list_1_0_i11);
	update_prof_current_proc(LABEL(mercury____Compare___list_1_0));

	{ detstackvar(5) = (Integer) r2; }
	{ if (((Integer) r2 == 0))
		GOTO_LABEL(mercury____Compare___list_1_0_i10); }
	{ r1 = (Integer) detstackvar(5); }
	{ GOTO_LABEL(mercury____Compare___list_1_0_i8); }
Define_label(mercury____Compare___list_1_0_i10);
	{ tag_incr_hp(r1, mktag(0), 5); }
	{ field(mktag(0), (Integer) r1, 0) = 1; }
	{ Declare_entry(mercury____Unify___list_1_0);
	  field(mktag(0), (Integer) r1, 1) = (Integer) ENTRY(mercury____Unify___list_1_0); }
	{ Declare_entry(mercury____Index___list_1_0);
	  field(mktag(0), (Integer) r1, 2) = (Integer) ENTRY(mercury____Index___list_1_0); }
	{ field(mktag(0), (Integer) r1, 3) = (Integer) LABEL(mercury____Compare___list_1_0); }
	{ field(mktag(0), (Integer) r1, 4) = (Integer) detstackvar(3); }
	{ r3 = (Integer) detstackvar(1); }
	{ r4 = (Integer) detstackvar(4); }

	{ Declare_entry(mercury__compare_3_0);
	  call(ENTRY(mercury__compare_3_0),
		LABEL(mercury____Compare___list_1_0_i14),
		LABEL(mercury____Compare___list_1_0)); }

Define_label(mercury____Compare___list_1_0_i14);
	update_prof_current_proc(LABEL(mercury____Compare___list_1_0));

	{ r1 = (Integer) r2; }
Define_label(mercury____Compare___list_1_0_i8);
	{ r2 = (Integer) r1; }
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(8); }
	decr_sp(8);

	{ proceed(); }
Define_label(mercury____Compare___list_1_0_i7);
	{ LVALUE_CAST(Word,succip) = (Integer) detstackvar(8); }
	decr_sp(8);

	{ Declare_entry(mercury__compare_error_0_0);
	  tailcall(ENTRY(mercury__compare_error_0_0),
		LABEL(mercury____Compare___list_1_0)); }
END_MODULE
