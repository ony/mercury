//
// Copyright (C) 2000-2001 The University of Melbourne.
// This file may only be copied under the terms of the GNU Library General
// Public License - see the file COPYING.LIB in the Mercury distribution.
//

// mercury_il.il - This file defines the system runtime types and
// methods that are used when generating code for the .NET backend.
// It is written in Microsoft's IL assembly language. 


// Declare the assemblies we use

.assembly extern mercury { }

.assembly extern mscorlib { 
	.ver 1:0:2411:0
	.publickeytoken = (B7 7A 5C 56 19 34 E0 89 )                         // .z\V.4..
	.hash = (B0 73 F2 4C 14 39 0A 35 25 EA 45 0F 60 58 C3 84   // .s.L.9.5%.E.`X..
           E0 3B E0 95 )      
}

// .assembly extern 'mercury_mcpp' { }

// .assembly extern 'mercury.io' { }

// ------------------------------------------------------------------------

.namespace mercury.runtime {

// Managed C++ can't call or create function pointers.
// So we have to do it in IL.  
// MC++ used to handle this, and then it stopped working, so now it's just
// not supported at all.  I hope it will make a comeback.

.class public TempHack {

.method static default int32 
get_ftn_ptr_typeclass_info_compare() {
	ldftn void ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_compare__typeclass_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_typeclass_info_unify() {
	ldftn int32 ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_unify__typeclass_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object,
		class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_base_typeclass_info_compare() {
	ldftn void ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_compare__base_typeclass_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_base_typeclass_info_unify() {
	ldftn int32 ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_unify__base_typeclass_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object,
		class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_type_info_compare() {
	ldftn void ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_compare__type_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_type_info_unify() {
	ldftn int32 ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_unify__type_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object,
		class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_type_ctor_info_compare() {
	ldftn void ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_compare__type_ctor_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_type_ctor_info_unify() {
	ldftn int32 ['mercury'] 'mercury'.'private_builtin__c_code'::
	do_unify__type_ctor_info_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object,
		class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_pred_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__pred_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_pred_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__pred_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_func_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__func_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_func_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__func_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_float_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__float_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}
.method static default int32 
get_ftn_ptr_float_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__float_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_void_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__void_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}
.method static default int32 
get_ftn_ptr_void_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__void_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_c_pointer_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__c_pointer_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_c_pointer_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__c_pointer_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_string_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__string_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_string_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__string_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_character_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__character_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_character_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__character_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_int_compare() {
	ldftn void ['mercury'] 'mercury'.'builtin__c_code'::
	do_compare__int_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_int_unify() {
	ldftn int32 ['mercury'] 'mercury'.'builtin__c_code'::
	do_unify__int_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_array_compare() {
	ldftn void ['mercury'] 'mercury'.'array__c_code'::
	do_compare__array_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_array_unify() {
	ldftn int32 ['mercury'] 'mercury'.'array__c_code'::
	do_unify__array_1_0(
		class [mscorlib]System.Object[], class [mscorlib]System.Object,
		class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_type_desc_compare() {
	ldftn void ['mercury'] 'mercury'.'std_util__c_code'::
	do_compare__type_desc_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_type_desc_unify() {
	ldftn int32 ['mercury'] 'mercury'.'std_util__c_code'::
	do_unify__type_desc_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_univ_compare() {
	ldftn void ['mercury'] 'mercury'.'std_util__c_code'::
	do_compare__univ_0_0(
		class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default int32 
get_ftn_ptr_univ_unify() {
	ldftn int32 ['mercury'] 'mercury'.'std_util__c_code'::
	do_unify__univ_0_0(
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

} // end of class TempHack

// ------------------------------------------------------------------------

// Implement some classes for boxing values.  Hopefully this is just
// temporary while the box/unbox instructions were broken, apparently
// they work now, so it's just SMOP to get rid of this code.

.class public BoxedInt {

.field public int32 val

.method instance void .ctor(int32 'intval')
{
	ldarg.0
	call	instance void [mscorlib]System.Object::.ctor()

	// set the value
	ldarg.0
	ldarg 'intval'
	stfld int32 ['mercury']mercury.runtime.BoxedInt::val
	ret
}

}

.class public BoxedFloat {

.field public float64 val

.method default void .ctor(float64 'floatval')
{
	newobj instance void ['mscorlib']System.Object::.ctor()
	dup

	// set the value
	ldarg 'floatval'
	stfld float64 ['mercury']mercury.runtime.BoxedFloat::val
	ret
}

}

// ------------------------------------------------------------------------

// The implementation of conversion routines.  Written in IL so that we can
// just plug in an implementation using box/unbox and see if it works.

.class public ConvertImpl {

.method static default class [mscorlib]System.Object ToObject(int32 ival)
{
	ldarg	ival
	box 	class [mscorlib]System.Int32
	ret
}

.method static default class [mscorlib]System.Object ToObject(float64 fval)
{
	ldarg fval
	box 	class [mscorlib]System.Float64
	ret
}

.method static default int32 ToInt32(class [mscorlib]System.Object obj)
{
	ldarg obj

	isinst class ['mscorlib']System.Int32
	unbox 	int32
	ldobj   int32
	ret
}

.method static default float64 ToFloat64(class [mscorlib]System.Object obj)
{
	ldarg obj

	isinst class ['mscorlib']System.Float64
	unbox 	float64
	ldobj   float64
	ret
}


}

// ------------------------------------------------------------------------

// This class implements some specific instances of call/N, mostly used for 
// doing unify and compare.  You can't call using a function pointer in MC++
// so we have to do it in IL.

.class public GenericCall {

.method static default  int32 semidet_call_3(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y') 
{
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	int32 (class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}


.method static default  int32 semidet_call_4(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'X',
	class [mscorlib]System.Object 'Y') 
{
	ldarg 'T1'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	int32 (class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  int32 semidet_call_5(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'T2',
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y')
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	int32 (class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  int32 semidet_call_6(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'T2',
	class [mscorlib]System.Object 'T3', class [mscorlib]System.Object 'X',
	class [mscorlib]System.Object 'Y')
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'T3'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	int32 (class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  int32 semidet_call_7(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'T2',
	class [mscorlib]System.Object 'T3', class [mscorlib]System.Object 'T4',
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y')
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'T3'
	ldarg 'T4'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	int32 (class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}


.method static default  int32 semidet_call_8(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'T2',
	class [mscorlib]System.Object 'T3', class [mscorlib]System.Object 'T4',
	class [mscorlib]System.Object 'T5', class [mscorlib]System.Object 'X',
	class [mscorlib]System.Object 'Y')
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'T3'
	ldarg 'T4'
	ldarg 'T5'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	int32 (class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

	// The result_call methods are intended to interface to polymorphic
	// procedures that have two real parameters, and a variable number of
	// type parameters.

.method static default  void result_call_4(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object[]& 'result', class [mscorlib]System.Object 'X', 
	class [mscorlib]System.Object 'Y') 
{
	ldarg 'result'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	void (class [mscorlib]System.Object[]&, class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  void result_call_5(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', 
	class [mscorlib]System.Object[]& 'result', 
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y') 
{
	ldarg 'T1'
	ldarg 'result'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	void (class [mscorlib]System.Object, class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  void result_call_6(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'T2',
	class [mscorlib]System.Object[]& 'result', 
	class [mscorlib]System.Object 'X', 
	class [mscorlib]System.Object 'Y')
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'result'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	void (class [mscorlib]System.Object,
		class [mscorlib]System.Object, class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  void result_call_7(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', 
	class [mscorlib]System.Object 'T2', class [mscorlib]System.Object 'T3', 
	class [mscorlib]System.Object[]& 'result', 
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y') 
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'T3'
	ldarg 'result'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	void (class [mscorlib]System.Object, class [mscorlib]System.Object,
		class [mscorlib]System.Object, class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  void result_call_8(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', class [mscorlib]System.Object 'T2',
	class [mscorlib]System.Object 'T3', class [mscorlib]System.Object 'T4',
	class [mscorlib]System.Object[]& 'result', 
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y') 
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'T3'
	ldarg 'T4'
	ldarg 'result'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	void (class [mscorlib]System.Object, class [mscorlib]System.Object,
		class [mscorlib]System.Object,
		class [mscorlib]System.Object, class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

.method static default  void result_call_9(class [mscorlib]System.Object 'procedure', 
	class [mscorlib]System.Object 'T1', 
	class [mscorlib]System.Object 'T2', class [mscorlib]System.Object 'T3', 
	class [mscorlib]System.Object 'T4', class [mscorlib]System.Object 'T5', 
	class [mscorlib]System.Object[]& 'result',
	class [mscorlib]System.Object 'X', class [mscorlib]System.Object 'Y') 
{
	ldarg 'T1'
	ldarg 'T2'
	ldarg 'T3'
	ldarg 'T4'
	ldarg 'T5'
	ldarg 'result'
	ldarg 'X'
	ldarg 'Y'
	ldarg 'procedure'
	call 	int32 ['mercury']mercury.runtime.ConvertImpl::ToInt32(class [mscorlib]System.Object)
	calli	void (class [mscorlib]System.Object, class [mscorlib]System.Object,
		class [mscorlib]System.Object, class [mscorlib]System.Object,
		class [mscorlib]System.Object, class [mscorlib]System.Object[]&,
		class [mscorlib]System.Object, class [mscorlib]System.Object)
	ret
}

}

// Call init_state/2 in the IO module.
// This gets called before main runs.
// It has to be written in IL because we call something that might not
// yet be available in a .DLL.

.class public 'Init' {
    .method static default void init_runtime() {
        call void ['mercury']mercury.io::init_state_2_p_0()
    }
}


}


