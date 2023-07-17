// Lean compiler output
// Module: Hybrid.ProofUtils
// Imports: Init Hybrid.Proof Hybrid.ListUtils Std.Data.List.Basic Mathlib.Data.List.Nodup
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_subst__nom(lean_object*, lean_object*, lean_object*);
lean_object* l_Form_new__nom(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__nom_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__svar_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450_(lean_object*);
LEAN_EXPORT lean_object* l_Proof_double_x27_x27_x27_loop(lean_object*, lean_object*);
lean_object* l_nom__subst__nom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__svar_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_x27_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_new__var_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_bulk__subst_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_x27_loop(lean_object*, lean_object*);
lean_object* l_nom__subst__svar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__occurs_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_loop(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Proof_double_x27_x27_x27(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_new__var_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Proof_double_x27_x27_x27_loop___boxed(lean_object*, lean_object*);
lean_object* l_Form_new__var(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__nom_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__occurs_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450____rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_bulk__subst_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450____rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Hybrid_ProofUtils_0__conjunction_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_new__var_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_3, x_9, x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_5(x_6, x_1, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_new__var_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__Form_new__var_match__1_splitter___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__svar_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_3(x_4, x_9, x_2, x_3);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_4(x_5, x_11, x_12, x_2, x_3);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_3(x_6, x_14, x_2, x_3);
return x_15;
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_4(x_7, x_16, x_17, x_2, x_3);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_apply_7(x_8, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__svar_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__nom__subst__svar_match__1_splitter___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_2(x_6, x_15, x_16);
return x_17;
}
case 5:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_1(x_7, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_2(x_8, x_20, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450____rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450____rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Hybrid_ProofUtils_0____private_Hybrid_Form_0__reprForm_match__1_splitter____x40_Hybrid_Form___hyg_2450____rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Hybrid_ProofUtils_0__Form_list__noms_loop_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__occurs_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_1, x_8);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_3(x_4, x_1, x_10, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_2(x_5, x_1, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_3(x_6, x_1, x_15, x_16);
return x_17;
}
default: 
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_apply_6(x_7, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__occurs_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__nom__occurs_match__1_splitter___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__nom_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_3(x_4, x_9, x_2, x_3);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_4(x_5, x_11, x_12, x_2, x_3);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_3(x_6, x_14, x_2, x_3);
return x_15;
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_4(x_7, x_16, x_17, x_2, x_3);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_apply_7(x_8, x_1, x_2, x_3, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__nom__subst__nom_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__nom__subst__nom_match__1_splitter___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Proof_double_x27_x27_x27_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Form_new__nom(x_1);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mod(x_7, x_8);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_9);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_12 = lean_nat_add(x_11, x_8);
lean_dec(x_11);
x_13 = l_nom__subst__nom(x_1, x_12, x_6);
lean_dec(x_6);
return x_13;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Proof_double_x27_x27_x27_loop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Proof_double_x27_x27_x27_loop(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Proof_double_x27_x27_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Form_new__nom(x_1);
x_3 = l_Proof_double_x27_x27_x27_loop(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_bulk__subst_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
x_7 = lean_apply_2(x_5, x_1, x_3);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_3(x_6, x_1, x_3, lean_box(0));
return x_8;
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_2(x_5, x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_apply_5(x_4, x_1, x_10, x_11, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_ProofUtils_0__Form_bulk__subst_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_ProofUtils_0__Form_bulk__subst_match__1_splitter___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_mul(x_7, x_6);
x_9 = l_nom__subst__nom(x_2, x_8, x_6);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Form_new__nom(x_1);
x_3 = l_Proof_Form_double_x27_x27_loop(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_x27_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = l_Form_new__var(x_2);
lean_inc(x_7);
x_8 = l_nom__subst__svar(x_2, x_7, x_6);
x_9 = l_Proof_Form_double_x27_x27_x27_loop(x_6, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_mul(x_10, x_6);
lean_dec(x_6);
x_12 = l_subst__nom(x_9, x_11, x_7);
lean_dec(x_7);
return x_12;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_x27_loop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Proof_Form_double_x27_x27_x27_loop(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Proof_Form_double_x27_x27_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Form_new__nom(x_1);
x_3 = l_Proof_Form_double_x27_x27_x27_loop(x_2, x_1);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Hybrid_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Hybrid_ListUtils(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_List_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_Nodup(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Hybrid_ProofUtils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Hybrid_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Hybrid_ListUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_List_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_Nodup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
