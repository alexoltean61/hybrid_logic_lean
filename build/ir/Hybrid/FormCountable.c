// Lean compiler output
// Module: Hybrid.FormCountable
// Imports: Init Mathlib.Data.Countable.Basic Mathlib.Logic.Equiv.List Mathlib.Data.Nat.Pow Hybrid.Form
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
static lean_object* l_Form_encode___closed__3;
LEAN_EXPORT lean_object* l_Form_encode___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__List_isPrefixOf_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_pow2list___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_pow3list___spec__1(lean_object*, lean_object*);
static lean_object* l_Form_encode___closed__8;
static lean_object* l_Form_encode___closed__10;
LEAN_EXPORT lean_object* l_pow2list(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Form_encode(lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__List_isPrefixOf_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pow3list(lean_object*);
static lean_object* l_Form_encode___closed__15;
static lean_object* l_Form_encode___closed__14;
static lean_object* l_Form_encode___closed__13;
static lean_object* l_Form_encode___closed__6;
static lean_object* l_Form_encode___closed__5;
static lean_object* l_Form_encode___closed__1;
static lean_object* l_Form_encode___closed__17;
static lean_object* l_Form_encode___closed__4;
static lean_object* l_Form_encode___closed__16;
lean_object* lean_nat_pow(lean_object*, lean_object*);
static lean_object* l_Form_encode___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Form_encode___closed__7;
static lean_object* l_Form_encode___closed__11;
static lean_object* l_Form_encode___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_squash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter(lean_object*);
static lean_object* l_Form_encode___closed__12;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_pow2list___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_11, x_19);
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_pow(x_21, x_20);
lean_dec(x_20);
x_23 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_24 = lean_nat_pow(x_21, x_23);
lean_dec(x_23);
x_25 = lean_nat_add(x_17, x_19);
lean_dec(x_17);
x_26 = lean_nat_pow(x_21, x_25);
lean_dec(x_25);
x_27 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_28 = lean_nat_pow(x_21, x_27);
lean_dec(x_27);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_pow(x_34, x_33);
lean_dec(x_33);
x_36 = lean_nat_add(x_14, x_32);
lean_dec(x_14);
x_37 = lean_nat_pow(x_34, x_36);
lean_dec(x_36);
x_38 = lean_nat_add(x_30, x_32);
lean_dec(x_30);
x_39 = lean_nat_pow(x_34, x_38);
lean_dec(x_38);
x_40 = lean_nat_add(x_31, x_32);
lean_dec(x_31);
x_41 = lean_nat_pow(x_34, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_37);
lean_ctor_set(x_4, 0, x_35);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_47 = x_6;
} else {
 lean_dec_ref(x_6);
 x_47 = lean_box(0);
}
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_11, x_48);
lean_dec(x_11);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_nat_pow(x_50, x_49);
lean_dec(x_49);
x_52 = lean_nat_add(x_44, x_48);
lean_dec(x_44);
x_53 = lean_nat_pow(x_50, x_52);
lean_dec(x_52);
x_54 = lean_nat_add(x_45, x_48);
lean_dec(x_45);
x_55 = lean_nat_pow(x_50, x_54);
lean_dec(x_54);
x_56 = lean_nat_add(x_46, x_48);
lean_dec(x_46);
x_57 = lean_nat_pow(x_50, x_56);
lean_dec(x_56);
if (lean_is_scalar(x_47)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_47;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_4, 1, x_59);
lean_ctor_set(x_4, 0, x_51);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_63 = x_5;
} else {
 lean_dec_ref(x_5);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_6, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_66 = x_6;
} else {
 lean_dec_ref(x_6);
 x_66 = lean_box(0);
}
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_61, x_67);
lean_dec(x_61);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_pow(x_69, x_68);
lean_dec(x_68);
x_71 = lean_nat_add(x_62, x_67);
lean_dec(x_62);
x_72 = lean_nat_pow(x_69, x_71);
lean_dec(x_71);
x_73 = lean_nat_add(x_64, x_67);
lean_dec(x_64);
x_74 = lean_nat_pow(x_69, x_73);
lean_dec(x_73);
x_75 = lean_nat_add(x_65, x_67);
lean_dec(x_65);
x_76 = lean_nat_pow(x_69, x_75);
lean_dec(x_75);
if (lean_is_scalar(x_66)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_66;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
if (lean_is_scalar(x_63)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_63;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_79);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_83 = x_4;
} else {
 lean_dec_ref(x_4);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_85 = x_5;
} else {
 lean_dec_ref(x_5);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_6, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_88 = x_6;
} else {
 lean_dec_ref(x_6);
 x_88 = lean_box(0);
}
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_82, x_89);
lean_dec(x_82);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_pow(x_91, x_90);
lean_dec(x_90);
x_93 = lean_nat_add(x_84, x_89);
lean_dec(x_84);
x_94 = lean_nat_pow(x_91, x_93);
lean_dec(x_93);
x_95 = lean_nat_add(x_86, x_89);
lean_dec(x_86);
x_96 = lean_nat_pow(x_91, x_95);
lean_dec(x_95);
x_97 = lean_nat_add(x_87, x_89);
lean_dec(x_87);
x_98 = lean_nat_pow(x_91, x_97);
lean_dec(x_97);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_85)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_85;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
if (lean_is_scalar(x_83)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_83;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_2);
x_1 = x_81;
x_2 = x_102;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_pow2list(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_pow2list___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_pow3list___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_11, x_19);
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_pow(x_21, x_20);
lean_dec(x_20);
x_23 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_24 = lean_nat_pow(x_21, x_23);
lean_dec(x_23);
x_25 = lean_nat_add(x_17, x_19);
lean_dec(x_17);
x_26 = lean_nat_pow(x_21, x_25);
lean_dec(x_25);
x_27 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_28 = lean_nat_pow(x_21, x_27);
lean_dec(x_27);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_pow(x_34, x_33);
lean_dec(x_33);
x_36 = lean_nat_add(x_14, x_32);
lean_dec(x_14);
x_37 = lean_nat_pow(x_34, x_36);
lean_dec(x_36);
x_38 = lean_nat_add(x_30, x_32);
lean_dec(x_30);
x_39 = lean_nat_pow(x_34, x_38);
lean_dec(x_38);
x_40 = lean_nat_add(x_31, x_32);
lean_dec(x_31);
x_41 = lean_nat_pow(x_34, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_37);
lean_ctor_set(x_4, 0, x_35);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_47 = x_6;
} else {
 lean_dec_ref(x_6);
 x_47 = lean_box(0);
}
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_11, x_48);
lean_dec(x_11);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_pow(x_50, x_49);
lean_dec(x_49);
x_52 = lean_nat_add(x_44, x_48);
lean_dec(x_44);
x_53 = lean_nat_pow(x_50, x_52);
lean_dec(x_52);
x_54 = lean_nat_add(x_45, x_48);
lean_dec(x_45);
x_55 = lean_nat_pow(x_50, x_54);
lean_dec(x_54);
x_56 = lean_nat_add(x_46, x_48);
lean_dec(x_46);
x_57 = lean_nat_pow(x_50, x_56);
lean_dec(x_56);
if (lean_is_scalar(x_47)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_47;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_4, 1, x_59);
lean_ctor_set(x_4, 0, x_51);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_63 = x_5;
} else {
 lean_dec_ref(x_5);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_6, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_66 = x_6;
} else {
 lean_dec_ref(x_6);
 x_66 = lean_box(0);
}
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_61, x_67);
lean_dec(x_61);
x_69 = lean_unsigned_to_nat(3u);
x_70 = lean_nat_pow(x_69, x_68);
lean_dec(x_68);
x_71 = lean_nat_add(x_62, x_67);
lean_dec(x_62);
x_72 = lean_nat_pow(x_69, x_71);
lean_dec(x_71);
x_73 = lean_nat_add(x_64, x_67);
lean_dec(x_64);
x_74 = lean_nat_pow(x_69, x_73);
lean_dec(x_73);
x_75 = lean_nat_add(x_65, x_67);
lean_dec(x_65);
x_76 = lean_nat_pow(x_69, x_75);
lean_dec(x_75);
if (lean_is_scalar(x_66)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_66;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
if (lean_is_scalar(x_63)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_63;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_79);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_83 = x_4;
} else {
 lean_dec_ref(x_4);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_85 = x_5;
} else {
 lean_dec_ref(x_5);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_6, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_88 = x_6;
} else {
 lean_dec_ref(x_6);
 x_88 = lean_box(0);
}
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_82, x_89);
lean_dec(x_82);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_pow(x_91, x_90);
lean_dec(x_90);
x_93 = lean_nat_add(x_84, x_89);
lean_dec(x_84);
x_94 = lean_nat_pow(x_91, x_93);
lean_dec(x_93);
x_95 = lean_nat_add(x_86, x_89);
lean_dec(x_86);
x_96 = lean_nat_pow(x_91, x_95);
lean_dec(x_95);
x_97 = lean_nat_add(x_87, x_89);
lean_dec(x_87);
x_98 = lean_nat_pow(x_91, x_97);
lean_dec(x_97);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_85)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_85;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
if (lean_is_scalar(x_83)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_83;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_2);
x_1 = x_81;
x_2 = x_102;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_pow3list(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_pow3list___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_squash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_pow2list(x_1);
x_4 = l_pow3list(x_2);
x_5 = l_List_appendTR___rarg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Form_encode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Form_encode___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Form_encode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Form_encode___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Form_encode___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Form_encode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Form_encode___closed__16;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Form_encode(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Form_encode___closed__4;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
x_15 = l_Form_encode___closed__5;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
x_24 = l_Form_encode___closed__6;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = l_Form_encode(x_28);
x_31 = l_Form_encode(x_29);
x_32 = l_squash(x_30, x_31);
x_33 = l_Form_encode___closed__10;
x_34 = l_List_appendTR___rarg(x_33, x_32);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = l_Form_encode(x_35);
x_37 = l_Form_encode___closed__14;
x_38 = l_List_appendTR___rarg(x_37, x_36);
return x_38;
}
default: 
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_39, x_41);
x_43 = l_Form_encode___closed__5;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Form_encode___closed__17;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Form_encode(x_40);
x_52 = l_List_appendTR___rarg(x_50, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Form_encode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Form_encode(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__List_isPrefixOf_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_1, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__List_isPrefixOf_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Hybrid_FormCountable_0__List_isPrefixOf_match__1_splitter___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Hybrid_FormCountable_0__Form_encode_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Countable_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Logic_Equiv_List(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Pow(uint8_t builtin, lean_object*);
lean_object* initialize_Hybrid_Form(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Hybrid_FormCountable(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Countable_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Logic_Equiv_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Pow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Hybrid_Form(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Form_encode___closed__1 = _init_l_Form_encode___closed__1();
lean_mark_persistent(l_Form_encode___closed__1);
l_Form_encode___closed__2 = _init_l_Form_encode___closed__2();
lean_mark_persistent(l_Form_encode___closed__2);
l_Form_encode___closed__3 = _init_l_Form_encode___closed__3();
lean_mark_persistent(l_Form_encode___closed__3);
l_Form_encode___closed__4 = _init_l_Form_encode___closed__4();
lean_mark_persistent(l_Form_encode___closed__4);
l_Form_encode___closed__5 = _init_l_Form_encode___closed__5();
lean_mark_persistent(l_Form_encode___closed__5);
l_Form_encode___closed__6 = _init_l_Form_encode___closed__6();
lean_mark_persistent(l_Form_encode___closed__6);
l_Form_encode___closed__7 = _init_l_Form_encode___closed__7();
lean_mark_persistent(l_Form_encode___closed__7);
l_Form_encode___closed__8 = _init_l_Form_encode___closed__8();
lean_mark_persistent(l_Form_encode___closed__8);
l_Form_encode___closed__9 = _init_l_Form_encode___closed__9();
lean_mark_persistent(l_Form_encode___closed__9);
l_Form_encode___closed__10 = _init_l_Form_encode___closed__10();
lean_mark_persistent(l_Form_encode___closed__10);
l_Form_encode___closed__11 = _init_l_Form_encode___closed__11();
lean_mark_persistent(l_Form_encode___closed__11);
l_Form_encode___closed__12 = _init_l_Form_encode___closed__12();
lean_mark_persistent(l_Form_encode___closed__12);
l_Form_encode___closed__13 = _init_l_Form_encode___closed__13();
lean_mark_persistent(l_Form_encode___closed__13);
l_Form_encode___closed__14 = _init_l_Form_encode___closed__14();
lean_mark_persistent(l_Form_encode___closed__14);
l_Form_encode___closed__15 = _init_l_Form_encode___closed__15();
lean_mark_persistent(l_Form_encode___closed__15);
l_Form_encode___closed__16 = _init_l_Form_encode___closed__16();
lean_mark_persistent(l_Form_encode___closed__16);
l_Form_encode___closed__17 = _init_l_Form_encode___closed__17();
lean_mark_persistent(l_Form_encode___closed__17);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
