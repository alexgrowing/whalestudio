// Lean compiler output
// Module: Formalism.StatementCM
// Imports: public import Init public meta import Init public import Formalism.StatementOC
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
lean_object* lp_mathlib_NonUnitalNonAssocRing_toHasDistribNeg___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_dualType___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_dualType___lam__0(lean_object* v_l_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_4_, 0, v_l_1_);
v___x_5_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_4_, v_a_2_, v_b_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType___lam__0___boxed(lean_object* v_l_6_, lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lp_tree_Formalism_dualType___lam__0(v_l_6_, v_a_7_, v_b_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType___lam__1(lean_object* v___x_11_, lean_object* v_g_12_){
_start:
{
lean_object* v_val_13_; lean_object* v_inv_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_25_; 
v_val_13_ = lean_ctor_get(v_g_12_, 0);
v_inv_14_ = lean_ctor_get(v_g_12_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_g_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_16_ = v_g_12_;
v_isShared_17_ = v_isSharedCheck_25_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_inv_14_);
lean_inc(v_val_13_);
lean_dec(v_g_12_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_25_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_1064__overap_18_; lean_object* v___x_19_; lean_object* v___x_1065__overap_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_1064__overap_18_ = lp_mathlib_NonUnitalNonAssocRing_toHasDistribNeg___redArg(v___x_11_);
v___x_19_ = lean_apply_1(v___x_1064__overap_18_, v_val_13_);
v___x_1065__overap_20_ = lp_mathlib_NonUnitalNonAssocRing_toHasDistribNeg___redArg(v___x_11_);
v___x_21_ = lean_apply_1(v___x_1065__overap_20_, v_inv_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 1, v___x_21_);
lean_ctor_set(v___x_16_, 0, v___x_19_);
v___x_23_ = v___x_16_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType___lam__1___boxed(lean_object* v___x_26_, lean_object* v_g_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_dualType___lam__1(v___x_26_, v_g_27_);
lean_dec_ref(v___x_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_dualType(lean_object* v_l_29_, lean_object* v_00_u03a6_30_){
_start:
{
lean_object* v___x_31_; lean_object* v_toSemiring_32_; lean_object* v_toMonoid_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_toOne_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_48_; 
lean_inc(v_l_29_);
v___x_31_ = lp_mathlib_ZMod_commRing(v_l_29_);
v_toSemiring_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref(v_toSemiring_32_);
v_toMonoid_33_ = lean_ctor_get(v_toSemiring_32_, 1);
lean_inc_ref(v_toMonoid_33_);
lean_dec_ref(v_toSemiring_32_);
v___x_34_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v___x_31_);
lean_dec_ref(v___x_31_);
v___x_35_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_33_);
lean_dec_ref(v_toMonoid_33_);
v_toOne_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_48_ == 0)
{
lean_object* v_unused_49_; 
v_unused_49_ = lean_ctor_get(v___x_35_, 1);
lean_dec(v_unused_49_);
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_48_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_toOne_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_48_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___x_43_; 
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_dualType___lam__0___boxed), 3, 1);
lean_closure_set(v___f_40_, 0, v_l_29_);
v___f_41_ = lean_alloc_closure((void*)(lp_tree_Formalism_dualType___lam__1___boxed), 2, 1);
lean_closure_set(v___f_41_, 0, v___x_34_);
lean_inc(v_toOne_36_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v_toOne_36_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_toOne_36_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_toOne_36_);
v___x_43_ = v_reuseFailAlloc_47_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
lean_inc_ref(v___x_43_);
lean_inc_ref_n(v___f_40_, 2);
v___x_44_ = lp_mathlib_Multiset_erase___redArg(v___f_40_, v_00_u03a6_30_, v___x_43_);
v___x_45_ = lp_mathlib_Finset_image___redArg(v___f_40_, v___f_41_, v___x_44_);
v___x_46_ = lp_mathlib_Multiset_ndinsert___redArg(v___f_40_, v___x_43_, v___x_45_);
return v___x_46_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_StatementOC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_StatementCM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_StatementOC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
