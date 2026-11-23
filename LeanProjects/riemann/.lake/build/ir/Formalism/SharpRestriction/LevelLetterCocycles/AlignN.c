// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.AlignN
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.ParConsts
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
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_tameList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_tameList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_tameList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_tameList___redArg(lean_object* v_g_1_, lean_object* v_00_u03c7_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toSemiring_5_; 
v___x_4_ = lp_mathlib_ZMod_commRing(v_g_1_);
v_toSemiring_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v___x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_toMonoid_6_; lean_object* v___x_7_; lean_object* v_toOne_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_15_; 
lean_dec_ref(v_00_u03c7_2_);
v_toMonoid_6_ = lean_ctor_get(v_toSemiring_5_, 1);
lean_inc_ref(v_toMonoid_6_);
lean_dec_ref(v_toSemiring_5_);
v___x_7_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_6_);
lean_dec_ref(v_toMonoid_6_);
v_toOne_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_15_ == 0)
{
lean_object* v_unused_16_; 
v_unused_16_ = lean_ctor_get(v___x_7_, 1);
lean_dec(v_unused_16_);
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_toOne_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
lean_inc(v_toOne_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v_toOne_8_);
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_toOne_8_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_toOne_8_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
else
{
lean_object* v_val_17_; lean_object* v_snd_18_; uint8_t v___x_19_; 
lean_dec_ref(v_toSemiring_5_);
v_val_17_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_x_3_, 1);
v_snd_18_ = lean_ctor_get(v_val_17_, 1);
v___x_19_ = lean_unbox(v_snd_18_);
if (v___x_19_ == 0)
{
lean_object* v_fst_20_; lean_object* v___x_21_; lean_object* v_val_22_; lean_object* v_inv_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_fst_20_ = lean_ctor_get(v_val_17_, 0);
lean_inc(v_fst_20_);
lean_dec(v_val_17_);
v___x_21_ = lean_apply_1(v_00_u03c7_2_, v_fst_20_);
v_val_22_ = lean_ctor_get(v___x_21_, 0);
v_inv_23_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_21_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_inv_23_);
lean_inc(v_val_22_);
lean_dec(v___x_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_val_22_);
lean_ctor_set(v___x_25_, 0, v_inv_23_);
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_inv_23_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_val_22_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_fst_31_; lean_object* v___x_32_; 
v_fst_31_ = lean_ctor_get(v_val_17_, 0);
lean_inc(v_fst_31_);
lean_dec(v_val_17_);
v___x_32_ = lean_apply_1(v_00_u03c7_2_, v_fst_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_tameList(lean_object* v_g_33_, lean_object* v_m_34_, lean_object* v_00_u03c7_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_Formalism_MainNotions_tameList___redArg(v_g_33_, v_00_u03c7_35_, v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_tameList___boxed(lean_object* v_g_38_, lean_object* v_m_39_, lean_object* v_00_u03c7_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_MainNotions_tameList(v_g_38_, v_m_39_, v_00_u03c7_40_, v_x_41_);
lean_dec(v_m_39_);
return v_res_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_AlignN(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
