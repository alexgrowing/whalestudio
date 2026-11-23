// Lean compiler output
// Module: Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes public import Formalism.LocalToGlobal.UnitaryNorms.CharHost public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_IndefiniteRowSideFullHecke_TameGeneratorWindow_tameList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_IndefiniteRowSideFullHecke_TameGeneratorWindow_tameList(lean_object* v_D_1_, lean_object* v_k_2_, lean_object* v_v_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_4_) == 0)
{
lean_object* v_host_5_; lean_object* v_g_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toSemiring_9_; lean_object* v_toMonoid_10_; lean_object* v___x_11_; lean_object* v_toOne_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
lean_dec(v_v_3_);
v_host_5_ = lean_ctor_get(v_D_1_, 1);
lean_inc_ref(v_host_5_);
lean_dec_ref(v_D_1_);
v_g_6_ = lean_ctor_get(v_host_5_, 6);
lean_inc_ref(v_g_6_);
lean_dec_ref(v_host_5_);
v___x_7_ = lean_apply_1(v_g_6_, v_k_2_);
v___x_8_ = lp_mathlib_ZMod_commRing(v___x_7_);
v_toSemiring_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_toSemiring_9_);
lean_dec_ref(v___x_8_);
v_toMonoid_10_ = lean_ctor_get(v_toSemiring_9_, 1);
lean_inc_ref(v_toMonoid_10_);
lean_dec_ref(v_toSemiring_9_);
v___x_11_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_10_);
lean_dec_ref(v_toMonoid_10_);
v_toOne_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 1);
lean_dec(v_unused_20_);
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_toOne_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
lean_inc(v_toOne_12_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v_toOne_12_);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_toOne_12_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_toOne_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_val_21_; lean_object* v_snd_22_; uint8_t v___x_23_; 
v_val_21_ = lean_ctor_get(v_x_4_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_x_4_, 1);
v_snd_22_ = lean_ctor_get(v_val_21_, 1);
v___x_23_ = lean_unbox(v_snd_22_);
if (v___x_23_ == 0)
{
lean_object* v_nd_24_; lean_object* v_fst_25_; lean_object* v_chiT_26_; lean_object* v___x_27_; lean_object* v_val_28_; lean_object* v_inv_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
v_nd_24_ = lean_ctor_get(v_D_1_, 41);
lean_inc_ref(v_nd_24_);
lean_dec_ref(v_D_1_);
v_fst_25_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_fst_25_);
lean_dec(v_val_21_);
v_chiT_26_ = lean_ctor_get(v_nd_24_, 31);
lean_inc_ref(v_chiT_26_);
lean_dec_ref(v_nd_24_);
v___x_27_ = lean_apply_3(v_chiT_26_, v_k_2_, v_v_3_, v_fst_25_);
v_val_28_ = lean_ctor_get(v___x_27_, 0);
v_inv_29_ = lean_ctor_get(v___x_27_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_27_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_inv_29_);
lean_inc(v_val_28_);
lean_dec(v___x_27_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v_val_28_);
lean_ctor_set(v___x_31_, 0, v_inv_29_);
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_inv_29_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_val_28_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
else
{
lean_object* v_nd_37_; lean_object* v_fst_38_; lean_object* v_chiT_39_; lean_object* v___x_40_; 
v_nd_37_ = lean_ctor_get(v_D_1_, 41);
lean_inc_ref(v_nd_37_);
lean_dec_ref(v_D_1_);
v_fst_38_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_fst_38_);
lean_dec(v_val_21_);
v_chiT_39_ = lean_ctor_get(v_nd_37_, 31);
lean_inc_ref(v_chiT_39_);
lean_dec_ref(v_nd_37_);
v___x_40_ = lean_apply_3(v_chiT_39_, v_k_2_, v_v_3_, v_fst_38_);
return v___x_40_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharHost(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_TameGeneratorWindow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharHost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
