// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataExtra public import Formalism.LocalRingCardinality.HostCls public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.DvdCondNIffCls public import Development.AutomorphicArithmetic.OrbitLabellings.NotIsCsOfGIdx
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
lean_object* lp_mathlib_padicValNat(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_vDG(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_vDG(lean_object* v_D_1_, lean_object* v_u_2_, lean_object* v_w_3_){
_start:
{
lean_object* v_what_u2082_4_; lean_object* v_places_5_; lean_object* v_mem_6_; lean_object* v_resChar_7_; lean_object* v___x_8_; lean_object* v_C_9_; lean_object* v_DGam_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_what_u2082_4_ = lean_ctor_get(v_D_1_, 4);
v_places_5_ = lean_ctor_get(v_what_u2082_4_, 2);
lean_inc_ref(v_places_5_);
v_mem_6_ = lean_ctor_get(v_D_1_, 10);
lean_inc_ref(v_mem_6_);
lean_dec_ref(v_D_1_);
v_resChar_7_ = lean_ctor_get(v_places_5_, 2);
lean_inc_ref(v_resChar_7_);
lean_dec_ref(v_places_5_);
v___x_8_ = lean_apply_1(v_mem_6_, v_u_2_);
v_C_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_C_9_);
lean_dec_ref(v___x_8_);
v_DGam_10_ = lean_ctor_get(v_C_9_, 2);
lean_inc(v_DGam_10_);
lean_dec_ref(v_C_9_);
v___x_11_ = lean_apply_1(v_resChar_7_, v_w_3_);
v___x_12_ = lp_mathlib_padicValNat(v___x_11_, v_DGam_10_);
lean_dec(v___x_11_);
v___x_13_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg___lam__0(lean_object* v_W_14_, lean_object* v_00_u03bc_15_, lean_object* v_u_16_, lean_object* v_w_17_, lean_object* v_hg_18_){
_start:
{
lean_object* v___x_19_; lean_object* v_fst_20_; 
v___x_19_ = lean_apply_4(v_W_14_, v_00_u03bc_15_, v_u_16_, v_w_17_, lean_box(0));
v_fst_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_fst_20_);
lean_dec_ref(v___x_19_);
return v_fst_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg___lam__1(lean_object* v_W_21_, lean_object* v_00_u03bc_22_, lean_object* v_u_23_, lean_object* v_w_24_, lean_object* v_hg_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___x_30_; lean_object* v_snd_31_; lean_object* v___x_32_; 
v___x_30_ = lean_apply_4(v_W_21_, v_00_u03bc_22_, v_u_23_, v_w_24_, lean_box(0));
v_snd_31_ = lean_ctor_get(v___x_30_, 1);
lean_inc(v_snd_31_);
lean_dec_ref(v___x_30_);
v___x_32_ = lean_apply_4(v_snd_31_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg(lean_object* v_Y_33_, lean_object* v_W_34_, lean_object* v_00_u03bc_35_){
_start:
{
lean_object* v_vOf_36_; lean_object* v_Fl_37_; lean_object* v_Vram_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_47_; 
v_vOf_36_ = lean_ctor_get(v_Y_33_, 0);
v_Fl_37_ = lean_ctor_get(v_Y_33_, 1);
v_Vram_38_ = lean_ctor_get(v_Y_33_, 4);
v_isSharedCheck_47_ = !lean_is_exclusive(v_Y_33_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; lean_object* v_unused_49_; 
v_unused_48_ = lean_ctor_get(v_Y_33_, 3);
lean_dec(v_unused_48_);
v_unused_49_ = lean_ctor_get(v_Y_33_, 2);
lean_dec(v_unused_49_);
v___x_40_ = v_Y_33_;
v_isShared_41_ = v_isSharedCheck_47_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_Vram_38_);
lean_inc(v_Fl_37_);
lean_inc(v_vOf_36_);
lean_dec(v_Y_33_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_47_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___x_45_; 
lean_inc(v_00_u03bc_35_);
lean_inc_ref(v_W_34_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg___lam__0), 5, 2);
lean_closure_set(v___f_42_, 0, v_W_34_);
lean_closure_set(v___f_42_, 1, v_00_u03bc_35_);
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg___lam__1), 9, 2);
lean_closure_set(v___f_43_, 0, v_W_34_);
lean_closure_set(v___f_43_, 1, v_00_u03bc_35_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 3, v___f_43_);
lean_ctor_set(v___x_40_, 2, v___f_42_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_vOf_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_Fl_37_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v___f_42_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v___f_43_);
lean_ctor_set(v_reuseFailAlloc_46_, 4, v_Vram_38_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt(lean_object* v_D_50_, lean_object* v_Y_51_, lean_object* v_W_52_, lean_object* v_00_u03bc_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___redArg(v_Y_51_, v_W_52_, v_00_u03bc_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt___boxed(lean_object* v_D_55_, lean_object* v_Y_56_, lean_object* v_W_57_, lean_object* v_00_u03bc_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_MainNotions_WeilJacquetShalikaLaw_TwLoc_Yt(v_D_55_, v_Y_56_, v_W_57_, v_00_u03bc_58_);
lean_dec_ref(v_D_55_);
return v_res_59_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataExtra(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_HostCls(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_FormalGroupSystem(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_DvdCondNIffCls(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_OrbitLabellings_NotIsCsOfGIdx(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_WeilJacquetShalikaLaw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_HostCls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
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
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_FormalGroupSystem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_DvdCondNIffCls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_OrbitLabellings_NotIsCsOfGIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
