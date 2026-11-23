// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ___redArg(lean_object* v_Q_1_){
_start:
{
lean_object* v_y_2_; lean_object* v_g0_3_; lean_object* v_c_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_y_2_ = lean_ctor_get(v_Q_1_, 0);
v_g0_3_ = lean_ctor_get(v_Q_1_, 1);
v_c_4_ = lean_ctor_get(v_Q_1_, 2);
v_isSharedCheck_11_ = !lean_is_exclusive(v_Q_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_6_ = v_Q_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_c_4_);
lean_inc(v_g0_3_);
lean_inc(v_y_2_);
lean_dec(v_Q_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_y_2_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_g0_3_);
lean_ctor_set(v_reuseFailAlloc_10_, 2, v_c_4_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ(lean_object* v_D_12_, lean_object* v_B_13_, lean_object* v_P_14_, lean_object* v_j_15_, lean_object* v_X_16_, lean_object* v_ka_17_, lean_object* v_wL_18_, lean_object* v_wF_19_, lean_object* v_G0_20_, lean_object* v_la_21_, lean_object* v_Q_22_, lean_object* v_rq_23_, lean_object* v_th_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ___redArg(v_Q_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ___boxed(lean_object* v_D_26_, lean_object* v_B_27_, lean_object* v_P_28_, lean_object* v_j_29_, lean_object* v_X_30_, lean_object* v_ka_31_, lean_object* v_wL_32_, lean_object* v_wF_33_, lean_object* v_G0_34_, lean_object* v_la_35_, lean_object* v_Q_36_, lean_object* v_rq_37_, lean_object* v_th_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_reQ(v_D_26_, v_B_27_, v_P_28_, v_j_29_, v_X_30_, v_ka_31_, v_wL_32_, v_wF_33_, v_G0_34_, v_la_35_, v_Q_36_, v_rq_37_, v_th_38_);
lean_dec(v_th_38_);
lean_dec(v_rq_37_);
lean_dec_ref(v_G0_34_);
lean_dec_ref(v_wF_33_);
lean_dec_ref(v_wL_32_);
lean_dec_ref(v_ka_31_);
lean_dec_ref(v_X_30_);
lean_dec(v_j_29_);
lean_dec_ref(v_P_28_);
lean_dec_ref(v_B_27_);
lean_dec_ref(v_D_26_);
return v_res_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_WeightedPrimeSumBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsGlobalFamilyQuotientBounded(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_WeightedPrimeSumBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
