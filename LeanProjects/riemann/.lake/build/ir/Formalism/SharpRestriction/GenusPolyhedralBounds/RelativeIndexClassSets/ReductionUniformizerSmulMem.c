// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ZeroGeneratorsLeThetaSpan public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseOrdBd public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_Dp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_Dp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_Dp(lean_object* v_D_1_, lean_object* v_B_2_, lean_object* v_P_3_, lean_object* v_j_4_, lean_object* v_X_5_, lean_object* v_la_6_, lean_object* v_00_u03b9_7_, lean_object* v_y_8_, lean_object* v_u_9_, lean_object* v_t_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_Dp___boxed(lean_object* v_D_12_, lean_object* v_B_13_, lean_object* v_P_14_, lean_object* v_j_15_, lean_object* v_X_16_, lean_object* v_la_17_, lean_object* v_00_u03b9_18_, lean_object* v_y_19_, lean_object* v_u_20_, lean_object* v_t_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_Dp(v_D_12_, v_B_13_, v_P_14_, v_j_15_, v_X_16_, v_la_17_, v_00_u03b9_18_, v_y_19_, v_u_20_, v_t_21_);
lean_dec(v_t_21_);
lean_dec_ref(v_u_20_);
lean_dec(v_y_19_);
lean_dec_ref(v_X_16_);
lean_dec(v_j_15_);
lean_dec_ref(v_P_14_);
lean_dec_ref(v_B_13_);
lean_dec_ref(v_D_12_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ZeroGeneratorsLeThetaSpan(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HasseOrdBd(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HassePresH(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_FinitePtsOfCurve(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ReductionUniformizerSmulMem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ZeroGeneratorsLeThetaSpan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HasseOrdBd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HassePresH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_FinitePtsOfCurve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
