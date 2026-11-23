// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast___redArg(lean_object* v_w_1_){
_start:
{
lean_inc_ref(v_w_1_);
return v_w_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast___redArg___boxed(lean_object* v_w_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_GlobalTheory_PtTie_isoCast___redArg(v_w_2_);
lean_dec_ref(v_w_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast(lean_object* v_X_4_, lean_object* v_Y_5_, lean_object* v_L_6_, lean_object* v_L_x27_7_, lean_object* v_h_8_, lean_object* v_M_9_, lean_object* v_f_10_, lean_object* v_w_11_){
_start:
{
lean_inc_ref(v_w_11_);
return v_w_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_PtTie_isoCast___boxed(lean_object* v_X_12_, lean_object* v_Y_13_, lean_object* v_L_14_, lean_object* v_L_x27_15_, lean_object* v_h_16_, lean_object* v_M_17_, lean_object* v_f_18_, lean_object* v_w_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_GlobalTheory_PtTie_isoCast(v_X_12_, v_Y_13_, v_L_14_, v_L_x27_15_, v_h_16_, v_M_17_, v_f_18_, v_w_19_);
lean_dec_ref(v_w_19_);
lean_dec_ref(v_f_18_);
lean_dec_ref(v_M_17_);
lean_dec_ref(v_L_x27_15_);
lean_dec_ref(v_L_14_);
lean_dec_ref(v_Y_13_);
lean_dec_ref(v_X_12_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_H1algStatement(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_CombBound4Of(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IsMixedOver(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_Jets_ExistsSecTieFOfTies(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_H1algStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_CombBound4Of(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IsMixedOver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
