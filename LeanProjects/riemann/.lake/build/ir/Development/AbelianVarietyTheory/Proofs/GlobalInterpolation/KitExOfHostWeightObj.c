// Lean compiler output
// Module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadCharacterBoundStatement public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValidStatement public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ScalePolynomialQuantitiesComparison(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MPowFiveMulFMulLLe(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRanksRankValFrame(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BadCharacterBoundStatement(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightRequirementOfValidStatement(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SamePointOfSameScale(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_KitExOfHostWeightObj(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ScalePolynomialQuantitiesComparison(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MPowFiveMulFMulLLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRanksRankValFrame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BadCharacterBoundStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightRequirementOfValidStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SamePointOfSameScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
