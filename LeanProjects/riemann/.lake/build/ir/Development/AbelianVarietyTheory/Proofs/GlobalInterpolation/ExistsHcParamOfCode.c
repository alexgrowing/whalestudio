// Lean compiler output
// Module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
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
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ScalePolynomialQuantitiesComparisonStatement(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExplicitRanksBasicBoundsLargeScaleStatement(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsHcParamOfCode(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ScalePolynomialQuantitiesComparisonStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExplicitRanksBasicBoundsLargeScaleStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
