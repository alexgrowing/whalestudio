// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.Inputs public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse public import Formalism.LocalToGlobal.IndefiniteForms.IndefExample public import Formalism.LocalToGlobal.IndefiniteForms.QuadraticExampleRankThreePackage public import Formalism.QuotientMetricDivisors.ReductionLemmaZero public import Formalism.QuotientMetricDivisors.FinalW public import Formalism.QuotientMetricDivisors.SixthReductionExplicit public import Formalism.MirabolicMackeyTheory.MirabolicIsMackey public import Formalism.DivisorInequality.BaseLevelBoundsWithCovolume public import Formalism.DivisorInequality.DivisorInequalityProofs.EvenDegreeWeightBounds public import Formalism.BranchSandwichDivisors.ChainDenominatorCoupled public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth public import Formalism.LocalToGlobal.Columns.ToHLat public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.PerEmbeddingCoupledBound public import Formalism.LocalToGlobal.KernelLattices.ThDistC
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Inputs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLatLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefUse(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefExample(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ReductionLemmaZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_FinalW(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_SixthReductionExplicit(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicIsMackey(uint8_t builtin);
lean_object* initialize_tree_Formalism_DivisorInequality_BaseLevelBoundsWithCovolume(uint8_t builtin);
lean_object* initialize_tree_Formalism_DivisorInequality_DivisorInequalityProofs_EvenDegreeWeightBounds(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_ChainDenominatorCoupled(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ToHLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_KernelLattices_ThDistC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DivisionHeightBoundStatement(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Inputs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefUse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefExample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_ReductionLemmaZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_FinalW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_SixthReductionExplicit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicIsMackey(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DivisorInequality_BaseLevelBoundsWithCovolume(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DivisorInequality_DivisorInequalityProofs_EvenDegreeWeightBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_ChainDenominatorCoupled(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ToHLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_KernelLattices_ThDistC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
