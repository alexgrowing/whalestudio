// Lean compiler output
// Module: Formalism.DivisorInequality.DivisorInequalityProofs.BaseLevelBoundsWithCovolumeHolds
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.DivisorInequality.StatementObj public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.StepDiii public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.Assembly public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DualMu public import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
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
lean_object* initialize_tree_Formalism_DivisorInequality_StatementObj(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu(uint8_t builtin);
lean_object* initialize_tree_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds(uint8_t builtin) {
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
res = initialize_tree_Formalism_DivisorInequality_StatementObj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
