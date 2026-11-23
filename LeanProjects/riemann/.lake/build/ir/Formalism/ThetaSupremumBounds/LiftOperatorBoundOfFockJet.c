// Lean compiler output
// Module: Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet
// Imports: public import Init public meta import Init public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.Assembly public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.HeightsoundOf public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.BlockIntegralOf public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.ClassSchur public import Mathlib public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq public import Formalism.ThetaSupremumBounds.StatementD public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.DominanceMono public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.FockJet public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.GaussCoord public import Formalism.ThetaSupremumBounds.StatementE
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
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_ClassSchur(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_StatementD(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaSupremumBounds_StatementE(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_ClassSchur(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_StatementD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaSupremumBounds_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
