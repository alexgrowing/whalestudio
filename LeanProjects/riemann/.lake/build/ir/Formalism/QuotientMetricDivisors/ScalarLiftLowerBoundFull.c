// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundFull
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.StatementK public import Formalism.QuotientMetricDivisors.RatHermLcvTwist public import Formalism.QuotientMetricDivisors.EigenRatHermLcv public import Formalism.QuotientMetricDivisors.ClassSumDualLe public import Formalism.QuotientMetricDivisors.ClassSumDualGeF public import Formalism.QuotientMetricDivisors.UntwistedChoice public import Formalism.QuotientMetricDivisors.HeightBoundExactNorms public import Formalism.QuotientMetricDivisors.Complement2Normaliser public import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
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
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_StatementK(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_EigenRatHermLcv(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualGeF(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_UntwistedChoice(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HeightBoundExactNorms(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_Complement2Normaliser(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_StatementK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_EigenRatHermLcv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualGeF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_UntwistedChoice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HeightBoundExactNorms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_Complement2Normaliser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
