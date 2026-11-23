// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
// Imports: public import Init public meta import Init public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BoundsIVal public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.GoodDual public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace public import Formalism.BranchSandwichDivisors.StatementJ public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.StepDiii public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
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
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BoundsIVal(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementJ(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BoundsIVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementJ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
