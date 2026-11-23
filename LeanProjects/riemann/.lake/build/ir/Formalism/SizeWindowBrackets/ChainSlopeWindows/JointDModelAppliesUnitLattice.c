// Lean compiler output
// Module: Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv public import Formalism.HarderNarasimhan.ShiftInvariance public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf public import Formalism.SizeWindowBrackets.ChainSlopeWindows.CorollaryModelSideCondition public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
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
lean_object* initialize_tree_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
