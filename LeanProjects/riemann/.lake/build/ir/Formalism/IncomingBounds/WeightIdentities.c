// Lean compiler output
// Module: Formalism.IncomingBounds.WeightIdentities
// Imports: public import Init public meta import Init public import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaF public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd public import Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm public import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd public import Formalism.IncomingBounds.FlowDegreeBounds.AltChooseSumEqZero public import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds public import Formalism.IncomingBounds.FlowDegreeBounds.Cayley public import Formalism.IncomingBounds.FlowDegreeBounds.Series public import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco
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
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_Cayley(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_Series(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_IncomingBounds_WeightIdentities(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_Cayley(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_Series(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
