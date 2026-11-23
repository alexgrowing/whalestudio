// Lean compiler output
// Module: Formalism.LocalRingCardinality.Lemmas
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.DataLatDefs public import Formalism.LocalRingCardinality.DataKap public import Formalism.LocalRingCardinality.DataExtra public import Formalism.LocalRingCardinality.DataParams public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
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
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataLatDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKap(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataExtra(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataLatDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
