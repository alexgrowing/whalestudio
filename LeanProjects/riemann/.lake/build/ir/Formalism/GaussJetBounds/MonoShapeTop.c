// Lean compiler output
// Module: Formalism.GaussJetBounds.MonoShapeTop
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GaussJetProofs.LemmaRA public import Formalism.GaussJetBounds.GaussJetProofs.TheoremAOneMonomialLogLoss public import Formalism.GaussJetBounds.GaussJetProofs.MinorProductSupportTop
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
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_MonoShapeTop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
