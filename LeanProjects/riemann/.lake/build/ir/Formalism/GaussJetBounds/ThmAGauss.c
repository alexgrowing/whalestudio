// Lean compiler output
// Module: Formalism.GaussJetBounds.ThmAGauss
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GaussJetProofs.ThmAGaussOf public import Formalism.GaussJetBounds.GaussJetProofs.Transfer public import Formalism.GaussJetBounds.GaussJetProofs.FJEval public import Formalism.GaussJetBounds.GaussJetProofs.Labels
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
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAGaussOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Transfer(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_FJEval(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Labels(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_ThmAGauss(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAGaussOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Transfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_FJEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Labels(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
