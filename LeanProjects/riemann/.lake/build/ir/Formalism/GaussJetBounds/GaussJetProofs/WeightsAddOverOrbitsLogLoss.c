// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitsLogLoss
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementO public import Formalism.GaussJetBounds.OneLetterRadius public import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight public import Formalism.GaussJetBounds.GaussJetProofs.LemmaRA public import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbits
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
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementO(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
