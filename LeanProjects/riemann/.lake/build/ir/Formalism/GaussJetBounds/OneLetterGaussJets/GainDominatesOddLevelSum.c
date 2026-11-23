// Lean compiler output
// Module: Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.OneLetterGaussJets.TheoremATwoFormsOfEntry public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CompanionTheory public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.OneLetterUnramifiedBound public import Formalism.GaussJetBounds.OneLetterGaussJets.SizesRows7
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
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_GainDominatesOddLevelSum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
