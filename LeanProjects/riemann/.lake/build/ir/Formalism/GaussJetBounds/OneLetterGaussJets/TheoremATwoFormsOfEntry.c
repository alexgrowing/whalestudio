// Lean compiler output
// Module: Formalism.GaussJetBounds.OneLetterGaussJets.TheoremATwoFormsOfEntry
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CapLeOddShiftBound public import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitsLogLoss public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TheoremAMonomialOfLemmas public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGen7Of public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGeneric7Of public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TwoFormsOfTheoremA public import Formalism.GaussJetBounds.OneLetterGaussJets.MinWeightSumAddCostAbsBound public import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets
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
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TheoremAMonomialOfLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGen7Of(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGeneric7Of(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_MinWeightSumAddCostAbsBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TheoremAMonomialOfLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGen7Of(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGeneric7Of(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_MinWeightSumAddCostAbsBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
