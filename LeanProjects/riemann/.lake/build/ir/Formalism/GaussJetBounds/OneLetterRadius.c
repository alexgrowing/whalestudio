// Lean compiler output
// Module: Formalism.GaussJetBounds.OneLetterRadius
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat public import Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity public import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight public import Formalism.GaussJetBounds.GaussJetProofs.LogStep public import Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm public import Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero public import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight public import Formalism.GaussJetBounds.GaussJetProofs.AsmOne
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
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LogStep(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmOne(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_LogStep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
