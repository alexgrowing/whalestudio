// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.QuotientSettingHolds
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator public import Formalism.RealPlaceAnalysis.IsRightTranslationIsometric public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
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
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_IsRightTranslationIsometric(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_QuotientSettingHolds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_IsRightTranslationIsometric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
