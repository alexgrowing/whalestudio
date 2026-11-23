// Lean compiler output
// Module: Formalism.PadicSubsetSums.StableGradedCounts.ZReuse
// Imports: public import Init public meta import Init public import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit public import Mathlib public import Formalism.GaloisIrreducibility.NoSolvableTransitive public import Formalism.ResultantValuation.ResultantAdjugateProofs.Adjugate public import Formalism.ResultantValuation.ResultantAdjugateProofs.Mobius public import Formalism.ResultantValuation.ResultantAdjugateProofs.Window public import Formalism.ResultantValuation.ResultantAdjugateProofs.Koszul public import Formalism.ResultantValuation.ResultantAdjugateProofs.Parabolic public import Formalism.ResultantValuation.BoundedCubic public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace public import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt
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
lean_object* initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_NoSolvableTransitive(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Window(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_BoundedCubic(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_PrimePairDyadicDisjointAlt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_NoSolvableTransitive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Window(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_BoundedCubic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_PrimePairDyadicDisjointAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
