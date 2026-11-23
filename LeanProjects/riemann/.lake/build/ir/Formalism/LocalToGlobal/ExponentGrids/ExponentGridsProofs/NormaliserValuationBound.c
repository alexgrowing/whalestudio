// Lean compiler output
// Module: Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.ExponentGrids.SecondComplementColumnExponents public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds public import Formalism.TranslateCocycles.TranslateCocycleProofs.TranslateScale public import Formalism.TranslateCocycles.TranslateCocycleProofs.NetGLMapSurjective public import Formalism.TranslateCocycles.TranslateCocycleProofs.HcBlockSumBounds
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
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ExponentGrids_SecondComplementColumnExponents(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds(uint8_t builtin);
lean_object* initialize_tree_Formalism_TranslateCocycles_TranslateCocycleProofs_TranslateScale(uint8_t builtin);
lean_object* initialize_tree_Formalism_TranslateCocycles_TranslateCocycleProofs_NetGLMapSurjective(uint8_t builtin);
lean_object* initialize_tree_Formalism_TranslateCocycles_TranslateCocycleProofs_HcBlockSumBounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ExponentGrids_SecondComplementColumnExponents(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TranslateCocycles_TranslateCocycleProofs_TranslateScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TranslateCocycles_TranslateCocycleProofs_NetGLMapSurjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TranslateCocycles_TranslateCocycleProofs_HcBlockSumBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
