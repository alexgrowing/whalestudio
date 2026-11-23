// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QlenEqZeroOfLe
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference public import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepClosed public import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent public import Formalism.LogFactorialIndices.LogProductFormula
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
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_SUnitsEulerDifference(uint8_t builtin);
lean_object* initialize_tree_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed(uint8_t builtin);
lean_object* initialize_tree_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogFactorialIndices_LogProductFormula(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QlenEqZeroOfLe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_SUnitsEulerDifference(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogFactorialIndices_LogProductFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
