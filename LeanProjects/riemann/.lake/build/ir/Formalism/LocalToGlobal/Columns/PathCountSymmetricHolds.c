// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.CardPathsEqSubmodulePairs public import Formalism.LocalToGlobal.Columns.MemOfSmulMemOfAddEqOne public import Formalism.LocalToGlobal.Columns.NeighbourConjOfTopNeighbour
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CardPathsEqSubmodulePairs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_MemOfSmulMemOfAddEqOne(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_NeighbourConjOfTopNeighbour(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_PathCountSymmetricHolds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CardPathsEqSubmodulePairs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_MemOfSmulMemOfAddEqOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_NeighbourConjOfTopNeighbour(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
