// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Col
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep public import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ConstantGeTwentyEight(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_HeckeCSDICommTrRep(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_FaceOf3(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LinkDIVL2R3Col(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_ConstantGeTwentyEight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_HeckeCSDICommTrRep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_FaceOf3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
