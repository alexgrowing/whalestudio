// Lean compiler output
// Module: Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
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
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
