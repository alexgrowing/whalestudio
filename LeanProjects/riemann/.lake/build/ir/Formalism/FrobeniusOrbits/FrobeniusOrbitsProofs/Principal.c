// Lean compiler output
// Module: Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.HostDiffSupport public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
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
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
