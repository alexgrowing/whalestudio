// Lean compiler output
// Module: Formalism.CMTypeGalois.HalfTypesFromGeneral
// Imports: public import Init public meta import Init public import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois public import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer public import Formalism.CMTypeGalois.CMTypeFrobenius.MQFrob public import Formalism.CMTypeGalois.CMTypeFrobenius.KroneckerMeaning public import Formalism.CMTypeGalois.CMTypeFrobenius.TypesA public import Formalism.CMTypeGalois.CMTypeFrobenius.TypesB public import Mathlib public import Formalism.CMTypeGalois.CMTypeFrobenius.HostFrob public import Formalism.CMTypeGalois.CMTypeFrobenius.HostConj public import Formalism.CMTypeGalois.CMTypeFrobenius.HostInertia public import Formalism.CMTypeGalois.CMTypeFrobenius.HostMu public import Formalism.CMTypeGalois.CMTypeFrobenius.HostEmb
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
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostFrob(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostEmb(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CMTypeGalois_HalfTypesFromGeneral(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostFrob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_HostEmb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
