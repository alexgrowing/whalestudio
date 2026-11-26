// Lean compiler output
// Module: New.Congruences.FirstOrder.TiedTraces
// Imports: public import Init public meta import Init public import Lib.GaloisRep.LocalGlobal.IwahoriCompatibility public import Lib.GaloisRep.TaylorWiles public import Lib.LocalGL.SphericalChainLemma public import New.Congruences.FirstOrder.OnePrime
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
lean_object* initialize_GRH_Lib_GaloisRep_LocalGlobal_IwahoriCompatibility(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_TaylorWiles(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_SphericalChainLemma(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_FirstOrder_OnePrime(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_FirstOrder_TiedTraces(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_LocalGlobal_IwahoriCompatibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_TaylorWiles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_LocalGL_SphericalChainLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_FirstOrder_OnePrime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
