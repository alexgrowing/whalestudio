// Lean compiler output
// Module: Lib.SiegelWeil.Tower.FiniteTateIntegral
// Imports: public import Init public meta import Init public import Lib.ClassField.Avatar.HeckeBaseChange public import Lib.ClassField.HeckeCharacter.TameModulus public import Lib.SiegelWeil.Tower.RealConeIntegral
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
lean_object* initialize_GRH_Lib_ClassField_Avatar_HeckeBaseChange(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_TameModulus(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_RealConeIntegral(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_SiegelWeil_Tower_FiniteTateIntegral(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Avatar_HeckeBaseChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_HeckeCharacter_TameModulus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_Tower_RealConeIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
