// Lean compiler output
// Module: Lib.GaloisRep.BaseChange.GlobalRoot
// Imports: public import Init public meta import Init public import Lib.ClassField.Global.CMSplittingCharacters public import Lib.ClassField.Global.ExistenceTheorem public import Lib.GaloisRep.BaseChange.CommutingHeckeFamilies public import Lib.General.NumberTheory.CMFields
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
lean_object* initialize_GRH_Lib_ClassField_Global_CMSplittingCharacters(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Global_ExistenceTheorem(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_BaseChange_CommutingHeckeFamilies(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_CMFields(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_BaseChange_GlobalRoot(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Global_CMSplittingCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Global_ExistenceTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_BaseChange_CommutingHeckeFamilies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_CMFields(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
