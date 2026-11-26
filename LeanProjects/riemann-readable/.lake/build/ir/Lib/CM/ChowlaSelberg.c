// Lean compiler output
// Module: Lib.CM.ChowlaSelberg
// Imports: public import Init public meta import Init public import Lib.Analytic.EntireLFunction public import Lib.CM.ConjugateCurve public import Lib.CM.Integrality.IsogenyIntegrality public import Lib.CM.KroneckerLimit public import Lib.ClassField.HeckeL.EulerProduct public import Lib.ClassField.Places.ValuationSubrings
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
lean_object* initialize_GRH_Lib_Analytic_EntireLFunction(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_ConjugateCurve(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_Integrality_IsogenyIntegrality(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_KroneckerLimit(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeL_EulerProduct(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_ValuationSubrings(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_CM_ChowlaSelberg(uint8_t builtin) {
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
res = initialize_GRH_Lib_Analytic_EntireLFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_CM_ConjugateCurve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_CM_Integrality_IsogenyIntegrality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_CM_KroneckerLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_HeckeL_EulerProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Places_ValuationSubrings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
