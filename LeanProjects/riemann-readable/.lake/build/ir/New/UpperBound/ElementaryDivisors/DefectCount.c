// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.DefectCount
// Imports: public import Init public meta import Init public import Lib.General.Measure.IntegralOperators public import Lib.LocalGL.Green.CuspidalFunctions public import New.UpperBound.ElementaryDivisors.PieriCone public import New.UpperBound.ElementaryDivisors.RootLemma
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
lean_object* initialize_GRH_Lib_General_Measure_IntegralOperators(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Green_CuspidalFunctions(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_PieriCone(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_DefectCount(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Measure_IntegralOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_LocalGL_Green_CuspidalFunctions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_PieriCone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
