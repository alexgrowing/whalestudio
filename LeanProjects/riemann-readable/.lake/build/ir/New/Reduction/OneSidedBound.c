// Lean compiler output
// Module: New.Reduction.OneSidedBound
// Imports: public import Init public meta import Init public import New.Reduction.Data.Existence public import New.Reduction.MainInequality public import New.Reduction.Zeros.Criterion public import New.Reduction.Zeros.PrimeNumberTheorem public import Statements
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
lean_object* initialize_GRH_New_Reduction_Data_Existence(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_MainInequality(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Zeros_Criterion(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Zeros_PrimeNumberTheorem(uint8_t builtin);
lean_object* initialize_GRH_Statements(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Reduction_OneSidedBound(uint8_t builtin) {
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
res = initialize_GRH_New_Reduction_Data_Existence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_MainInequality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Zeros_Criterion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Zeros_PrimeNumberTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Statements(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
