// Lean compiler output
// Module: New.UpperBound.Divisibility.LocalDivisibility
// Imports: public import Init public meta import Init public import New.UpperBound.Divisibility.ColengthAtLevel public import New.UpperBound.Divisibility.MarkOperator public import New.UpperBound.Divisibility.ValuationAtLevel public import New.UpperBound.Divisibility.ValuationAtNonSplitPrimes public import New.UpperBound.Size.Estimates
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
lean_object* initialize_GRH_New_UpperBound_Divisibility_ColengthAtLevel(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Divisibility_MarkOperator(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Divisibility_ValuationAtLevel(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Divisibility_ValuationAtNonSplitPrimes(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Size_Estimates(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Divisibility_LocalDivisibility(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_Divisibility_ColengthAtLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Divisibility_MarkOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Divisibility_ValuationAtLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Divisibility_ValuationAtNonSplitPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Size_Estimates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
