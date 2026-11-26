// Lean compiler output
// Module: New.Spanning.RemainingTerms.Size
// Imports: public import Init public meta import Init public import New.Spanning.Bessel.OpenCellPairing public import New.Spanning.RemainingTerms.SchurOrbit public import New.Spanning.Unfolding.TermStructure
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
lean_object* initialize_GRH_New_Spanning_Bessel_OpenCellPairing(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_SchurOrbit(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_TermStructure(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_Size(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_Bessel_OpenCellPairing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_RemainingTerms_SchurOrbit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_TermStructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
