// Lean compiler output
// Module: New.UpperBound.Size.ArchimedeanSize
// Imports: public import Init public meta import Init public import New.Reduction.PrimeSums public import New.Spanning.Unfolding.FillingAdmissible public import New.UpperBound.Divisibility.ChainDatumExpansion public import New.UpperBound.Objects.RowChain public import New.UpperBound.Size.Estimates
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
lean_object* initialize_GRH_New_Reduction_PrimeSums(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_FillingAdmissible(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Divisibility_ChainDatumExpansion(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_RowChain(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Size_Estimates(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Size_ArchimedeanSize(uint8_t builtin) {
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
res = initialize_GRH_New_Reduction_PrimeSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_FillingAdmissible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Divisibility_ChainDatumExpansion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_RowChain(builtin);
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
