// Lean compiler output
// Module: New.Spanning.Bessel.FillingData
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Character.FormalDegree public import New.Determinant.AuxiliaryForms.DeepLevelPoincarePeriod public import New.Spanning.Bessel.CutTailBound public import New.Spanning.Bessel.SchurBound public import New.Spanning.Frames.RealBandLimits public import New.Spanning.Unfolding.Climbing public import New.UpperBound.Objects.Rows
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
lean_object* initialize_GRH_Lib_DiscreteSeries_Character_FormalDegree(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_DeepLevelPoincarePeriod(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Bessel_CutTailBound(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Bessel_SchurBound(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Frames_RealBandLimits(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_Climbing(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Bessel_FillingData(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Character_FormalDegree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_AuxiliaryForms_DeepLevelPoincarePeriod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Bessel_CutTailBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Bessel_SchurBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Frames_RealBandLimits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_Climbing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Rows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
