// Lean compiler output
// Module: New.Determinant.AuxiliaryForms.DeepLevelVanishing
// Imports: public import Init public meta import Init public import Lib.Adelic.TraceFormula.OrbitalUnfolding public import New.Appendix.DiscreteSeries.PositionGroup public import New.Determinant.AuxiliaryForms.DeepLevelPoincarePeriod public import New.Determinant.AuxiliaryForms.PathData public import New.UpperBound.Objects.RowChain
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
lean_object* initialize_GRH_Lib_Adelic_TraceFormula_OrbitalUnfolding(uint8_t builtin);
lean_object* initialize_GRH_New_Appendix_DiscreteSeries_PositionGroup(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_DeepLevelPoincarePeriod(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_PathData(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_RowChain(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_DeepLevelVanishing(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_TraceFormula_OrbitalUnfolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Appendix_DiscreteSeries_PositionGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_AuxiliaryForms_DeepLevelPoincarePeriod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_AuxiliaryForms_PathData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_RowChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
