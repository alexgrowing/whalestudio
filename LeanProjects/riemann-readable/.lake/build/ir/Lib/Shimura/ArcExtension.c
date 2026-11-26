// Lean compiler output
// Module: Lib.Shimura.ArcExtension
// Imports: public import Init public meta import Init public import Lib.General.Geometry.GeometricPoints public import Lib.Shimura.ThetaGroup public import Lib.Shimura.ThetaNormality.NormalGeneration public import Lib.Shimura.Uniformisation.HolomorphicFamilies
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
lean_object* initialize_GRH_Lib_General_Geometry_GeometricPoints(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaGroup(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaNormality_NormalGeneration(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ArcExtension(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Geometry_GeometricPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaNormality_NormalGeneration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
