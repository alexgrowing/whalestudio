// Lean compiler output
// Module: Lib.Cohomology.Etale.ProperFunctors
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.EllAdicCohomology public import Lib.Cohomology.Etale.RelativeChains public import Lib.General.Geometry.GeometricPoints public import Lib.General.Geometry.PointsOfProperSchemes
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
lean_object* initialize_GRH_Lib_Cohomology_Etale_EllAdicCohomology(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_RelativeChains(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Geometry_GeometricPoints(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Geometry_PointsOfProperSchemes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_Etale_ProperFunctors(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_EllAdicCohomology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_Etale_RelativeChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Geometry_GeometricPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Geometry_PointsOfProperSchemes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
