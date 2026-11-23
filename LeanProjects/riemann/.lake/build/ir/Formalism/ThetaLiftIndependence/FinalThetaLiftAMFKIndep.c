// Lean compiler output
// Module: Formalism.ThetaLiftIndependence.FinalThetaLiftAMFKIndep
// Imports: public import Init public meta import Init public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.GaussOp public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.EigenSwap public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.FFPlancherel public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap
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
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_OrbitSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_EigenSwap(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_DetSwap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaLiftIndependence_FinalThetaLiftAMFKIndep(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_OrbitSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_EigenSwap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_DetSwap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
