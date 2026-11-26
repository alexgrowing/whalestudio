// Lean compiler output
// Module: Lib.Shimura.Uniformisation.TorusModel
// Imports: public import Init public meta import Init public import Lib.Shimura.AbelianScheme.IsogenyFlatness public import Lib.Shimura.ArcExtension public import Lib.Shimura.ThetaModuli.ThetaFamilyRigidity public import Lib.Shimura.Uniformisation.AppellHumbert public import Lib.Shimura.Uniformisation.BallModel public import Lib.Shimura.Uniformisation.LieExponential
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
lean_object* initialize_GRH_Lib_Shimura_AbelianScheme_IsogenyFlatness(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ArcExtension(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_ThetaFamilyRigidity(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_AppellHumbert(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_BallModel(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_LieExponential(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_Uniformisation_TorusModel(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_AbelianScheme_IsogenyFlatness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ArcExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaModuli_ThetaFamilyRigidity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_AppellHumbert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_BallModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_LieExponential(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
