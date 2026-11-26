// Lean compiler output
// Module: New.Determinant.Norms.AdjointThetaLift
// Imports: public import Init public meta import Init public import Lib.General.Groups.IndexOfProduct public import Lib.SiegelWeil.RallisInner.SharpData public import New.OneLift.HeckeValues.CharacterLift public import New.Spanning.Multiplicities.HeckeEigensystems
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
lean_object* initialize_GRH_Lib_General_Groups_IndexOfProduct(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_RallisInner_SharpData(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_HeckeValues_CharacterLift(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Multiplicities_HeckeEigensystems(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_Norms_AdjointThetaLift(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Groups_IndexOfProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_RallisInner_SharpData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_HeckeValues_CharacterLift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Multiplicities_HeckeEigensystems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
