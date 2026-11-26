// Lean compiler output
// Module: New.Congruences.GaloisRepresentations.SelmerHypotheses
// Imports: public import Init public meta import Init public import Lib.GaloisRep.LocalGlobal.LabelCompatibility public import Lib.GaloisRep.Main.DivisibleSelmerModules public import New.Congruences.LocalLoss.Basic public import New.OneLift.TestedForms public import New.UpperBound.Objects.Rows
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
lean_object* initialize_GRH_Lib_GaloisRep_LocalGlobal_LabelCompatibility(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Main_DivisibleSelmerModules(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_LocalLoss_Basic(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_TestedForms(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_GaloisRepresentations_SelmerHypotheses(uint8_t builtin) {
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
res = initialize_GRH_Lib_GaloisRep_LocalGlobal_LabelCompatibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_Main_DivisibleSelmerModules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_LocalLoss_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_TestedForms(builtin);
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
