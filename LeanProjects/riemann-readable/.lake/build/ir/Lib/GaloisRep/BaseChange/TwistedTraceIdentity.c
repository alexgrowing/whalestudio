// Lean compiler output
// Module: Lib.GaloisRep.BaseChange.TwistedTraceIdentity
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.HeckeEigenforms public import Lib.Adelic.Landherr public import Lib.GaloisRep.BaseChange.GlobalRoot public import Lib.Shimura.TraceFormula.DefiniteTrace
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
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_HeckeEigenforms(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Landherr(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_BaseChange_GlobalRoot(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_TraceFormula_DefiniteTrace(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_BaseChange_TwistedTraceIdentity(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_HeckeEigenforms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Adelic_Landherr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GaloisRep_BaseChange_GlobalRoot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_TraceFormula_DefiniteTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
