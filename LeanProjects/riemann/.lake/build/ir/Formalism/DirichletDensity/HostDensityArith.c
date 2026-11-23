// Lean compiler output
// Module: Formalism.DirichletDensity.HostDensityArith
// Imports: public import Init public meta import Init public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr public import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr public import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity public import Formalism.DirichletDensity.DirichletDensityProofs.LogToDir public import Formalism.DirichletDensity.DirichletDensityProofs.HostDensityArith public import Formalism.DirichletDensity.DirichletDensityProofs.HostDensity
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
lean_object* initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr(uint8_t builtin);
lean_object* initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr(uint8_t builtin);
lean_object* initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity(uint8_t builtin);
lean_object* initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir(uint8_t builtin);
lean_object* initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith(uint8_t builtin);
lean_object* initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_DirichletDensity_HostDensityArith(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
