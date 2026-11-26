// Lean compiler output
// Module: Lib.LocalGL.Iwahori.QuadraticRelation
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.ComponentsAndBlockSums public import Lib.General.LinearAlgebra.Eigenvalues public import Lib.LocalGL.Iwahori.ParahoricStructure public import Lib.Shimura.Uniformisation.HolomorphicFamilies
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
lean_object* initialize_GRH_Lib_Adelic_Unitary_ComponentsAndBlockSums(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(uint8_t builtin);
lean_object* initialize_GRH_Lib_LocalGL_Iwahori_ParahoricStructure(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_LocalGL_Iwahori_QuadraticRelation(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_ComponentsAndBlockSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_LocalGL_Iwahori_ParahoricStructure(builtin);
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
