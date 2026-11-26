// Lean compiler output
// Module: Lib.Weil.Periods.ConstantTerm
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.BlockPeriods public import Lib.General.LinearAlgebra.BlockEmbeddings public import Lib.Weil.DualPair.MixedModel public import Lib.Weil.Periods.BesselIntegral public import Lib.Weil.Periods.Equivariant
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
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_BlockPeriods(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_MixedModel(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_BesselIntegral(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_Equivariant(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Periods_ConstantTerm(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_BlockPeriods(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_MixedModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Periods_BesselIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Periods_Equivariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
