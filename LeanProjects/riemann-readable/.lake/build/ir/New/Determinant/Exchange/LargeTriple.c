// Lean compiler output
// Module: New.Determinant.Exchange.LargeTriple
// Imports: public import Init public meta import Init public import Lib.SiegelWeil.Formula.StrongApproximation public import Lib.SiegelWeil.Tower.LargeSideConstantTerm public import New.Determinant.Exchange.EquivariantDifference public import New.Determinant.Exchange.NegativeIndices public import New.Determinant.Exchange.StableSpacesStandardData
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
lean_object* initialize_GRH_Lib_SiegelWeil_Formula_StrongApproximation(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_LargeSideConstantTerm(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Exchange_EquivariantDifference(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Exchange_NegativeIndices(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Exchange_StableSpacesStandardData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_Exchange_LargeTriple(uint8_t builtin) {
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
res = initialize_GRH_Lib_SiegelWeil_Formula_StrongApproximation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_Tower_LargeSideConstantTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Exchange_EquivariantDifference(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Exchange_NegativeIndices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Exchange_StableSpacesStandardData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
