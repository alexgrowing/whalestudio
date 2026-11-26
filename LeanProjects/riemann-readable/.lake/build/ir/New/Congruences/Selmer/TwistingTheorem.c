// Lean compiler output
// Module: New.Congruences.Selmer.TwistingTheorem
// Imports: public import Init public meta import Init public import Lib.General.NumberTheory.LargeResidueField public import New.Congruences.FirstOrder.EvenClasses public import New.Congruences.Selmer.GeneralTheorem public import New.Congruences.Selmer.LValueSystems public import New.Congruences.Selmer.MainSummands
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
lean_object* initialize_GRH_Lib_General_NumberTheory_LargeResidueField(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_FirstOrder_EvenClasses(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_GeneralTheorem(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_LValueSystems(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_MainSummands(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Selmer_TwistingTheorem(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_NumberTheory_LargeResidueField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_FirstOrder_EvenClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_GeneralTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_LValueSystems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_MainSummands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
