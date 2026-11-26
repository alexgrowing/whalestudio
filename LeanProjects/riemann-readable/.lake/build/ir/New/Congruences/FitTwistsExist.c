// Lean compiler output
// Module: New.Congruences.FitTwistsExist
// Imports: public import Init public meta import Init public import New.Congruences.FirstOrder.DenominatorBound public import New.Congruences.GaloisRepresentations.RowsFromEigensystems public import New.Congruences.Selmer.TwistingTheorem public import New.Determinant.Chain.NormOfChain public import New.OneLift.HeckeValues.CentralAction
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
lean_object* initialize_GRH_New_Congruences_FirstOrder_DenominatorBound(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_GaloisRepresentations_RowsFromEigensystems(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_TwistingTheorem(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Chain_NormOfChain(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_HeckeValues_CentralAction(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_FitTwistsExist(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_FirstOrder_DenominatorBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_GaloisRepresentations_RowsFromEigensystems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_TwistingTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Chain_NormOfChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_HeckeValues_CentralAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
