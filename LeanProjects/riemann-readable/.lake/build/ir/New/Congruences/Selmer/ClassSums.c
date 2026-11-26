// Lean compiler output
// Module: New.Congruences.Selmer.ClassSums
// Imports: public import Init public meta import Init public import New.Congruences.GaloisRepresentations.SelmerHypotheses public import New.Congruences.Selmer.AuxiliaryPrimes public import New.OneLift.ComparisonOperator.ThreeExchanges public import New.OneLift.HeckeValues.AlgebraicPartIntegrality public import New.OneLift.HeckeValues.PeriodAtOne public import New.OneLift.HeckeValues.TwistedRatio
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
lean_object* initialize_GRH_New_Congruences_GaloisRepresentations_SelmerHypotheses(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ThreeExchanges(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_HeckeValues_AlgebraicPartIntegrality(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_HeckeValues_PeriodAtOne(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_HeckeValues_TwistedRatio(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Selmer_ClassSums(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_GaloisRepresentations_SelmerHypotheses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Selmer_AuxiliaryPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_ThreeExchanges(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_HeckeValues_AlgebraicPartIntegrality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_HeckeValues_PeriodAtOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_HeckeValues_TwistedRatio(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
