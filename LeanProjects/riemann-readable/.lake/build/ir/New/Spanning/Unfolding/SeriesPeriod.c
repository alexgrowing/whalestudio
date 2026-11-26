// Lean compiler output
// Module: New.Spanning.Unfolding.SeriesPeriod
// Imports: public import Init public meta import Init public import Lib.Adelic.QuotientMeasure.MovingTheQuotient public import Lib.Weil.Periods.RealAndFinitePoints public import New.Spanning.Unfolding.BesselFormula public import New.Spanning.Unfolding.FillingAdmissible public import New.UpperBound.Objects.PoincareMap
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
lean_object* initialize_GRH_Lib_Adelic_QuotientMeasure_MovingTheQuotient(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_RealAndFinitePoints(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_BesselFormula(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_FillingAdmissible(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_PoincareMap(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_SeriesPeriod(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_QuotientMeasure_MovingTheQuotient(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Periods_RealAndFinitePoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_BesselFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_FillingAdmissible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_PoincareMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
