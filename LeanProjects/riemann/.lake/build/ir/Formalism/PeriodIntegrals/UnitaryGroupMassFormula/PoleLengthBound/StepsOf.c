// Lean compiler output
// Module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.StepsOf
// Imports: public import Init public meta import Init public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AALeAAp public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Assemble public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LiftMul public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFrom public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Closed public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Taylor public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiLenHolds public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
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
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_AALeAAp(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_Assemble(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_LiftMul(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_PiBallFrom(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_Closed(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_Taylor(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_PiLenHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FiltLenF(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SumAntidiagonalTuple(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_StepsOf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_AALeAAp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_Assemble(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_LiftMul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_PiBallFrom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_Closed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_Taylor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoleLengthBound_PiLenHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FiltLenF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SumAntidiagonalTuple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
