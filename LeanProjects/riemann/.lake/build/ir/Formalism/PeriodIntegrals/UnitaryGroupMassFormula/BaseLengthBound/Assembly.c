// Lean compiler output
// Module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Assembly
// Imports: public import Init public meta import Init public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseOf public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseMemHK public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseSmul public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseVan public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Column public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.UInjOfColumn public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseOpSmul
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
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_LenBaseOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseMemHK(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FiltLenF(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SumAntidiagonalTuple(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_TaylorRep(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseSmul(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseVan(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_Column(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_UInjOfColumn(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseOpSmul(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_Assembly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_LenBaseOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseMemHK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FiltLenF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SumAntidiagonalTuple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_TaylorRep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseSmul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseVan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_Column(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_UInjOfColumn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_HasseOpSmul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
