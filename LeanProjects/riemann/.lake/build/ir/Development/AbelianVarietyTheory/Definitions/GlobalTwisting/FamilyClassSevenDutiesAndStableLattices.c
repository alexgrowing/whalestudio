// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood public import Formalism.LocalRingCardinality.DataAmbForm public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
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
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataAmbForm(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_AuxiliaryPrimeMemAvoidedPrimes(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_FamilyClassSevenDutiesAndStableLattices(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataAmbForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_AuxiliaryPrimeMemAvoidedPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
