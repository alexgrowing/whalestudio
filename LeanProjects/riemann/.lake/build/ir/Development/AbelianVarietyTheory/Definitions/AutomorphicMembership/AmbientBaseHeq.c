// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
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
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CmQuadraticFormEqAlternatingForm(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_EtaJUntw(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_PointPropertyEqSizeFree(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_FamilyClassSevenDutiesAndStableLattices(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AdmissibleIndexBoundAllPowers(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_MinfDensity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_AmbientBaseHeq(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CmQuadraticFormEqAlternatingForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_EtaJUntw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_PointPropertyEqSizeFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_FamilyClassSevenDutiesAndStableLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AdmissibleIndexBoundAllPowers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_MinfDensity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
