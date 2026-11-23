// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero public import Formalism.RealPlaceAnalysis.StatementD public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId
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
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementD(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
