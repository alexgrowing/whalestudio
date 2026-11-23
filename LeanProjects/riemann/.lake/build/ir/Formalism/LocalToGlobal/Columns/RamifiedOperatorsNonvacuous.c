// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.RamifiedOperatorsNonvacuous
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.KernelArgumentHypothesisScalar public import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg public import Formalism.LocalToGlobal.Columns.AtTOwedV public import Formalism.LocalToGlobal.Columns.AtTOwedC public import Formalism.LocalToGlobal.Columns.LocWLemmas public import Formalism.LocalToGlobal.Columns.ToHLatLemmas public import Formalism.LocalToGlobal.Columns.Inputs public import Formalism.GL3MeanSquares.PrimeOrderRamificationResults public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_KernelArgumentHypothesisScalar(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_BtExistsSmulLeOfFg(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AtTOwedV(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AtTOwedC(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_LocWLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ToHLatLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_Inputs(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_PrimeOrderRamificationResults(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_CoeNeZeroOfNotMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RamifiedOperatorsNonvacuous(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_KernelArgumentHypothesisScalar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_BtExistsSmulLeOfFg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AtTOwedV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AtTOwedC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_LocWLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ToHLatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_Inputs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_PrimeOrderRamificationResults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_CoeNeZeroOfNotMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
