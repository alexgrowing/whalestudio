// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.LocWLemmas
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem public import Formalism.SizeWindowBrackets.SBrDiv public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.DataForms public import Formalism.LocalRingCardinality.SpanPowerMembership.Places public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic public import Formalism.GL3MeanSquares.HookFormulaTorsion.InvariantKernelTraceVanishes public import Formalism.LocalRingCardinality.DataIdx public import Formalism.LocalRingCardinality.Lemmas public import Formalism.SizeWindowBrackets.JointCSlopeExists public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_SBrDiv(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Places(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataIdx(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Lemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_JointCSlopeExists(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_LocWLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_SBrDiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Places(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_JointCSlopeExists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
