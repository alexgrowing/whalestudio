// Lean compiler output
// Module: Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs public import Formalism.LocalRingCardinality.DataNChoice public import Formalism.LocalRingCardinality.DataIdx public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedGal public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
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
lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TwDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataNChoice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataIdx(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedGal(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_LeastSplitAuxiliaryPrimeThetaChainSpec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_WittCoreInclusionMulVecMemLatticeCompletionAtPla(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TwDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataNChoice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GaloisLevelStructure_TiedGal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_LeastSplitAuxiliaryPrimeThetaChainSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
