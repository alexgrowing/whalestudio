// Lean compiler output
// Module: Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.NonsquarefreeBounds.Newton public import Formalism.CyclotomicNorms.NonsquarefreeBounds.SubstitutionBound public import Formalism.CyclotomicNorms.NonsquarefreeBounds.SpanQuadraticOfImage public import Formalism.CyclotomicNorms.NonsquarefreeBounds.Central public import Formalism.CyclotomicNorms.NonsquarefreeBounds.Cycles public import Formalism.TameInertiaTowers.FinalGroup public import Formalism.CyclotomicNorms.NonsquarefreeBounds.Jordan public import Formalism.CyclotomicNorms.NonsquarefreeBounds.RestrictionOfBlocksAndJordan public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
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
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Cycles(uint8_t builtin);
lean_object* initialize_tree_Formalism_TameInertiaTowers_FinalGroup(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Jordan(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_IrreducibilityOfGoodTuple(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Cycles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TameInertiaTowers_FinalGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Jordan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
