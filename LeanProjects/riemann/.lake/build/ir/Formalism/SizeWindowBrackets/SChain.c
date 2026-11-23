// Lean compiler output
// Module: Formalism.SizeWindowBrackets.SChain
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith public import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis public import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
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
lean_object* initialize_tree_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_SChain(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
