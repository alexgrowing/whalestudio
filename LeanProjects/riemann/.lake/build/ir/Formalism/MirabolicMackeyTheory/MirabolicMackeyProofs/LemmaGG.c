// Lean compiler output
// Module: Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.MirabolicMackeyTheory.StatementL public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OrthogonalityOfMackey public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
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
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_StatementL(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG(uint8_t builtin) {
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
res = initialize_tree_Formalism_MirabolicMackeyTheory_StatementL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
