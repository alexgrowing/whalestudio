// Lean compiler output
// Module: Formalism.MirabolicMackeyTheory.MirabolicIsMackey
// Imports: public import Init public meta import Init public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ErrSum public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxFull public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnExport public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnLocal public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OrthogonalityOfMackey public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms
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
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxFull(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxPsiGood(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnExport(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicIsMackey(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxFull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxPsiGood(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnExport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
