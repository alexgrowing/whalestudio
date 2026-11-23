// Lean compiler output
// Module: Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.GenusCovolBound public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusScale public import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct public import Formalism.FockGram.FockGramProofs.CovolGram
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
lean_object* initialize_tree_Formalism_HermitianLattices_GenusCovolBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_CovolGram(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound(uint8_t builtin) {
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
res = initialize_tree_Formalism_HermitianLattices_GenusCovolBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_CovolGram(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
