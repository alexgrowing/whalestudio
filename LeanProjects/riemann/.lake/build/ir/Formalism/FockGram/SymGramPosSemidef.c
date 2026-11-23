// Lean compiler output
// Module: Formalism.FockGram.SymGramPosSemidef
// Imports: public import Init public meta import Init public import Formalism.FockGram.FockGramProofs.FockHerm public import Formalism.FockGram.FockGramProofs.FockSesq public import Formalism.FockGram.FockGramProofs.FockPerm public import Formalism.FockGram.FockGramProofs.DetSymPow public import Formalism.FockGram.FockGramProofs.SubIndexNorm public import Mathlib public import Formalism.FockGram.FockGramProofs.CovolGram public import Formalism.FockGram.FockGramProofs.HermDualOf public import Formalism.FockGram.FockGramProofs.HermitianTensorMulHermitian public import Formalism.FockGram.StatementSymPos public import Mathlib.Analysis.Matrix.Order public import Mathlib.Analysis.Matrix.PosDef public import Mathlib.Analysis.InnerProductSpace.Positive
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
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_FockHerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_FockSesq(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_FockPerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_DetSymPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_SubIndexNorm(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_CovolGram(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_HermDualOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_StatementSymPos(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Matrix_Order(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Matrix_PosDef(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Positive(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FockGram_SymGramPosSemidef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_FockHerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_FockSesq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_FockPerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_DetSymPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_SubIndexNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_CovolGram(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_HermDualOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_StatementSymPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Matrix_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Matrix_PosDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Positive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
