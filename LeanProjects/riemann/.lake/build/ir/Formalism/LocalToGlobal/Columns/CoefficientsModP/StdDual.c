// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.CoefModB public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaRoundFreeHolds public import Formalism.GradedWeylDivisibility.StatementE
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefModB(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaIndependenceHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaRoundFreeHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementE(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_StdDual(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefModB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaIndependenceHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaRoundFreeHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
