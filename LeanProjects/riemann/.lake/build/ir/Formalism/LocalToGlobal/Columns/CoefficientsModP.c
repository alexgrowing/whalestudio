// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.CoefficientsModP
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaRoundFreeHolds public import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord public import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual public import Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual public import Formalism.LocalToGlobal.Columns.CoefficientsModP.NabDual
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
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_PairingNondegenerateHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_LatticeBasisExistsHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaIndependenceHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_TauLatticeLatticeHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaRoundFreeHolds(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_BaseCh(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_PairBDual(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_StdDual(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NabDual(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_PairingNondegenerateHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_LatticeBasisExistsHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaIndependenceHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_TauLatticeLatticeHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NablaRoundFreeHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_BaseCh(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_PairBDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_StdDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_NabDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
