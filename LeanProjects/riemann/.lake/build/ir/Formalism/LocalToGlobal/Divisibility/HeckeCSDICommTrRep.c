// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundColumns public import Formalism.LocalToGlobal.Columns.HeckeInert public import Formalism.LocalToGlobal.Columns.HeckeInertLemmas public import Formalism.LocalToGlobal.Columns.HeckeInertTr
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_offSubI_lev___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_offSubI_lev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_offSubI_lev___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_offSubI_lev___redArg(lean_object* v_P_1_){
_start:
{
return v_P_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_offSubI_lev(lean_object* v_E_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_ST_6_, lean_object* v_SG_7_, lean_object* v_SG_x27_8_, lean_object* v_S0_9_, lean_object* v_P_10_){
_start:
{
return v_P_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_offSubI_lev___boxed(lean_object* v_E_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_ST_15_, lean_object* v_SG_16_, lean_object* v_SG_x27_17_, lean_object* v_S0_18_, lean_object* v_P_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_DIV_offSubI_lev(v_E_11_, v_inst_12_, v_inst_13_, v_inst_14_, v_ST_15_, v_SG_16_, v_SG_x27_17_, v_S0_18_, v_P_19_);
lean_dec(v_SG_x27_17_);
lean_dec(v_SG_16_);
lean_dec(v_ST_15_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_12_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_TrivialExtensionSideWellFormed(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DivisionHeightBoundColumns(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeInert(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeInertLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeInertTr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_HeckeCSDICommTrRep(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_TrivialExtensionSideWellFormed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_DivisionHeightBoundColumns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeInert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeInertLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeInertTr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
