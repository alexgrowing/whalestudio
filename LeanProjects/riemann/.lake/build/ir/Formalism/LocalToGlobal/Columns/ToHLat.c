// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.ToHLat
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq public import Formalism.LocalToGlobal.Columns.GSetLemmas public import Formalism.LocalToGlobal.Columns.ColForms public import Formalism.LocalToGlobal.Columns.ColFormsLemmas public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice public import Formalism.LocalToGlobal.Columns.RowForms public import Formalism.LocalToGlobal.Columns.RowFormsLemmas public import Formalism.LocalToGlobal.Divisibility.Frames public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec public import Formalism.LocalToGlobal.GlobalTheory.HLatOps
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
lean_object* lp_mathlib_SMulMemClass_subtype___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_GSD_subIncl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SMulMemClass_subtype___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_GSD_subIncl___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_GSD_subIncl___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_subIncl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_subIncl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_subIncl(lean_object* v_K_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_S_6_, lean_object* v_h_7_, lean_object* v_U_8_, lean_object* v_L_9_, lean_object* v_L_x27_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(lp_tree_Formalism_L2_Col_GSD_subIncl___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_subIncl___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_S_16_, lean_object* v_h_17_, lean_object* v_U_18_, lean_object* v_L_19_, lean_object* v_L_x27_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_Col_GSD_subIncl(v_K_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_S_16_, v_h_17_, v_U_18_, v_L_19_, v_L_x27_20_);
lean_dec_ref(v_S_16_);
lean_dec(v_inst_15_);
lean_dec_ref(v_inst_13_);
return v_res_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ScaledRamifiedLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Frames(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_HLatOps(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ToHLat(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ScaledRamifiedLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Frames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_HLatOps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
