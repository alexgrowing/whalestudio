// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.ClassSumDualLe
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.Statement
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
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cutLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cutLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_valLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_valLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cutLat(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_n_3_, lean_object* v_d_4_, lean_object* v_E_5_, lean_object* v_A_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cutLat___boxed(lean_object* v_K_8_, lean_object* v_inst_9_, lean_object* v_n_10_, lean_object* v_d_11_, lean_object* v_E_12_, lean_object* v_A_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_DivisionValues_cutLat(v_K_8_, v_inst_9_, v_n_10_, v_d_11_, v_E_12_, v_A_13_);
lean_dec(v_E_12_);
lean_dec(v_d_11_);
lean_dec(v_n_10_);
lean_dec_ref(v_inst_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_valLat(lean_object* v_K_15_, lean_object* v_inst_16_, lean_object* v_n_17_, lean_object* v_Cl_18_, lean_object* v_V_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_I_24_, lean_object* v_N_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_valLat___boxed(lean_object* v_K_27_, lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_Cl_30_, lean_object* v_V_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_I_36_, lean_object* v_N_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_DivisionValues_valLat(v_K_27_, v_inst_28_, v_n_29_, v_Cl_30_, v_V_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_I_36_, v_N_37_);
lean_dec(v_I_36_);
lean_dec(v_inst_34_);
lean_dec(v_inst_33_);
lean_dec_ref(v_inst_32_);
lean_dec(v_n_29_);
lean_dec_ref(v_inst_28_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualLe(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
