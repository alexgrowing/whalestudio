// Lean compiler output
// Module: Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.CMTypeGalois.StatementGroup
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___redArg___lam__0(lean_object* v_toMul_1_, lean_object* v_c_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_toMul_1_, v_c_2_, v_x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___redArg(lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_c_7_, lean_object* v_H_8_, lean_object* v_S_9_){
_start:
{
lean_object* v_toMonoid_10_; lean_object* v___x_11_; lean_object* v_toMul_12_; lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_toMonoid_10_ = lean_ctor_get(v_inst_5_, 0);
v___x_11_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_10_);
v_toMul_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_toMul_12_);
lean_dec_ref(v___x_11_);
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_Q3_TypesB_ext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v_toMul_12_);
lean_closure_set(v___f_13_, 1, v_c_7_);
lean_inc(v_S_9_);
lean_inc_ref_n(v_inst_6_, 2);
v___x_14_ = lp_mathlib_Multiset_sub___redArg(v_inst_6_, v_H_8_, v_S_9_);
v___x_15_ = lp_mathlib_Finset_image___redArg(v_inst_6_, v___f_13_, v___x_14_);
v___x_16_ = lp_mathlib_Multiset_ndunion___redArg(v_inst_6_, v_S_9_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___redArg___boxed(lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_c_19_, lean_object* v_H_20_, lean_object* v_S_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_Q3_TypesB_ext___redArg(v_inst_17_, v_inst_18_, v_c_19_, v_H_20_, v_S_21_);
lean_dec_ref(v_inst_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext(lean_object* v_G_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_c_26_, lean_object* v_H_27_, lean_object* v_S_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Formalism_Q3_TypesB_ext___redArg(v_inst_24_, v_inst_25_, v_c_26_, v_H_27_, v_S_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_TypesB_ext___boxed(lean_object* v_G_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_c_33_, lean_object* v_H_34_, lean_object* v_S_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_Q3_TypesB_ext(v_G_30_, v_inst_31_, v_inst_32_, v_c_33_, v_H_34_, v_S_35_);
lean_dec_ref(v_inst_31_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_StatementGroup(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB(uint8_t builtin) {
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
res = initialize_tree_Formalism_CMTypeGalois_StatementGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
