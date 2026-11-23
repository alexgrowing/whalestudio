// Lean compiler output
// Module: Formalism.LagrangeIdealLifts.Statement
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_padicValInt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_padicValNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_h0c___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_h0c___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_h0c(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_h0c___lam__0(lean_object* v_00_u2113_1_, lean_object* v_m_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lp_mathlib_padicValInt(v_00_u2113_1_, v_a_3_);
v___x_5_ = lean_nat_add(v_m_2_, v___x_4_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_h0c___lam__0___boxed(lean_object* v_00_u2113_6_, lean_object* v_m_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_LIFT_h0c___lam__0(v_00_u2113_6_, v_m_7_, v_a_8_);
lean_dec(v_a_8_);
lean_dec(v_m_7_);
lean_dec(v_00_u2113_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_h0c(lean_object* v_00_u2113_10_, lean_object* v_m_11_, lean_object* v_U_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; 
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_LIFT_h0c___lam__0___boxed), 3, 2);
lean_closure_set(v___f_13_, 0, v_00_u2113_10_);
lean_closure_set(v___f_13_, 1, v_m_11_);
v___x_14_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v_U_12_, v___f_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU___lam__0(lean_object* v_00_u2113_15_, lean_object* v_s_16_, lean_object* v_j_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lp_mathlib_padicValInt(v_00_u2113_15_, v_j_17_);
v___x_19_ = lean_nat_add(v_s_16_, v___x_18_);
lean_dec(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU___lam__0___boxed(lean_object* v_00_u2113_20_, lean_object* v_s_21_, lean_object* v_j_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_LIFT_eU___lam__0(v_00_u2113_20_, v_s_21_, v_j_22_);
lean_dec(v_j_22_);
lean_dec(v_s_21_);
lean_dec(v_00_u2113_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU(lean_object* v_00_u2113_24_, lean_object* v_M_25_, lean_object* v_s_26_, lean_object* v_J_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc(v_s_26_);
lean_inc(v_00_u2113_24_);
v___f_28_ = lean_alloc_closure((void*)(lp_tree_Formalism_LIFT_eU___lam__0___boxed), 3, 2);
lean_closure_set(v___f_28_, 0, v_00_u2113_24_);
lean_closure_set(v___f_28_, 1, v_s_26_);
v___x_29_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v_J_27_, v___f_28_);
v___x_30_ = lean_nat_mul(v_M_25_, v_s_26_);
lean_dec(v_s_26_);
v___x_31_ = lean_nat_add(v___x_29_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_29_);
v___x_32_ = lp_mathlib_Nat_factorialBinarySplitting(v_M_25_);
v___x_33_ = lp_mathlib_padicValNat(v_00_u2113_24_, v___x_32_);
lean_dec(v_00_u2113_24_);
v___x_34_ = lean_nat_add(v___x_31_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v___x_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LIFT_eU___boxed(lean_object* v_00_u2113_35_, lean_object* v_M_36_, lean_object* v_s_37_, lean_object* v_J_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_LIFT_eU(v_00_u2113_35_, v_M_36_, v_s_37_, v_J_38_);
lean_dec(v_M_36_);
return v_res_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LagrangeIdealLifts_Statement(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
