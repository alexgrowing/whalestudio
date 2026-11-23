// Lean compiler output
// Module: Formalism.WideWeightTheorem.Statement
// Imports: public import Init public meta import Init public import Formalism.JacobiWeightFamilies.Statement
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_WeightedSieveThreeParameter_gavg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_WeightedSieveThreeParameter_gavg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_WeightedSieveThreeParameter_gavg___lam__0(lean_object* v_w_1_, lean_object* v_y_2_, lean_object* v_f_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___f_8_; 
lean_inc(v_j_4_);
v___x_5_ = lean_apply_1(v_w_1_, v_j_4_);
v___x_6_ = lean_apply_1(v_y_2_, v_j_4_);
v___x_7_ = lean_apply_1(v_f_3_, v___x_6_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_8_, 0, v___x_5_);
lean_closure_set(v___f_8_, 1, v___x_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_WeightedSieveThreeParameter_gavg(lean_object* v_n_9_, lean_object* v_w_10_, lean_object* v_y_11_, lean_object* v_f_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_WeightedSieveThreeParameter_gavg___lam__0), 4, 3);
lean_closure_set(v___f_13_, 0, v_w_10_);
lean_closure_set(v___f_13_, 1, v_y_11_);
lean_closure_set(v___f_13_, 2, v_f_12_);
v___x_14_ = l_List_finRange(v_n_9_);
v___x_15_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_14_, v___f_13_);
return v___x_15_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_JacobiWeightFamilies_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_WideWeightTheorem_Statement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_JacobiWeightFamilies_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
