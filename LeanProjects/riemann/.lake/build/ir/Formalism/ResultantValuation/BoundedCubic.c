// Lean compiler output
// Module: Formalism.ResultantValuation.BoundedCubic
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
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_thirdDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_thirdDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_thirdDiff___redArg(lean_object* v_inst_1_, lean_object* v_00_u03c6_2_, lean_object* v_x_3_, lean_object* v_y_4_, lean_object* v_z_5_){
_start:
{
lean_object* v_toAddMonoid_6_; lean_object* v_toAddSemigroup_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_toZero_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; 
v_toAddMonoid_6_ = lean_ctor_get(v_inst_1_, 0);
v_toAddSemigroup_7_ = lean_ctor_get(v_toAddMonoid_6_, 0);
lean_inc_n(v_toAddSemigroup_7_, 4);
lean_inc_n(v_y_4_, 2);
lean_inc_n(v_x_3_, 2);
v___x_8_ = lean_apply_2(v_toAddSemigroup_7_, v_x_3_, v_y_4_);
lean_inc_n(v_z_5_, 3);
lean_inc(v___x_8_);
v___x_9_ = lean_apply_2(v_toAddSemigroup_7_, v___x_8_, v_z_5_);
lean_inc_n(v_00_u03c6_2_, 7);
v___x_10_ = lean_apply_1(v_00_u03c6_2_, v___x_9_);
v___x_11_ = lean_apply_1(v_00_u03c6_2_, v___x_8_);
v___x_12_ = lean_apply_2(v_toAddSemigroup_7_, v_x_3_, v_z_5_);
v___x_13_ = lean_apply_1(v_00_u03c6_2_, v___x_12_);
v___x_14_ = lean_apply_2(v_toAddSemigroup_7_, v_y_4_, v_z_5_);
v___x_15_ = lean_apply_1(v_00_u03c6_2_, v___x_14_);
v___x_16_ = lean_apply_1(v_00_u03c6_2_, v_x_3_);
v___x_17_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_inst_1_);
lean_dec_ref(v_inst_1_);
v_toZero_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_toZero_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lean_apply_1(v_00_u03c6_2_, v_y_4_);
v___f_20_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_20_, 0, v___x_11_);
v___f_21_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_21_, 0, v___x_10_);
lean_closure_set(v___f_21_, 1, v___f_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_22_, 0, v___x_13_);
v___f_23_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_23_, 0, v___f_21_);
lean_closure_set(v___f_23_, 1, v___f_22_);
v___f_24_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_24_, 0, v___x_15_);
v___f_25_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_25_, 0, v___f_23_);
lean_closure_set(v___f_25_, 1, v___f_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_26_, 0, v___f_25_);
lean_closure_set(v___f_26_, 1, v___x_16_);
v___f_27_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_27_, 0, v___f_26_);
lean_closure_set(v___f_27_, 1, v___x_19_);
v___x_28_ = lean_apply_1(v_00_u03c6_2_, v_z_5_);
v___f_29_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_29_, 0, v___f_27_);
lean_closure_set(v___f_29_, 1, v___x_28_);
v___x_30_ = lean_apply_1(v_00_u03c6_2_, v_toZero_18_);
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_31_, 0, v___x_30_);
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_32_, 0, v___f_29_);
lean_closure_set(v___f_32_, 1, v___f_31_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_thirdDiff(lean_object* v_G_33_, lean_object* v_inst_34_, lean_object* v_00_u03c6_35_, lean_object* v_x_36_, lean_object* v_y_37_, lean_object* v_z_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree_Formalism_ResultantValuation_thirdDiff___redArg(v_inst_34_, v_00_u03c6_35_, v_x_36_, v_y_37_, v_z_38_);
return v___x_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ResultantValuation_BoundedCubic(uint8_t builtin) {
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
