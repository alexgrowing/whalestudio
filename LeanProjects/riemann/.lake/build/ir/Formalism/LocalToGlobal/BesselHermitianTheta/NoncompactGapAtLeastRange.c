// Lean compiler output
// Module: Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
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
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Theta_sparBound___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Theta_sparBound___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Theta_sparBound___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Theta_sparBound___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Theta_sparBound(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Theta_sparBound___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Theta_sparBound___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(8u);
v___x_4_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Theta_sparBound(lean_object* v_n_5_, lean_object* v_p_6_, lean_object* v_q_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___f_12_; lean_object* v___y_14_; uint8_t v___x_18_; 
v___x_8_ = lean_obj_once(&lp_tree_Formalism_L2_Theta_sparBound___closed__0, &lp_tree_Formalism_L2_Theta_sparBound___closed__0_once, _init_lp_tree_Formalism_L2_Theta_sparBound___closed__0);
v___x_9_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_n_5_);
lean_inc_ref(v___x_9_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_8_);
lean_closure_set(v___f_10_, 1, v___x_9_);
v___x_11_ = lean_obj_once(&lp_tree_Formalism_L2_Theta_sparBound___closed__1, &lp_tree_Formalism_L2_Theta_sparBound___closed__1_once, _init_lp_tree_Formalism_L2_Theta_sparBound___closed__1);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___x_11_);
lean_closure_set(v___f_12_, 1, v___x_9_);
v___x_18_ = lean_nat_dec_le(v_p_6_, v_q_7_);
if (v___x_18_ == 0)
{
lean_dec(v_p_6_);
v___y_14_ = v_q_7_;
goto v___jp_13_;
}
else
{
lean_dec(v_q_7_);
v___y_14_ = v_p_6_;
goto v___jp_13_;
}
v___jp_13_:
{
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___f_17_; 
v___x_15_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___y_14_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_16_, 0, v___f_12_);
lean_closure_set(v___f_16_, 1, v___x_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_17_, 0, v___f_10_);
lean_closure_set(v___f_17_, 1, v___f_16_);
return v___f_17_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_SchurIrreducible(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_NoncompactGapAtLeastRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_SchurIrreducible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
