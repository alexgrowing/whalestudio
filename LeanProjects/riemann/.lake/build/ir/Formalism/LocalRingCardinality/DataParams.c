// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataParams
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataParams₂
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
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_jG;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_condE(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_condE___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_qSig(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_qSig___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_Mrt(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_Mrt___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_gapS(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_BasicNotions_LevelStarExponents_jG(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(5u);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_condE(lean_object* v_D_2_){
_start:
{
lean_object* v_host_3_; lean_object* v_toHostAx_4_; lean_object* v_q_5_; lean_object* v_d_6_; lean_object* v_QS_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_host_3_ = lean_ctor_get(v_D_2_, 1);
v_toHostAx_4_ = lean_ctor_get(v_host_3_, 0);
v_q_5_ = lean_ctor_get(v_toHostAx_4_, 0);
v_d_6_ = lean_ctor_get(v_toHostAx_4_, 1);
v_QS_7_ = lean_ctor_get(v_toHostAx_4_, 2);
v___x_8_ = lean_nat_mul(v_QS_7_, v_q_5_);
v___x_9_ = lean_nat_mul(v___x_8_, v_d_6_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_condE___boxed(lean_object* v_D_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_BasicNotions_LevelStarExponents_condE(v_D_10_);
lean_dec_ref(v_D_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_qSig(lean_object* v_D_12_){
_start:
{
lean_object* v_R_13_; lean_object* v_m_14_; 
v_R_13_ = lean_ctor_get(v_D_12_, 0);
v_m_14_ = lean_ctor_get(v_R_13_, 2);
lean_inc(v_m_14_);
return v_m_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_qSig___boxed(lean_object* v_D_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_BasicNotions_LevelStarExponents_qSig(v_D_15_);
lean_dec_ref(v_D_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_Mrt(lean_object* v_D_17_){
_start:
{
lean_object* v_R_18_; lean_object* v_m_19_; lean_object* v_t_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_R_18_ = lean_ctor_get(v_D_17_, 0);
v_m_19_ = lean_ctor_get(v_R_18_, 2);
v_t_20_ = lean_ctor_get(v_R_18_, 3);
v___x_21_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_18_);
v___x_22_ = lean_nat_mul(v_m_19_, v_t_20_);
v___x_23_ = lean_nat_add(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v___x_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_Mrt___boxed(lean_object* v_D_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_BasicNotions_LevelStarExponents_Mrt(v_D_24_);
lean_dec_ref(v_D_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_LevelStarExponents_gapS(lean_object* v_D_26_, lean_object* v_C_27_){
_start:
{
lean_object* v_R_28_; lean_object* v_k_29_; lean_object* v_m_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v___f_42_; 
v_R_28_ = lean_ctor_get(v_D_26_, 0);
lean_inc_ref(v_R_28_);
lean_dec_ref(v_D_26_);
v_k_29_ = lean_ctor_get(v_R_28_, 1);
v_m_30_ = lean_ctor_get(v_R_28_, 2);
lean_inc_n(v_m_30_, 2);
lean_inc(v_k_29_);
v___x_31_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_k_29_);
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_32_, 0, v_C_27_);
lean_closure_set(v___f_32_, 1, v___x_31_);
v___x_33_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_m_30_);
v___x_34_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v___x_33_);
v___x_35_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_34_, v___x_33_);
v___f_36_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_36_, 0, v___f_32_);
lean_closure_set(v___f_36_, 1, v___x_35_);
v___x_37_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_28_, v_m_30_);
lean_dec(v_m_30_);
lean_dec_ref(v_R_28_);
v___x_38_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_37_);
v___x_39_ = lean_unsigned_to_nat(10u);
v___x_40_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_39_, v___x_33_);
v___f_41_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_41_, 0, v___x_38_);
lean_closure_set(v___f_41_, 1, v___x_40_);
v___f_42_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_42_, 0, v___f_36_);
lean_closure_set(v___f_42_, 1, v___f_41_);
return v___f_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Formalism_BasicNotions_LevelStarExponents_jG = _init_lp_tree_Formalism_BasicNotions_LevelStarExponents_jG();
lean_mark_persistent(lp_tree_Formalism_BasicNotions_LevelStarExponents_jG);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
