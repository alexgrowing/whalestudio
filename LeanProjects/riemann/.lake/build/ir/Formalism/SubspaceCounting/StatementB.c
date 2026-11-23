// Lean compiler output
// Module: Formalism.SubspaceCounting.StatementB
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Multiset_bell_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_window___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_window___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_window(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binLower___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binLower___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binLower(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_tailSum___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_tailSum___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_tailSum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_gaussBinom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_gaussBinom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_window___lam__0(lean_object* v_i_1_, lean_object* v_n_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_nat_add(v_i_1_, v_j_3_);
v___x_5_ = lean_nat_mod(v___x_4_, v_n_2_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_window___lam__0___boxed(lean_object* v_i_6_, lean_object* v_n_7_, lean_object* v_j_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_G0_window___lam__0(v_i_6_, v_n_7_, v_j_8_);
lean_dec(v_j_8_);
lean_dec(v_n_7_);
lean_dec(v_i_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(lean_object* v_f_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lp_mathlib_Multiset_map___redArg(v_f_10_, v_s_11_);
v___x_13_ = lp_mathlib_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Multiset_bell_spec__2_spec__4_spec__6_spec__8___redArg(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_window(lean_object* v_n_14_, lean_object* v_i_15_, lean_object* v_L_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_G0_window___lam__0___boxed), 3, 2);
lean_closure_set(v___f_17_, 0, v_i_15_);
lean_closure_set(v___f_17_, 1, v_n_14_);
v___x_18_ = l_List_range(v_L_16_);
v___x_19_ = lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(v___f_17_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0(lean_object* v_00_u03b1_20_, lean_object* v_f_21_, lean_object* v_s_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(v_f_21_, v_s_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binLower___lam__0(lean_object* v_n_24_, lean_object* v_00_u03b4_25_, lean_object* v_j_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___f_36_; 
v___x_27_ = lp_mathlib_Nat_fast__choose(v_n_24_, v_j_26_);
v___x_28_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_27_);
lean_inc(v_00_u03b4_25_);
v___x_29_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v_j_26_, v_00_u03b4_25_);
v___f_30_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_30_, 0, v___x_28_);
lean_closure_set(v___f_30_, 1, v___x_29_);
v___x_31_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_32_, 0, v_00_u03b4_25_);
v___f_33_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_33_, 0, v___x_31_);
lean_closure_set(v___f_33_, 1, v___f_32_);
v___x_34_ = lean_nat_sub(v_n_24_, v_j_26_);
v___x_35_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_34_, v___f_33_);
lean_dec(v___x_34_);
v___f_36_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_36_, 0, v___f_30_);
lean_closure_set(v___f_36_, 1, v___x_35_);
return v___f_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binLower___lam__0___boxed(lean_object* v_n_37_, lean_object* v_00_u03b4_38_, lean_object* v_j_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_G0_binLower___lam__0(v_n_37_, v_00_u03b4_38_, v_j_39_);
lean_dec(v_j_39_);
lean_dec(v_n_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_binLower(lean_object* v_n_41_, lean_object* v_00_u03b4_42_, lean_object* v_N_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___f_44_ = lean_alloc_closure((void*)(lp_tree_Formalism_G0_binLower___lam__0___boxed), 3, 2);
lean_closure_set(v___f_44_, 0, v_n_41_);
lean_closure_set(v___f_44_, 1, v_00_u03b4_42_);
v___x_45_ = l_List_range(v_N_43_);
v___x_46_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_45_, v___f_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_tailSum___lam__0(lean_object* v_u_47_, lean_object* v_x_48_, lean_object* v_l_49_){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = lean_nat_dec_le(v_u_47_, v_l_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec(v_l_49_);
lean_dec_ref(v_x_48_);
v___x_51_ = lean_unsigned_to_nat(0u);
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
v___x_52_ = lean_apply_1(v_x_48_, v_l_49_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_tailSum___lam__0___boxed(lean_object* v_u_53_, lean_object* v_x_54_, lean_object* v_l_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_Formalism_G0_tailSum___lam__0(v_u_53_, v_x_54_, v_l_55_);
lean_dec(v_u_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_tailSum(lean_object* v_N_57_, lean_object* v_x_58_, lean_object* v_u_59_){
_start:
{
lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___f_60_ = lean_alloc_closure((void*)(lp_tree_Formalism_G0_tailSum___lam__0___boxed), 3, 2);
lean_closure_set(v___f_60_, 0, v_u_59_);
lean_closure_set(v___f_60_, 1, v_x_58_);
v___x_61_ = l_List_finRange(v_N_57_);
v___x_62_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_61_, v___f_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_gaussBinom(lean_object* v_q_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_zero_66_; uint8_t v_isZero_67_; 
v_zero_66_ = lean_unsigned_to_nat(0u);
v_isZero_67_ = lean_nat_dec_eq(v_x_65_, v_zero_66_);
if (v_isZero_67_ == 1)
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(1u);
return v___x_68_;
}
else
{
uint8_t v_isZero_69_; 
v_isZero_69_ = lean_nat_dec_eq(v_x_64_, v_zero_66_);
if (v_isZero_69_ == 1)
{
return v_zero_66_;
}
else
{
lean_object* v_one_70_; lean_object* v_n_71_; lean_object* v_n_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_one_70_ = lean_unsigned_to_nat(1u);
v_n_71_ = lean_nat_sub(v_x_65_, v_one_70_);
v_n_72_ = lean_nat_sub(v_x_64_, v_one_70_);
v___x_73_ = lp_tree_Formalism_G0_gaussBinom(v_q_63_, v_n_72_, v_n_71_);
v___x_74_ = lean_nat_add(v_n_71_, v_one_70_);
lean_dec(v_n_71_);
v___x_75_ = lean_nat_pow(v_q_63_, v___x_74_);
v___x_76_ = lp_tree_Formalism_G0_gaussBinom(v_q_63_, v_n_72_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v_n_72_);
v___x_77_ = lean_nat_mul(v___x_75_, v___x_76_);
lean_dec(v___x_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_nat_add(v___x_73_, v___x_77_);
lean_dec(v___x_77_);
lean_dec(v___x_73_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_G0_gaussBinom___boxed(lean_object* v_q_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_tree_Formalism_G0_gaussBinom(v_q_79_, v_x_80_, v_x_81_);
lean_dec(v_x_81_);
lean_dec(v_x_80_);
lean_dec(v_q_79_);
return v_res_82_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SubspaceCounting_StatementB(uint8_t builtin) {
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
