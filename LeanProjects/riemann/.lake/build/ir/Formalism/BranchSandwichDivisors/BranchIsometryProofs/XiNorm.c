// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.BranchSandwichDivisors.StatementW public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_tree_Formalism_REAL_fockF___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnC___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00Formalism_BranchingDeterminantCap_xnSg_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnSg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnN___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnLam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnLam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnC___lam__0(lean_object* v_M_1_, lean_object* v_m_2_, lean_object* v_q_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; lean_object* v___f_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; 
v___x_4_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_M_1_);
lean_inc(v_q_3_);
v___x_5_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_q_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_7_, 0, v___x_4_);
lean_closure_set(v___f_7_, 1, v___f_6_);
v___x_8_ = lean_apply_1(v_m_2_, v_q_3_);
v___x_9_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_8_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___f_7_);
lean_closure_set(v___f_10_, 1, v___x_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0(lean_object* v_s_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_13_ = ((lean_object*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0___closed__0));
v___x_14_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_15_ = l_List_foldrTR___redArg(v___f_13_, v___x_14_, v_s_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0___redArg(lean_object* v_s_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lp_mathlib_Multiset_map___redArg(v_f_17_, v_s_16_);
v___x_19_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0_spec__0(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnC(lean_object* v_M_20_, lean_object* v_m_21_, lean_object* v_p_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_xnC___lam__0), 3, 2);
lean_closure_set(v___f_23_, 0, v_M_20_);
lean_closure_set(v___f_23_, 1, v_m_21_);
v___x_24_ = l_List_range(v_p_22_);
v___x_25_ = lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0___redArg(v___x_24_, v___f_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0(lean_object* v_00_u03b9_26_, lean_object* v_s_27_, lean_object* v_f_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_xnC_spec__0___redArg(v_s_27_, v_f_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_a_30_, lean_object* v_b_31_, lean_object* v_r_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = lean_nat_dec_eq(v_r_32_, v_a_30_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; 
v___x_34_ = lean_nat_dec_eq(v_r_32_, v_b_31_);
if (v___x_34_ == 0)
{
lean_inc(v_r_32_);
return v_r_32_;
}
else
{
lean_inc(v_a_30_);
return v_a_30_;
}
}
else
{
lean_inc(v_b_31_);
return v_b_31_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_a_35_, lean_object* v_b_36_, lean_object* v_r_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_a_35_, v_b_36_, v_r_37_);
lean_dec(v_r_37_);
lean_dec(v_b_36_);
lean_dec(v_a_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___lam__0(lean_object* v_a_39_, lean_object* v_b_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_a_39_, v_b_40_, v___y_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___lam__0___boxed(lean_object* v_a_43_, lean_object* v_b_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___lam__0(v_a_43_, v_b_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec(v_b_44_);
lean_dec(v_a_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3(lean_object* v_p_47_, lean_object* v_a_48_, lean_object* v_b_49_){
_start:
{
lean_object* v___f_50_; lean_object* v___x_51_; 
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_50_, 0, v_a_48_);
lean_closure_set(v___f_50_, 1, v_b_49_);
lean_inc_ref(v___f_50_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___f_50_);
lean_ctor_set(v___x_51_, 1, v___f_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_p_52_, lean_object* v_a_53_, lean_object* v_b_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3(v_p_52_, v_a_53_, v_b_54_);
lean_dec(v_p_52_);
return v_res_55_;
}
}
static lean_object* _init_lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__0, &lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__0_once, _init_lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__0);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(lean_object* v_p_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v_x_62_);
v___x_63_ = lean_obj_once(&lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__1, &lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__1_once, _init_lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___closed__1);
return v___x_63_;
}
else
{
lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v_toFun_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_head_64_ = lean_ctor_get(v_x_61_, 0);
lean_inc_n(v_head_64_, 2);
v_tail_65_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_tail_65_);
lean_dec_ref_known(v_x_61_, 2);
v_toFun_66_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_toFun_66_);
v___x_67_ = lean_apply_1(v_toFun_66_, v_head_64_);
v___x_68_ = lean_nat_dec_eq(v_head_64_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_val_72_; lean_object* v_inv_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_82_; 
v___x_69_ = lp_tree_Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3(v_p_60_, v_head_64_, v___x_67_);
v___x_70_ = lp_mathlib_Equiv_trans___redArg(v_x_62_, v___x_69_);
v___x_71_ = lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(v_p_60_, v_tail_65_, v___x_70_);
v_val_72_ = lean_ctor_get(v___x_71_, 0);
v_inv_73_ = lean_ctor_get(v___x_71_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_82_ == 0)
{
v___x_75_ = v___x_71_;
v_isShared_76_ = v_isSharedCheck_82_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_inv_73_);
lean_inc(v_val_72_);
lean_dec(v___x_71_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_82_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_int_neg(v_val_72_);
lean_dec(v_val_72_);
v___x_78_ = lean_int_neg(v_inv_73_);
lean_dec(v_inv_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_78_);
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
else
{
lean_dec(v___x_67_);
lean_dec(v_head_64_);
v_x_61_ = v_tail_65_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1___boxed(lean_object* v_p_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(v_p_84_, v_x_85_, v_x_86_);
lean_dec(v_p_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0___lam__0(lean_object* v_p_88_, lean_object* v_f_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_inc(v_p_88_);
v___x_90_ = l_List_finRange(v_p_88_);
v___x_91_ = lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(v_p_88_, v___x_90_, v_f_89_);
lean_dec(v_p_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0(lean_object* v_p_92_){
_start:
{
lean_object* v___f_93_; 
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_93_, 0, v_p_92_);
return v___f_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00Formalism_BranchingDeterminantCap_xnSg_spec__1(lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v_a_94_);
v___x_96_ = lp_mathlib_Complex_ofReal(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnSg(lean_object* v_p_97_, lean_object* v_00_u03c0_98_){
_start:
{
lean_object* v___x_99_; lean_object* v_val_100_; lean_object* v___x_101_; 
v___x_99_ = lp_tree_Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0___lam__0(v_p_97_, v_00_u03c0_98_);
v_val_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_val_100_);
lean_dec_ref(v___x_99_);
v___x_101_ = lp_tree_Int_cast___at___00Formalism_BranchingDeterminantCap_xnSg_spec__1(v_val_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___redArg(lean_object* v_p_102_, lean_object* v_f_103_, lean_object* v_s_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(v_p_102_, v_s_104_, v_f_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___redArg___boxed(lean_object* v_p_106_, lean_object* v_f_107_, lean_object* v_s_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___redArg(v_p_106_, v_f_107_, v_s_108_);
lean_dec(v_p_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0(lean_object* v_p_110_, lean_object* v_inst_111_, lean_object* v_f_112_, lean_object* v_s_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_tree_Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1(v_p_110_, v_s_113_, v_f_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0___boxed(lean_object* v_p_116_, lean_object* v_inst_117_, lean_object* v_f_118_, lean_object* v_s_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0(v_p_116_, v_inst_117_, v_f_118_, v_s_119_, v_a_120_);
lean_dec(v_p_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_p_122_, lean_object* v_a_123_, lean_object* v_b_124_, lean_object* v_r_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_a_123_, v_b_124_, v_r_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_p_127_, lean_object* v_a_128_, lean_object* v_b_129_, lean_object* v_r_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Equiv_swapCore___at___00Equiv_swap___at___00Equiv_Perm_signAux2___at___00Equiv_Perm_signAux3___at___00Equiv_Perm_sign___at___00Formalism_BranchingDeterminantCap_xnSg_spec__0_spec__0_spec__1_spec__3_spec__4(v_p_127_, v_a_128_, v_b_129_, v_r_130_);
lean_dec(v_r_130_);
lean_dec(v_b_129_);
lean_dec(v_a_128_);
lean_dec(v_p_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnN___redArg(lean_object* v_f_132_){
_start:
{
lean_object* v___x_133_; lean_object* v_re_134_; 
lean_inc_ref(v_f_132_);
v___x_133_ = lp_tree_Formalism_REAL_fockF___redArg(v_f_132_, v_f_132_);
v_re_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_re_134_);
lean_dec_ref(v___x_133_);
return v_re_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnN(lean_object* v_00_u03c3_135_, lean_object* v_f_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lp_tree_Formalism_BranchingDeterminantCap_xnN___redArg(v_f_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnAdd(lean_object* v_00_u03bc_138_, lean_object* v_p_139_, lean_object* v_j_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
lean_inc(v_j_140_);
v___x_141_ = lean_apply_1(v_00_u03bc_138_, v_j_140_);
v___x_142_ = lean_nat_dec_lt(v_j_140_, v_p_139_);
lean_dec(v_j_140_);
if (v___x_142_ == 0)
{
return v___x_141_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v___x_141_, v___x_143_);
lean_dec(v___x_141_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnAdd___boxed(lean_object* v_00_u03bc_145_, lean_object* v_p_146_, lean_object* v_j_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_tree_Formalism_BranchingDeterminantCap_xnAdd(v_00_u03bc_145_, v_p_146_, v_j_147_);
lean_dec(v_p_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnLam(lean_object* v_n_149_, lean_object* v_lam_150_, lean_object* v_q_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_lt(v_q_151_, v_n_149_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_dec(v_q_151_);
lean_dec_ref(v_lam_150_);
v___x_153_ = lean_unsigned_to_nat(0u);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_apply_1(v_lam_150_, v_q_151_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_xnLam___boxed(lean_object* v_n_155_, lean_object* v_lam_156_, lean_object* v_q_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lp_tree_Formalism_BranchingDeterminantCap_xnLam(v_n_155_, v_lam_156_, v_q_157_);
lean_dec(v_n_155_);
return v_res_158_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementW(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm(uint8_t builtin) {
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
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
