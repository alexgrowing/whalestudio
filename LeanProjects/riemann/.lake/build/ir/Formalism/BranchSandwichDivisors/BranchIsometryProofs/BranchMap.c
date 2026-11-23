// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.GradedWeylDivisibility.FinalC public import Formalism.BranchSandwichDivisors.StatementW public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq
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
lean_object* lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Equiv_Perm_signAux2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Module_End_instRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Module_End_instMul___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_instFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Module_End_instMul___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_zW(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_zW___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_lastW(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_lastW___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_omg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_omg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmChi___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmChi___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmChi(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmRho___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmRho(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__0(lean_object* v___y_1_, lean_object* v_E_2_, lean_object* v_a_3_, lean_object* v_i_4_, lean_object* v_toSub_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc(v___y_6_);
v___x_7_ = lean_apply_1(v___y_1_, v___y_6_);
v___x_8_ = lean_apply_3(v_E_2_, v_a_3_, v_i_4_, v___y_6_);
v___x_9_ = lean_apply_2(v_toSub_5_, v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__1(lean_object* v_toZero_10_, lean_object* v_x_11_){
_start:
{
lean_inc(v_toZero_10_);
return v_toZero_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__1___boxed(lean_object* v_toZero_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__1(v_toZero_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec(v_toZero_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg(lean_object* v_inst_15_, lean_object* v_E_16_, lean_object* v_u_17_, lean_object* v_k_18_, lean_object* v_a_19_, lean_object* v_i_20_){
_start:
{
lean_object* v_toAddMonoid_21_; lean_object* v_toSub_22_; uint8_t v___x_23_; 
v_toAddMonoid_21_ = lean_ctor_get(v_inst_15_, 0);
v_toSub_22_ = lean_ctor_get(v_inst_15_, 2);
lean_inc(v_toSub_22_);
v___x_23_ = lean_nat_dec_eq(v_a_19_, v_i_20_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v_toZero_25_; lean_object* v___f_26_; lean_object* v___f_27_; 
lean_inc_ref(v_toAddMonoid_21_);
lean_dec(v_k_18_);
lean_dec_ref(v_inst_15_);
v___x_24_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_21_);
lean_dec_ref(v_toAddMonoid_21_);
v_toZero_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_toZero_25_);
lean_dec_ref(v___x_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_26_, 0, v_toZero_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__0), 6, 5);
lean_closure_set(v___f_27_, 0, v___f_26_);
lean_closure_set(v___f_27_, 1, v_E_16_);
lean_closure_set(v___f_27_, 2, v_a_19_);
lean_closure_set(v___f_27_, 3, v_i_20_);
lean_closure_set(v___f_27_, 4, v_toSub_22_);
return v___f_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_toIntCast_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___f_34_; 
v___x_28_ = lp_mathlib_Module_End_instRing___redArg(v_inst_15_);
v___x_29_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_28_);
v_toIntCast_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_toIntCast_30_);
lean_dec_ref(v___x_29_);
v___x_31_ = lean_nat_to_int(v_k_18_);
v___x_32_ = lean_int_add(v_u_17_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_apply_1(v_toIntCast_30_, v___x_32_);
v___f_34_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___lam__0), 6, 5);
lean_closure_set(v___f_34_, 0, v___x_33_);
lean_closure_set(v___f_34_, 1, v_E_16_);
lean_closure_set(v___f_34_, 2, v_a_19_);
lean_closure_set(v___f_34_, 3, v_i_20_);
lean_closure_set(v___f_34_, 4, v_toSub_22_);
return v___f_34_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg___boxed(lean_object* v_inst_35_, lean_object* v_E_36_, lean_object* v_u_37_, lean_object* v_k_38_, lean_object* v_a_39_, lean_object* v_i_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg(v_inst_35_, v_E_36_, v_u_37_, v_k_38_, v_a_39_, v_i_40_);
lean_dec(v_u_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF(lean_object* v_R_42_, lean_object* v_M_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_n_47_, lean_object* v_E_48_, lean_object* v_u_49_, lean_object* v_k_50_, lean_object* v_a_51_, lean_object* v_i_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg(v_inst_45_, v_E_48_, v_u_49_, v_k_50_, v_a_51_, v_i_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmF___boxed(lean_object* v_R_54_, lean_object* v_M_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_n_59_, lean_object* v_E_60_, lean_object* v_u_61_, lean_object* v_k_62_, lean_object* v_a_63_, lean_object* v_i_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_tree_Formalism_BranchingDeterminantCap_bmF(v_R_54_, v_M_55_, v_inst_56_, v_inst_57_, v_inst_58_, v_n_59_, v_E_60_, v_u_61_, v_k_62_, v_a_63_, v_i_64_);
lean_dec(v_u_61_);
lean_dec(v_n_59_);
lean_dec(v_inst_58_);
lean_dec_ref(v_inst_56_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___lam__0(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_E_69_, lean_object* v_u_70_, lean_object* v_k_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_28__overap_75_; lean_object* v___x_76_; 
lean_inc_n(v_k_71_, 2);
v___x_73_ = lean_apply_1(v_00_u03b1_66_, v_k_71_);
v___x_74_ = lean_apply_1(v_00_u03b2_67_, v_k_71_);
v___x_28__overap_75_ = lp_tree_Formalism_BranchingDeterminantCap_bmF___redArg(v_inst_68_, v_E_69_, v_u_70_, v_k_71_, v___x_73_, v___x_74_);
v___x_76_ = lean_apply_1(v___x_28__overap_75_, v___y_72_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___lam__0___boxed(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_inst_79_, lean_object* v_E_80_, lean_object* v_u_81_, lean_object* v_k_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___lam__0(v_00_u03b1_77_, v_00_u03b2_78_, v_inst_79_, v_E_80_, v_u_81_, v_k_82_, v___y_83_);
lean_dec(v_u_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg(lean_object* v_inst_87_, lean_object* v_n_88_, lean_object* v_E_89_, lean_object* v_u_90_, lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_93_, 0, v_00_u03b1_91_);
lean_closure_set(v___f_93_, 1, v_00_u03b2_92_);
lean_closure_set(v___f_93_, 2, v_inst_87_);
lean_closure_set(v___f_93_, 3, v_E_89_);
lean_closure_set(v___f_93_, 4, v_u_90_);
v___f_94_ = ((lean_object*)(lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__0));
v___f_95_ = ((lean_object*)(lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg___closed__1));
v___x_96_ = l_List_ofFn___redArg(v_n_88_, v___f_93_);
v___x_97_ = l_List_prod___redArg(v___f_94_, v___f_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM(lean_object* v_R_98_, lean_object* v_M_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_n_103_, lean_object* v_E_104_, lean_object* v_u_105_, lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg(v_inst_101_, v_n_103_, v_E_104_, v_u_105_, v_00_u03b1_106_, v_00_u03b2_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmM___boxed(lean_object* v_R_109_, lean_object* v_M_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_n_114_, lean_object* v_E_115_, lean_object* v_u_116_, lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_tree_Formalism_BranchingDeterminantCap_bmM(v_R_109_, v_M_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_n_114_, v_E_115_, v_u_116_, v_00_u03b1_117_, v_00_u03b2_118_);
lean_dec(v_inst_113_);
lean_dec_ref(v_inst_111_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg___lam__0(lean_object* v_00_u03b1_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_toFun_122_; lean_object* v___x_123_; 
v_toFun_122_ = lean_ctor_get(v_00_u03b1_120_, 0);
lean_inc(v_toFun_122_);
lean_dec_ref(v_00_u03b1_120_);
v___x_123_ = lean_apply_1(v_toFun_122_, v___y_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg___lam__1(lean_object* v___x_124_, lean_object* v___x_125_, lean_object* v_inst_126_, lean_object* v_n_127_, lean_object* v_E_128_, lean_object* v_u_129_, lean_object* v_00_u03b2_130_, lean_object* v_toZSMul_131_, lean_object* v_00_u03b1_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_134_; lean_object* v_val_135_; lean_object* v___f_136_; lean_object* v___x_309__overap_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
lean_inc_ref(v_00_u03b1_132_);
v___x_134_ = lp_mathlib_Equiv_Perm_signAux2___redArg(v___x_124_, v___x_125_, v_00_u03b1_132_);
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v___x_134_);
v___f_136_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg___lam__0), 2, 1);
lean_closure_set(v___f_136_, 0, v_00_u03b1_132_);
v___x_309__overap_137_ = lp_tree_Formalism_BranchingDeterminantCap_bmM___redArg(v_inst_126_, v_n_127_, v_E_128_, v_u_129_, v___f_136_, v_00_u03b2_130_);
v___x_138_ = lean_apply_1(v___x_309__overap_137_, v___y_133_);
v___x_139_ = lean_apply_2(v_toZSMul_131_, v_val_135_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg(lean_object* v_inst_140_, lean_object* v_n_141_, lean_object* v_E_142_, lean_object* v_u_143_, lean_object* v_00_u03b2_144_){
_start:
{
lean_object* v_toAddMonoid_145_; lean_object* v_toZSMul_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_toAddMonoid_145_ = lean_ctor_get(v_inst_140_, 0);
v_toZSMul_146_ = lean_ctor_get(v_inst_140_, 3);
lean_inc(v_toZSMul_146_);
lean_inc_ref(v_toAddMonoid_145_);
v___x_147_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_145_);
lean_inc_n(v_n_141_, 2);
v___x_148_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_148_, 0, v_n_141_);
v___x_149_ = l_List_finRange(v_n_141_);
lean_inc_n(v___x_149_, 2);
lean_inc_ref_n(v___x_148_, 2);
v___f_150_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg___lam__1), 10, 8);
lean_closure_set(v___f_150_, 0, v___x_148_);
lean_closure_set(v___f_150_, 1, v___x_149_);
lean_closure_set(v___f_150_, 2, v_inst_140_);
lean_closure_set(v___f_150_, 3, v_n_141_);
lean_closure_set(v___f_150_, 4, v_E_142_);
lean_closure_set(v___f_150_, 5, v_u_143_);
lean_closure_set(v___f_150_, 6, v_00_u03b2_144_);
lean_closure_set(v___f_150_, 7, v_toZSMul_146_);
v___x_151_ = lp_mathlib_Equiv_instFintype___redArg(v___x_148_, v___x_148_, v___x_149_, v___x_149_);
v___x_152_ = lp_mathlib_Finset_sum___redArg(v___x_147_, v___x_151_, v___f_150_);
lean_dec_ref(v___x_147_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi(lean_object* v_R_153_, lean_object* v_M_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_n_158_, lean_object* v_E_159_, lean_object* v_u_160_, lean_object* v_00_u03b2_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg(v_inst_156_, v_n_158_, v_E_159_, v_u_160_, v_00_u03b2_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmPi___boxed(lean_object* v_R_163_, lean_object* v_M_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_n_168_, lean_object* v_E_169_, lean_object* v_u_170_, lean_object* v_00_u03b2_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = lp_tree_Formalism_BranchingDeterminantCap_bmPi(v_R_163_, v_M_164_, v_inst_165_, v_inst_166_, v_inst_167_, v_n_168_, v_E_169_, v_u_170_, v_00_u03b2_171_);
lean_dec(v_inst_167_);
lean_dec_ref(v_inst_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg(lean_object* v_inst_174_, lean_object* v_n_175_, lean_object* v_E_176_, lean_object* v_u_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg___closed__0));
v___x_179_ = lp_tree_Formalism_BranchingDeterminantCap_bmPi___redArg(v_inst_174_, v_n_175_, v_E_176_, v_u_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet(lean_object* v_R_180_, lean_object* v_M_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_n_185_, lean_object* v_E_186_, lean_object* v_u_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lp_tree_Formalism_BranchingDeterminantCap_capDet___redArg(v_inst_183_, v_n_185_, v_E_186_, v_u_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_capDet___boxed(lean_object* v_R_189_, lean_object* v_M_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_n_194_, lean_object* v_E_195_, lean_object* v_u_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lp_tree_Formalism_BranchingDeterminantCap_capDet(v_R_189_, v_M_190_, v_inst_191_, v_inst_192_, v_inst_193_, v_n_194_, v_E_195_, v_u_196_);
lean_dec(v_inst_193_);
lean_dec_ref(v_inst_191_);
return v_res_197_;
}
}
static lean_object* _init_lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_nat_to_int(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0(lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0, &lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0_once, _init_lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___boxed(lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0(v_x_202_);
lean_dec(v_x_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg(lean_object* v_i_205_, lean_object* v_x_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___f_208_; lean_object* v___x_209_; 
v___f_208_ = ((lean_object*)(lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___closed__0));
v___x_209_ = lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(v___f_208_, v_i_205_, v_x_206_, v_a_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___boxed(lean_object* v_i_210_, lean_object* v_x_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg(v_i_210_, v_x_211_, v_a_212_);
lean_dec(v_x_211_);
lean_dec(v_i_210_);
return v_res_213_;
}
}
static lean_object* _init_lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_to_int(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_zW(lean_object* v_n_216_, lean_object* v_v_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_fst_219_; lean_object* v_snd_220_; uint8_t v___x_221_; 
v_fst_219_ = lean_ctor_get(v_v_217_, 0);
v_snd_220_ = lean_ctor_get(v_v_217_, 1);
v___x_221_ = lean_nat_dec_eq(v_fst_219_, v_n_216_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec(v_a_218_);
v___x_222_ = lean_obj_once(&lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0, &lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0_once, _init_lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg___lam__0___closed__0);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0, &lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0_once, _init_lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0);
v___x_224_ = lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg(v_snd_220_, v___x_223_, v_a_218_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_zW___boxed(lean_object* v_n_225_, lean_object* v_v_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_tree_Formalism_BranchingDeterminantCap_zW(v_n_225_, v_v_226_, v_a_227_);
lean_dec_ref(v_v_226_);
lean_dec(v_n_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0(lean_object* v_n_229_, lean_object* v_i_230_, lean_object* v_x_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___redArg(v_i_230_, v_x_231_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0___boxed(lean_object* v_n_234_, lean_object* v_i_235_, lean_object* v_x_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = lp_tree_Pi_single___at___00Formalism_BranchingDeterminantCap_zW_spec__0(v_n_234_, v_i_235_, v_x_236_, v_a_237_);
lean_dec(v_x_236_);
lean_dec(v_i_235_);
lean_dec(v_n_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_lastW(lean_object* v_n_239_, lean_object* v_v_240_){
_start:
{
lean_object* v_fst_241_; uint8_t v___x_242_; 
v_fst_241_ = lean_ctor_get(v_v_240_, 0);
v___x_242_ = lean_nat_dec_eq(v_fst_241_, v_n_239_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_unsigned_to_nat(0u);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = lean_unsigned_to_nat(1u);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_lastW___boxed(lean_object* v_n_245_, lean_object* v_v_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = lp_tree_Formalism_BranchingDeterminantCap_lastW(v_n_245_, v_v_246_);
lean_dec_ref(v_v_246_);
lean_dec(v_n_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_omg___lam__0(lean_object* v_00_u03b2_248_, lean_object* v_s_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
lean_inc(v_s_249_);
v___x_250_ = lean_nat_to_int(v_s_249_);
v___x_251_ = lean_obj_once(&lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0, &lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0_once, _init_lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0);
v___x_252_ = lean_int_add(v___x_250_, v___x_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_apply_1(v_00_u03b2_248_, v_s_249_);
v___x_254_ = lean_int_mul(v___x_252_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_omg(lean_object* v_n_255_, lean_object* v_00_u03b2_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___f_257_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_omg___lam__0), 2, 1);
lean_closure_set(v___f_257_, 0, v_00_u03b2_256_);
v___x_258_ = l_List_finRange(v_n_255_);
v___x_259_ = lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(v___x_258_, v___f_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmChi___lam__0(lean_object* v_u_260_, lean_object* v_lam_261_, lean_object* v_00_u03b2_262_, lean_object* v_j_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc_n(v_j_263_, 2);
v___x_264_ = lean_nat_to_int(v_j_263_);
v___x_265_ = lean_int_add(v_u_260_, v___x_264_);
lean_dec(v___x_264_);
v___x_266_ = lean_apply_1(v_lam_261_, v_j_263_);
v___x_267_ = lean_nat_to_int(v___x_266_);
v___x_268_ = lean_apply_1(v_00_u03b2_262_, v_j_263_);
v___x_269_ = lean_int_sub(v___x_267_, v___x_268_);
lean_dec(v___x_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_int_sub(v___x_265_, v___x_269_);
lean_dec(v___x_269_);
lean_dec(v___x_265_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmChi___lam__0___boxed(lean_object* v_u_271_, lean_object* v_lam_272_, lean_object* v_00_u03b2_273_, lean_object* v_j_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = lp_tree_Formalism_BranchingDeterminantCap_bmChi___lam__0(v_u_271_, v_lam_272_, v_00_u03b2_273_, v_j_274_);
lean_dec(v_u_271_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0(lean_object* v_s_277_){
_start:
{
lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___f_278_ = ((lean_object*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0___closed__0));
v___x_279_ = lean_obj_once(&lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0, &lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0_once, _init_lp_tree_Formalism_BranchingDeterminantCap_zW___closed__0);
v___x_280_ = l_List_foldrTR___redArg(v___f_278_, v___x_279_, v_s_277_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0___redArg(lean_object* v_s_281_, lean_object* v_f_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lp_mathlib_Multiset_map___redArg(v_f_282_, v_s_281_);
v___x_284_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0_spec__0(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmChi(lean_object* v_n_285_, lean_object* v_lam_286_, lean_object* v_00_u03b2_287_, lean_object* v_u_288_){
_start:
{
lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___f_289_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmChi___lam__0___boxed), 4, 3);
lean_closure_set(v___f_289_, 0, v_u_288_);
lean_closure_set(v___f_289_, 1, v_lam_286_);
lean_closure_set(v___f_289_, 2, v_00_u03b2_287_);
v___x_290_ = l_List_finRange(v_n_285_);
v___x_291_ = lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0___redArg(v___x_290_, v___f_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0(lean_object* v_00_u03b9_292_, lean_object* v_s_293_, lean_object* v_f_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lp_tree_Finset_prod___at___00Formalism_BranchingDeterminantCap_bmChi_spec__0___redArg(v_s_293_, v_f_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmRho___lam__0(lean_object* v_lam_296_, lean_object* v_sg_297_, lean_object* v_s_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_inc(v_s_298_);
v___x_299_ = lean_apply_1(v_lam_296_, v_s_298_);
v___x_300_ = lean_apply_1(v_sg_297_, v_s_298_);
v___x_301_ = lean_nat_sub(v___x_299_, v___x_300_);
lean_dec(v___x_300_);
lean_dec(v___x_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_bmRho(lean_object* v_n_302_, lean_object* v_lam_303_, lean_object* v_sg_304_, lean_object* v_a_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = lean_nat_dec_lt(v_a_305_, v_n_302_);
if (v___x_306_ == 0)
{
lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_a_305_);
v___f_307_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_bmRho___lam__0), 3, 2);
lean_closure_set(v___f_307_, 0, v_lam_303_);
lean_closure_set(v___f_307_, 1, v_sg_304_);
v___x_308_ = l_List_finRange(v_n_302_);
v___x_309_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_308_, v___f_307_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
lean_dec_ref(v_lam_303_);
lean_dec(v_n_302_);
v___x_310_ = lean_apply_1(v_sg_304_, v_a_305_);
return v___x_310_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalC(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementW(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
