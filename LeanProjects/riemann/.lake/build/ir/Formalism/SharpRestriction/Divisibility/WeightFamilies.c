// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.WeightFamilies
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataDIV public import Formalism.LocalRingCardinality.DataParamsT public import Formalism.LocalRingCardinality.ConjSqrtMinusD public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts public import Formalism.GelfandTransference.EnergyIdentity
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
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_HostRaw_conj(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_rho(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_rho___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_ev___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_ev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_ev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___closed__0 = (const lean_object*)&lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_restrictScalars___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_restrictScalars___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_rho(lean_object* v_D_1_, lean_object* v_j_2_){
_start:
{
lean_object* v_R_3_; lean_object* v___x_4_; lean_object* v_snd_5_; 
v_R_3_ = lean_ctor_get(v_D_1_, 0);
v___x_4_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_3_, v_j_2_);
v_snd_5_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v___x_4_);
return v_snd_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_rho___boxed(lean_object* v_D_6_, lean_object* v_j_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_MainNotions_WeightFamilies_rho(v_D_6_, v_j_7_);
lean_dec(v_j_7_);
lean_dec_ref(v_D_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dP(lean_object* v_D_9_, lean_object* v_j_10_){
_start:
{
lean_object* v_R_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_R_11_ = lean_ctor_get(v_D_9_, 0);
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_11_);
v___x_14_ = lean_nat_mul(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lp_tree_Formalism_MainNotions_WeightFamilies_rho(v_D_9_, v_j_10_);
v___x_16_ = lean_nat_mul(v___x_14_, v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dP___boxed(lean_object* v_D_17_, lean_object* v_j_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_MainNotions_WeightFamilies_dP(v_D_17_, v_j_18_);
lean_dec(v_j_18_);
lean_dec_ref(v_D_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__0(lean_object* v_ka_20_, lean_object* v_00_u03c4_21_, lean_object* v_i_22_){
_start:
{
lean_object* v_aP_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_aP_23_ = lean_ctor_get(v_ka_20_, 0);
lean_inc_ref(v_aP_23_);
lean_dec_ref(v_ka_20_);
v___x_24_ = lean_apply_2(v_aP_23_, v_00_u03c4_21_, v_i_22_);
v___x_25_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__1(lean_object* v_ka_26_, lean_object* v_00_u03c4_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_aM_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_aM_29_ = lean_ctor_get(v_ka_26_, 1);
lean_inc_ref(v_aM_29_);
lean_dec_ref(v_ka_26_);
v___x_30_ = lean_apply_2(v_aM_29_, v_00_u03c4_27_, v_i_28_);
v___x_31_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__2(lean_object* v_R_32_, lean_object* v_j_33_, lean_object* v_ka_34_, lean_object* v_00_u03c4_35_){
_start:
{
lean_object* v___x_36_; lean_object* v_fst_37_; lean_object* v_snd_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___f_45_; 
v___x_36_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_32_, v_j_33_);
v_fst_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_fst_37_);
v_snd_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_snd_38_);
lean_dec_ref(v___x_36_);
lean_inc(v_00_u03c4_35_);
lean_inc_ref(v_ka_34_);
v___f_39_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__0), 3, 2);
lean_closure_set(v___f_39_, 0, v_ka_34_);
lean_closure_set(v___f_39_, 1, v_00_u03c4_35_);
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__1), 3, 2);
lean_closure_set(v___f_40_, 0, v_ka_34_);
lean_closure_set(v___f_40_, 1, v_00_u03c4_35_);
v___x_41_ = l_List_finRange(v_fst_37_);
v___x_42_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_41_, v___f_39_);
v___x_43_ = l_List_finRange(v_snd_38_);
v___x_44_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_43_, v___f_40_);
v___f_45_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_45_, 0, v___x_42_);
lean_closure_set(v___f_45_, 1, v___x_44_);
return v___f_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__2___boxed(lean_object* v_R_46_, lean_object* v_j_47_, lean_object* v_ka_48_, lean_object* v_00_u03c4_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__2(v_R_46_, v_j_47_, v_ka_48_, v_00_u03c4_49_);
lean_dec(v_j_47_);
lean_dec_ref(v_R_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size(lean_object* v_D_51_, lean_object* v_j_52_, lean_object* v_ka_53_){
_start:
{
lean_object* v_what_u2082_54_; lean_object* v_R_55_; lean_object* v_instTau_56_; lean_object* v___x_57_; lean_object* v_snd_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___y_64_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_what_u2082_54_ = lean_ctor_get(v_D_51_, 4);
lean_inc_ref(v_what_u2082_54_);
v_R_55_ = lean_ctor_get(v_D_51_, 0);
lean_inc_ref_n(v_R_55_, 2);
lean_dec_ref(v_D_51_);
v_instTau_56_ = lean_ctor_get(v_what_u2082_54_, 5);
lean_inc(v_instTau_56_);
lean_dec_ref(v_what_u2082_54_);
v___x_57_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_55_, v_j_52_);
v_snd_58_ = lean_ctor_get(v___x_57_, 1);
lean_inc(v_snd_58_);
lean_dec_ref(v___x_57_);
lean_inc_ref(v_ka_53_);
v___f_59_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightFamilies_Wt_size___lam__2___boxed), 4, 3);
lean_closure_set(v___f_59_, 0, v_R_55_);
lean_closure_set(v___f_59_, 1, v_j_52_);
lean_closure_set(v___f_59_, 2, v_ka_53_);
v___x_60_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v_instTau_56_, v___f_59_);
v___x_61_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_55_);
v___x_62_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_61_);
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_dec_le(v_snd_58_, v___x_76_);
if (v___x_77_ == 0)
{
v___y_64_ = v_snd_58_;
goto v___jp_63_;
}
else
{
lean_dec(v_snd_58_);
v___y_64_ = v___x_76_;
goto v___jp_63_;
}
v___jp_63_:
{
lean_object* v_n_65_; lean_object* v___x_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___f_75_; 
v_n_65_ = lean_ctor_get(v_ka_53_, 2);
lean_inc(v_n_65_);
lean_dec_ref(v_ka_53_);
v___x_66_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___y_64_);
v___f_67_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_67_, 0, v___x_62_);
lean_closure_set(v___f_67_, 1, v___x_66_);
v___x_68_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_55_);
lean_dec_ref(v_R_55_);
v___x_69_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_68_);
v___f_70_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_70_, 0, v___f_67_);
lean_closure_set(v___f_70_, 1, v___x_69_);
v___x_71_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_n_65_);
v___f_72_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_72_, 0, v___f_70_);
lean_closure_set(v___f_72_, 1, v___x_71_);
v___f_73_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_73_, 0, v___x_60_);
lean_closure_set(v___f_73_, 1, v___f_72_);
v___x_74_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_75_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_75_, 0, v___f_73_);
lean_closure_set(v___f_75_, 1, v___x_74_);
return v___f_75_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY(lean_object* v_D_78_, lean_object* v_j_79_){
_start:
{
lean_object* v_R_80_; lean_object* v___x_81_; lean_object* v_fst_82_; lean_object* v_snd_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_R_80_ = lean_ctor_get(v_D_78_, 0);
v___x_81_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_80_, v_j_79_);
v_fst_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_fst_82_);
v_snd_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc(v_snd_83_);
lean_dec_ref(v___x_81_);
v___x_84_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_80_);
v___x_85_ = lean_nat_mul(v_fst_82_, v_snd_83_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_sub(v_fst_82_, v___x_86_);
v___x_88_ = lean_nat_mul(v_fst_82_, v___x_87_);
lean_dec(v___x_87_);
lean_dec(v_fst_82_);
v___x_89_ = lean_nat_shiftr(v___x_88_, v___x_86_);
lean_dec(v___x_88_);
v___x_90_ = lean_nat_add(v___x_85_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_85_);
v___x_91_ = lean_nat_sub(v_snd_83_, v___x_86_);
v___x_92_ = lean_nat_mul(v_snd_83_, v___x_91_);
lean_dec(v___x_91_);
lean_dec(v_snd_83_);
v___x_93_ = lean_nat_shiftr(v___x_92_, v___x_86_);
lean_dec(v___x_92_);
v___x_94_ = lean_nat_add(v___x_90_, v___x_93_);
lean_dec(v___x_93_);
lean_dec(v___x_90_);
v___x_95_ = lean_nat_mul(v___x_84_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_84_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY___boxed(lean_object* v_D_96_, lean_object* v_j_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_MainNotions_WeightFamilies_dimY(v_D_96_, v_j_97_);
lean_dec(v_j_97_);
lean_dec_ref(v_D_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_ev___lam__0(lean_object* v_l_99_, lean_object* v_x_100_, lean_object* v_toMul_101_, lean_object* v_i_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_inc(v_i_102_);
v___x_103_ = lean_apply_1(v_l_99_, v_i_102_);
v___x_104_ = lean_apply_1(v_x_100_, v_i_102_);
v___x_105_ = lean_apply_2(v_toMul_101_, v___x_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0___lam__0(lean_object* v_toAdd_106_, lean_object* v_x1_107_, lean_object* v_x2_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_apply_2(v_toAdd_106_, v_x1_107_, v_x2_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0(lean_object* v___x_110_, lean_object* v_s_111_){
_start:
{
lean_object* v_instField_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_toSemiring_115_; lean_object* v_toAddCommMonoid_116_; lean_object* v___x_117_; lean_object* v_toZero_118_; lean_object* v_toAdd_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v_instField_112_ = lean_ctor_get(v___x_110_, 3);
v___x_113_ = lp_mathlib_Field_toSemifield___redArg(v_instField_112_);
v___x_114_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_113_);
v_toSemiring_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc_ref(v_toSemiring_115_);
lean_dec_ref(v___x_114_);
v_toAddCommMonoid_116_ = lean_ctor_get(v_toSemiring_115_, 0);
lean_inc_ref(v_toAddCommMonoid_116_);
lean_dec_ref(v_toSemiring_115_);
v___x_117_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_116_);
lean_dec_ref(v_toAddCommMonoid_116_);
v_toZero_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_toZero_118_);
v_toAdd_119_ = lean_ctor_get(v___x_117_, 1);
lean_inc(v_toAdd_119_);
lean_dec_ref(v___x_117_);
v___f_120_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_120_, 0, v_toAdd_119_);
v___x_121_ = l_List_foldrTR___redArg(v___f_120_, v_toZero_118_, v_s_111_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0___boxed(lean_object* v___x_122_, lean_object* v_s_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0(v___x_122_, v_s_123_);
lean_dec_ref(v___x_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(lean_object* v___x_125_, lean_object* v_s_126_, lean_object* v_f_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lp_mathlib_Multiset_map___redArg(v_f_127_, v_s_126_);
v___x_129_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0_spec__0(v___x_125_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg___boxed(lean_object* v___x_130_, lean_object* v_s_131_, lean_object* v_f_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(v___x_130_, v_s_131_, v_f_132_);
lean_dec_ref(v___x_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_ev(lean_object* v_D_134_, lean_object* v_n_135_, lean_object* v_l_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_host_138_; lean_object* v_toHostAx_139_; lean_object* v_instField_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_toSemiring_143_; lean_object* v___x_144_; lean_object* v_toMul_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___x_148_; 
v_host_138_ = lean_ctor_get(v_D_134_, 1);
v_toHostAx_139_ = lean_ctor_get(v_host_138_, 0);
v_instField_140_ = lean_ctor_get(v_toHostAx_139_, 3);
v___x_141_ = lp_mathlib_Field_toSemifield___redArg(v_instField_140_);
v___x_142_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_141_);
v_toSemiring_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc_ref(v_toSemiring_143_);
lean_dec_ref(v___x_142_);
v___x_144_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_143_);
v_toMul_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_toMul_145_);
lean_dec_ref(v___x_144_);
v___x_146_ = l_List_finRange(v_n_135_);
v___f_147_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightFamilies_ev___lam__0), 4, 3);
lean_closure_set(v___f_147_, 0, v_l_136_);
lean_closure_set(v___f_147_, 1, v_x_137_);
lean_closure_set(v___f_147_, 2, v_toMul_145_);
v___x_148_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(v_toHostAx_139_, v___x_146_, v___f_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_ev___boxed(lean_object* v_D_149_, lean_object* v_n_150_, lean_object* v_l_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_tree_Formalism_MainNotions_WeightFamilies_ev(v_D_149_, v_n_150_, v_l_151_, v_x_152_);
lean_dec_ref(v_D_149_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0(lean_object* v___x_154_, lean_object* v_00_u03b9_155_, lean_object* v_s_156_, lean_object* v_f_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(v___x_154_, v_s_156_, v_f_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___boxed(lean_object* v___x_159_, lean_object* v_00_u03b9_160_, lean_object* v_s_161_, lean_object* v_f_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0(v___x_159_, v_00_u03b9_160_, v_s_161_, v_f_162_);
lean_dec_ref(v___x_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__0(lean_object* v_R_164_, lean_object* v_l_165_, lean_object* v_i_166_, lean_object* v_toHostAx_167_, lean_object* v_A_168_, lean_object* v_toMul_169_, lean_object* v_m_170_, lean_object* v_k_171_){
_start:
{
lean_object* v_toFrame_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_toFun_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toFrame_172_ = lean_ctor_get(v_R_164_, 0);
lean_inc(v_i_166_);
v___x_173_ = lean_apply_1(v_l_165_, v_i_166_);
v___x_174_ = lp_tree_Formalism_HC_HostRaw_conj(v_toFrame_172_, v_toHostAx_167_);
v_toFun_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_toFun_175_);
lean_dec_ref(v___x_174_);
lean_inc(v_k_171_);
v___x_176_ = lean_apply_2(v_A_168_, v_i_166_, v_k_171_);
lean_inc(v_toMul_169_);
v___x_177_ = lean_apply_2(v_toMul_169_, v___x_173_, v___x_176_);
v___x_178_ = lean_apply_1(v_m_170_, v_k_171_);
v___x_179_ = lean_apply_1(v_toFun_175_, v___x_178_);
v___x_180_ = lean_apply_2(v_toMul_169_, v___x_177_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__0___boxed(lean_object* v_R_181_, lean_object* v_l_182_, lean_object* v_i_183_, lean_object* v_toHostAx_184_, lean_object* v_A_185_, lean_object* v_toMul_186_, lean_object* v_m_187_, lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__0(v_R_181_, v_l_182_, v_i_183_, v_toHostAx_184_, v_A_185_, v_toMul_186_, v_m_187_, v_k_188_);
lean_dec_ref(v_R_181_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__1(lean_object* v_R_190_, lean_object* v_l_191_, lean_object* v_toHostAx_192_, lean_object* v_A_193_, lean_object* v_toMul_194_, lean_object* v_m_195_, lean_object* v___x_196_, lean_object* v_i_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___x_199_; 
lean_inc_ref(v_toHostAx_192_);
v___f_198_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__0___boxed), 8, 7);
lean_closure_set(v___f_198_, 0, v_R_190_);
lean_closure_set(v___f_198_, 1, v_l_191_);
lean_closure_set(v___f_198_, 2, v_i_197_);
lean_closure_set(v___f_198_, 3, v_toHostAx_192_);
lean_closure_set(v___f_198_, 4, v_A_193_);
lean_closure_set(v___f_198_, 5, v_toMul_194_);
lean_closure_set(v___f_198_, 6, v_m_195_);
v___x_199_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(v_toHostAx_192_, v___x_196_, v___f_198_);
lean_dec_ref(v_toHostAx_192_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_hform(lean_object* v_D_200_, lean_object* v_n_201_, lean_object* v_A_202_, lean_object* v_l_203_, lean_object* v_m_204_){
_start:
{
lean_object* v_host_205_; lean_object* v_toHostAx_206_; lean_object* v_R_207_; lean_object* v_instField_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_toSemiring_211_; lean_object* v___x_212_; lean_object* v_toMul_213_; lean_object* v___x_214_; lean_object* v___f_215_; lean_object* v___x_216_; 
v_host_205_ = lean_ctor_get(v_D_200_, 1);
v_toHostAx_206_ = lean_ctor_get(v_host_205_, 0);
lean_inc_ref_n(v_toHostAx_206_, 2);
v_R_207_ = lean_ctor_get(v_D_200_, 0);
lean_inc_ref(v_R_207_);
lean_dec_ref(v_D_200_);
v_instField_208_ = lean_ctor_get(v_toHostAx_206_, 3);
v___x_209_ = lp_mathlib_Field_toSemifield___redArg(v_instField_208_);
v___x_210_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_209_);
v_toSemiring_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_toSemiring_211_);
lean_dec_ref(v___x_210_);
v___x_212_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_211_);
v_toMul_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_toMul_213_);
lean_dec_ref(v___x_212_);
v___x_214_ = l_List_finRange(v_n_201_);
lean_inc(v___x_214_);
v___f_215_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightFamilies_hform___lam__1), 8, 7);
lean_closure_set(v___f_215_, 0, v_R_207_);
lean_closure_set(v___f_215_, 1, v_l_203_);
lean_closure_set(v___f_215_, 2, v_toHostAx_206_);
lean_closure_set(v___f_215_, 3, v_A_202_);
lean_closure_set(v___f_215_, 4, v_toMul_213_);
lean_closure_set(v___f_215_, 5, v_m_204_);
lean_closure_set(v___f_215_, 6, v___x_214_);
v___x_216_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_WeightFamilies_ev_spec__0___redArg(v_toHostAx_206_, v___x_214_, v___f_215_);
lean_dec_ref(v_toHostAx_206_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__1(lean_object* v_X_217_, lean_object* v_j_218_, lean_object* v_ka_219_, lean_object* v_00_u03b9_220_, lean_object* v_s_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__1___boxed(lean_object* v_X_223_, lean_object* v_j_224_, lean_object* v_ka_225_, lean_object* v_00_u03b9_226_, lean_object* v_s_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__1(v_X_223_, v_j_224_, v_ka_225_, v_00_u03b9_226_, v_s_227_);
lean_dec_ref(v_s_227_);
lean_dec_ref(v_ka_225_);
lean_dec(v_j_224_);
lean_dec_ref(v_X_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__2(lean_object* v_X_229_, lean_object* v_j_230_, lean_object* v_ka_231_, lean_object* v_00_u03b9_232_, lean_object* v_s_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__2___boxed(lean_object* v_X_235_, lean_object* v_j_236_, lean_object* v_ka_237_, lean_object* v_00_u03b9_238_, lean_object* v_s_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = lp_tree_iInf___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__2(v_X_235_, v_j_236_, v_ka_237_, v_00_u03b9_238_, v_s_239_);
lean_dec_ref(v_s_239_);
lean_dec_ref(v_ka_237_);
lean_dec(v_j_236_);
lean_dec_ref(v_X_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0_spec__0(lean_object* v_X_241_, lean_object* v_j_242_, lean_object* v_ka_243_, lean_object* v_cu_244_, lean_object* v_00_u03c7_245_, lean_object* v_00_u03c3_u2081_u2082_246_, lean_object* v_f_247_, lean_object* v_p_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0_spec__0___boxed(lean_object* v_X_250_, lean_object* v_j_251_, lean_object* v_ka_252_, lean_object* v_cu_253_, lean_object* v_00_u03c7_254_, lean_object* v_00_u03c3_u2081_u2082_255_, lean_object* v_f_256_, lean_object* v_p_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0_spec__0(v_X_250_, v_j_251_, v_ka_252_, v_cu_253_, v_00_u03c7_254_, v_00_u03c3_u2081_u2082_255_, v_f_256_, v_p_257_);
lean_dec(v_f_256_);
lean_dec(v_00_u03c3_u2081_u2082_255_);
lean_dec(v_00_u03c7_254_);
lean_dec(v_cu_253_);
lean_dec_ref(v_ka_252_);
lean_dec(v_j_251_);
lean_dec_ref(v_X_250_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0(lean_object* v_X_259_, lean_object* v_j_260_, lean_object* v_ka_261_, lean_object* v_cu_262_, lean_object* v_00_u03c7_263_, lean_object* v_00_u03c4_u2081_u2082_264_, lean_object* v_f_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0___boxed(lean_object* v_X_267_, lean_object* v_j_268_, lean_object* v_ka_269_, lean_object* v_cu_270_, lean_object* v_00_u03c7_271_, lean_object* v_00_u03c4_u2081_u2082_272_, lean_object* v_f_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = lp_tree_LinearMap_ker___at___00Formalism_MainNotions_WeightFamilies_MggK_spec__0(v_X_267_, v_j_268_, v_ka_269_, v_cu_270_, v_00_u03c7_271_, v_00_u03c4_u2081_u2082_272_, v_f_273_);
lean_dec(v_f_273_);
lean_dec(v_00_u03c4_u2081_u2082_272_);
lean_dec(v_00_u03c7_271_);
lean_dec(v_cu_270_);
lean_dec_ref(v_ka_269_);
lean_dec(v_j_268_);
lean_dec_ref(v_X_267_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__0(lean_object* v_X_275_, lean_object* v_j_276_, lean_object* v_cu_277_, lean_object* v_00_u03c7_278_, lean_object* v_ka_279_, lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__0___boxed(lean_object* v_X_282_, lean_object* v_j_283_, lean_object* v_cu_284_, lean_object* v_00_u03c7_285_, lean_object* v_ka_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__0(v_X_282_, v_j_283_, v_cu_284_, v_00_u03c7_285_, v_ka_286_, v_x_287_);
lean_dec_ref(v_ka_286_);
lean_dec(v_00_u03c7_285_);
lean_dec(v_cu_284_);
lean_dec(v_j_283_);
lean_dec_ref(v_X_282_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__1(lean_object* v_X_289_, lean_object* v_j_290_, lean_object* v_cu_291_, lean_object* v_ka_292_, lean_object* v_00_u03c7_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__1___boxed(lean_object* v_X_295_, lean_object* v_j_296_, lean_object* v_cu_297_, lean_object* v_ka_298_, lean_object* v_00_u03c7_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__1(v_X_295_, v_j_296_, v_cu_297_, v_ka_298_, v_00_u03c7_299_);
lean_dec(v_00_u03c7_299_);
lean_dec_ref(v_ka_298_);
lean_dec(v_cu_297_);
lean_dec(v_j_296_);
lean_dec_ref(v_X_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__2(lean_object* v_X_301_, lean_object* v_j_302_, lean_object* v_ka_303_, lean_object* v_cu_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_box(0);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__2___boxed(lean_object* v_X_306_, lean_object* v_j_307_, lean_object* v_ka_308_, lean_object* v_cu_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___lam__2(v_X_306_, v_j_307_, v_ka_308_, v_cu_309_);
lean_dec(v_cu_309_);
lean_dec_ref(v_ka_308_);
lean_dec(v_j_307_);
lean_dec_ref(v_X_306_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg(lean_object* v_X_311_, lean_object* v_j_312_, lean_object* v_ka_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(0);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg___boxed(lean_object* v_X_315_, lean_object* v_j_316_, lean_object* v_ka_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggK___redArg(v_X_315_, v_j_316_, v_ka_317_);
lean_dec_ref(v_ka_317_);
lean_dec(v_j_316_);
lean_dec_ref(v_X_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK(lean_object* v_D_319_, lean_object* v_X_320_, lean_object* v_CR_321_, lean_object* v_T_322_, lean_object* v_c_323_, lean_object* v_j_324_, lean_object* v_ka_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(0);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggK___boxed(lean_object* v_D_327_, lean_object* v_X_328_, lean_object* v_CR_329_, lean_object* v_T_330_, lean_object* v_c_331_, lean_object* v_j_332_, lean_object* v_ka_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggK(v_D_327_, v_X_328_, v_CR_329_, v_T_330_, v_c_331_, v_j_332_, v_ka_333_);
lean_dec_ref(v_ka_333_);
lean_dec(v_j_332_);
lean_dec(v_c_331_);
lean_dec(v_T_330_);
lean_dec(v_CR_329_);
lean_dec_ref(v_X_328_);
lean_dec_ref(v_D_327_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___lam__0(lean_object* v_self_335_){
_start:
{
lean_inc(v_self_335_);
return v_self_335_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___lam__0___boxed(lean_object* v_self_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___lam__0(v_self_336_);
lean_dec(v_self_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0(lean_object* v_X_339_, lean_object* v_j_340_, lean_object* v_ka_341_, lean_object* v_p_342_){
_start:
{
lean_object* v___f_343_; 
v___f_343_ = ((lean_object*)(lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___closed__0));
return v___f_343_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0___boxed(lean_object* v_X_344_, lean_object* v_j_345_, lean_object* v_ka_346_, lean_object* v_p_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = lp_tree_Submodule_subtype___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__0(v_X_344_, v_j_345_, v_ka_346_, v_p_347_);
lean_dec_ref(v_ka_346_);
lean_dec(v_j_345_);
lean_dec_ref(v_X_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_restrictScalars___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__1(lean_object* v_X_349_, lean_object* v_j_350_, lean_object* v_ka_351_, lean_object* v_inst_352_, lean_object* v_V_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_box(0);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_restrictScalars___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__1___boxed(lean_object* v_X_355_, lean_object* v_j_356_, lean_object* v_ka_357_, lean_object* v_inst_358_, lean_object* v_V_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = lp_tree_Submodule_restrictScalars___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__1(v_X_355_, v_j_356_, v_ka_357_, v_inst_358_, v_V_359_);
lean_dec_ref(v_ka_357_);
lean_dec(v_j_356_);
lean_dec_ref(v_X_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__2(lean_object* v_X_361_, lean_object* v_j_362_, lean_object* v_ka_363_, lean_object* v___x_364_, lean_object* v_00_u03c3_u2081_u2082_365_, lean_object* v_f_366_, lean_object* v_p_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__2___boxed(lean_object* v_X_369_, lean_object* v_j_370_, lean_object* v_ka_371_, lean_object* v___x_372_, lean_object* v_00_u03c3_u2081_u2082_373_, lean_object* v_f_374_, lean_object* v_p_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = lp_tree_Submodule_comap___at___00Formalism_MainNotions_WeightFamilies_MggIn_spec__2(v_X_369_, v_j_370_, v_ka_371_, v___x_372_, v_00_u03c3_u2081_u2082_373_, v_f_374_, v_p_375_);
lean_dec(v_f_374_);
lean_dec(v_00_u03c3_u2081_u2082_373_);
lean_dec_ref(v_ka_371_);
lean_dec(v_j_370_);
lean_dec_ref(v_X_369_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___redArg(lean_object* v_X_377_, lean_object* v_j_378_, lean_object* v_ka_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___redArg___boxed(lean_object* v_X_381_, lean_object* v_j_382_, lean_object* v_ka_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___redArg(v_X_381_, v_j_382_, v_ka_383_);
lean_dec_ref(v_ka_383_);
lean_dec(v_j_382_);
lean_dec_ref(v_X_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn(lean_object* v_D_385_, lean_object* v_X_386_, lean_object* v_CR_387_, lean_object* v_T_388_, lean_object* v_c_389_, lean_object* v_j_390_, lean_object* v_ka_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_box(0);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_MggIn___boxed(lean_object* v_D_393_, lean_object* v_X_394_, lean_object* v_CR_395_, lean_object* v_T_396_, lean_object* v_c_397_, lean_object* v_j_398_, lean_object* v_ka_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = lp_tree_Formalism_MainNotions_WeightFamilies_MggIn(v_D_393_, v_X_394_, v_CR_395_, v_T_396_, v_c_397_, v_j_398_, v_ka_399_);
lean_dec_ref(v_ka_399_);
lean_dec(v_j_398_);
lean_dec(v_c_397_);
lean_dec(v_T_396_);
lean_dec(v_CR_395_);
lean_dec_ref(v_X_394_);
lean_dec_ref(v_D_393_);
return v_res_400_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParamsT(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_ConjSqrtMinusD(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(uint8_t builtin);
lean_object* initialize_tree_Formalism_GelfandTransference_EnergyIdentity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightFamilies(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParamsT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_ConjSqrtMinusD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GelfandTransference_EnergyIdentity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
