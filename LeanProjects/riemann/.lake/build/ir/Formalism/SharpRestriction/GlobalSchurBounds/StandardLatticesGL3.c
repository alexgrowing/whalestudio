// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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
lean_object* lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pullB___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pullB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_LaB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_LaB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_subLa(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_subLa___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_toAddMonoidHom___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_toAddMonoidHom___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_map___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_map___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_cBar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0___closed__0 = (const lean_object*)&lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_La0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_La0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__0(lean_object* v_T_1_, lean_object* v_z_2_, lean_object* v_00_u03c4_3_, lean_object* v_a_4_, lean_object* v_b_5_, lean_object* v_j_6_, lean_object* v_c_7_){
_start:
{
lean_object* v_emb_8_; lean_object* v___x_9_; lean_object* v_re_10_; lean_object* v_im_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_emb_8_ = lean_ctor_get(v_T_1_, 0);
lean_inc_ref(v_emb_8_);
lean_dec_ref(v_T_1_);
lean_inc(v_c_7_);
lean_inc(v_a_4_);
lean_inc(v_00_u03c4_3_);
v___x_9_ = lean_apply_3(v_z_2_, v_00_u03c4_3_, v_a_4_, v_c_7_);
v_re_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_re_10_);
v_im_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_im_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_apply_3(v_b_5_, v_j_6_, v_a_4_, v_c_7_);
v___x_13_ = lean_apply_2(v_emb_8_, v_00_u03c4_3_, v___x_12_);
v___x_14_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(v___x_13_);
v___x_15_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_10_, v_im_11_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__1(lean_object* v_T_16_, lean_object* v_z_17_, lean_object* v_00_u03c4_18_, lean_object* v_b_19_, lean_object* v_j_20_, lean_object* v_N_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__0), 7, 6);
lean_closure_set(v___f_23_, 0, v_T_16_);
lean_closure_set(v___f_23_, 1, v_z_17_);
lean_closure_set(v___f_23_, 2, v_00_u03c4_18_);
lean_closure_set(v___f_23_, 3, v_a_22_);
lean_closure_set(v___f_23_, 4, v_b_19_);
lean_closure_set(v___f_23_, 5, v_j_20_);
v___x_24_ = l_List_finRange(v_N_21_);
v___x_25_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v___x_24_, v___f_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__2(lean_object* v_T_26_, lean_object* v_z_27_, lean_object* v_b_28_, lean_object* v_j_29_, lean_object* v_N_30_, lean_object* v_N_x27_31_, lean_object* v_00_u03c4_32_){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__1), 7, 6);
lean_closure_set(v___f_33_, 0, v_T_26_);
lean_closure_set(v___f_33_, 1, v_z_27_);
lean_closure_set(v___f_33_, 2, v_00_u03c4_32_);
lean_closure_set(v___f_33_, 3, v_b_28_);
lean_closure_set(v___f_33_, 4, v_j_29_);
lean_closure_set(v___f_33_, 5, v_N_30_);
v___x_34_ = l_List_finRange(v_N_x27_31_);
v___x_35_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v___x_34_, v___f_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg(lean_object* v_D_36_, lean_object* v_T_37_, lean_object* v_N_38_, lean_object* v_N_x27_39_, lean_object* v_b_40_, lean_object* v_j_41_, lean_object* v_z_42_){
_start:
{
lean_object* v_what_u2082_43_; lean_object* v_instTau_44_; lean_object* v___f_45_; lean_object* v___x_46_; 
v_what_u2082_43_ = lean_ctor_get(v_D_36_, 4);
lean_inc_ref(v_what_u2082_43_);
lean_dec_ref(v_D_36_);
v_instTau_44_ = lean_ctor_get(v_what_u2082_43_, 5);
lean_inc(v_instTau_44_);
lean_dec_ref(v_what_u2082_43_);
v___f_45_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg___lam__2), 7, 6);
lean_closure_set(v___f_45_, 0, v_T_37_);
lean_closure_set(v___f_45_, 1, v_z_42_);
lean_closure_set(v___f_45_, 2, v_b_40_);
lean_closure_set(v___f_45_, 3, v_j_41_);
lean_closure_set(v___f_45_, 4, v_N_38_);
lean_closure_set(v___f_45_, 5, v_N_x27_39_);
v___x_46_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v_instTau_44_, v___f_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB(lean_object* v_D_47_, lean_object* v_T_48_, lean_object* v_N_49_, lean_object* v_N_x27_50_, lean_object* v_r_51_, lean_object* v_b_52_, lean_object* v_j_53_, lean_object* v_z_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg(v_D_47_, v_T_48_, v_N_49_, v_N_x27_50_, v_b_52_, v_j_53_, v_z_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___boxed(lean_object* v_D_56_, lean_object* v_T_57_, lean_object* v_N_58_, lean_object* v_N_x27_59_, lean_object* v_r_60_, lean_object* v_b_61_, lean_object* v_j_62_, lean_object* v_z_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB(v_D_56_, v_T_57_, v_N_58_, v_N_x27_59_, v_r_60_, v_b_61_, v_j_62_, v_z_63_);
lean_dec(v_r_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pullB___lam__0(lean_object* v_D_65_, lean_object* v_T_66_, lean_object* v_N_67_, lean_object* v_N_x27_68_, lean_object* v_b_69_, lean_object* v_z_70_, lean_object* v_g_71_, lean_object* v_j_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_coordB___redArg(v_D_65_, v_T_66_, v_N_67_, v_N_x27_68_, v_b_69_, v_j_72_, v_z_70_);
v___x_74_ = lean_apply_1(v_g_71_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pullB(lean_object* v_D_75_, lean_object* v_T_76_, lean_object* v_N_77_, lean_object* v_N_x27_78_, lean_object* v_r_79_, lean_object* v_b_80_, lean_object* v_g_81_, lean_object* v_z_82_){
_start:
{
lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___f_83_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_StandardLatticesGL3_pullB___lam__0), 8, 7);
lean_closure_set(v___f_83_, 0, v_D_75_);
lean_closure_set(v___f_83_, 1, v_T_76_);
lean_closure_set(v___f_83_, 2, v_N_77_);
lean_closure_set(v___f_83_, 3, v_N_x27_78_);
lean_closure_set(v___f_83_, 4, v_b_80_);
lean_closure_set(v___f_83_, 5, v_z_82_);
lean_closure_set(v___f_83_, 6, v_g_81_);
v___x_84_ = l_List_finRange(v_r_79_);
v___x_85_ = lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1___redArg(v___x_84_, v___f_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_LaB(lean_object* v_D_86_, lean_object* v_T_87_, lean_object* v_N_88_, lean_object* v_N_x27_89_, lean_object* v_r_90_, lean_object* v_b_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_LaB___boxed(lean_object* v_D_93_, lean_object* v_T_94_, lean_object* v_N_95_, lean_object* v_N_x27_96_, lean_object* v_r_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_LaB(v_D_93_, v_T_94_, v_N_95_, v_N_x27_96_, v_r_97_, v_b_98_);
lean_dec(v_b_98_);
lean_dec(v_r_97_);
lean_dec(v_N_x27_96_);
lean_dec(v_N_95_);
lean_dec_ref(v_T_94_);
lean_dec_ref(v_D_93_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_subLa(lean_object* v_V_100_, lean_object* v_inst_101_, lean_object* v_m_102_, lean_object* v_A_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_subLa___boxed(lean_object* v_V_105_, lean_object* v_inst_106_, lean_object* v_m_107_, lean_object* v_A_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_subLa(v_V_105_, v_inst_106_, v_m_107_, v_A_108_);
lean_dec(v_m_107_);
lean_dec_ref(v_inst_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_toAddMonoidHom___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__0(lean_object* v_self_110_){
_start:
{
lean_inc_ref(v_self_110_);
return v_self_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_toAddMonoidHom___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__0___boxed(lean_object* v_self_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_tree_RingHom_toAddMonoidHom___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__0(v_self_111_);
lean_dec_ref(v_self_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_map___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__1(lean_object* v_f_113_, lean_object* v_H_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_map___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__1___boxed(lean_object* v_f_116_, lean_object* v_H_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_tree_AddSubgroup_map___at___00Formalism_MainNotions_StandardLatticesGL3_torBar_spec__1(v_f_116_, v_H_117_);
lean_dec_ref(v_f_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___redArg___lam__0(lean_object* v_emb_119_, lean_object* v_00_u03c4_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_apply_2(v_emb_119_, v_00_u03c4_120_, v_x_121_);
v___x_123_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___redArg(lean_object* v_T_124_){
_start:
{
lean_object* v_emb_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_134_; 
v_emb_125_ = lean_ctor_get(v_T_124_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_T_124_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_T_124_, 1);
lean_dec(v_unused_135_);
v___x_127_ = v_T_124_;
v_isShared_128_ = v_isSharedCheck_134_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_emb_125_);
lean_dec(v_T_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_134_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___f_129_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___redArg___lam__0), 3, 1);
lean_closure_set(v___f_129_, 0, v_emb_125_);
v___x_130_ = lean_box(0);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_130_);
lean_ctor_set(v___x_127_, 0, v___f_129_);
v___x_132_ = v___x_127_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___f_129_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar(lean_object* v_D_136_, lean_object* v_T_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___redArg(v_T_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar___boxed(lean_object* v_D_139_, lean_object* v_T_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_torBar(v_D_139_, v_T_140_);
lean_dec_ref(v_D_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar___redArg(lean_object* v_z_142_, lean_object* v_00_u03c4_143_, lean_object* v_i_144_, lean_object* v_j_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_apply_3(v_z_142_, v_00_u03c4_143_, v_i_144_, v_j_145_);
v___x_147_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar(lean_object* v_D_148_, lean_object* v_N_149_, lean_object* v_N_x27_150_, lean_object* v_z_151_, lean_object* v_00_u03c4_152_, lean_object* v_i_153_, lean_object* v_j_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar___redArg(v_z_151_, v_00_u03c4_152_, v_i_153_, v_j_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar___boxed(lean_object* v_D_156_, lean_object* v_N_157_, lean_object* v_N_x27_158_, lean_object* v_z_159_, lean_object* v_00_u03c4_160_, lean_object* v_i_161_, lean_object* v_j_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar(v_D_156_, v_N_157_, v_N_x27_158_, v_z_159_, v_00_u03c4_160_, v_i_161_, v_j_162_);
lean_dec(v_N_x27_158_);
lean_dec(v_N_157_);
lean_dec_ref(v_D_156_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_cBar(lean_object* v_D_164_, lean_object* v_N_165_, lean_object* v_N_x27_166_, lean_object* v_G_167_, lean_object* v_z_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_StandardLatticesGL3_vBar___boxed), 7, 4);
lean_closure_set(v___x_169_, 0, v_D_164_);
lean_closure_set(v___x_169_, 1, v_N_165_);
lean_closure_set(v___x_169_, 2, v_N_x27_166_);
lean_closure_set(v___x_169_, 3, v_z_168_);
v___x_170_ = lean_apply_1(v_G_167_, v___x_169_);
v___x_171_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__2(lean_object* v___x_172_, lean_object* v_I_173_, lean_object* v_p_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__2___boxed(lean_object* v___x_176_, lean_object* v_I_177_, lean_object* v_p_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lp_tree_Submodule_pi___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__2(v___x_176_, v_I_177_, v_p_178_);
lean_dec_ref(v_p_178_);
lean_dec_ref(v___x_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg___lam__0(lean_object* v___x_180_, lean_object* v_f_181_, lean_object* v_x_182_, lean_object* v_b_183_){
_start:
{
lean_object* v_toCommSemiring_184_; lean_object* v___x_185_; lean_object* v_toMul_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_toCommSemiring_184_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_toCommSemiring_184_);
lean_dec_ref(v___x_180_);
v___x_185_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_184_);
v_toMul_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_toMul_186_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_apply_1(v_f_181_, v_b_183_);
v___x_188_ = lean_apply_2(v_toMul_186_, v___x_187_, v_x_182_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg(lean_object* v___x_189_, lean_object* v_f_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_instField_192_; lean_object* v___x_193_; lean_object* v___f_194_; 
v_instField_192_ = lean_ctor_get(v___x_189_, 3);
v___x_193_ = lp_mathlib_Field_toSemifield___redArg(v_instField_192_);
v___f_194_ = lean_alloc_closure((void*)(lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg___lam__0), 4, 3);
lean_closure_set(v___f_194_, 0, v___x_193_);
lean_closure_set(v___f_194_, 1, v_f_190_);
lean_closure_set(v___f_194_, 2, v_x_191_);
return v___f_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg___boxed(lean_object* v___x_195_, lean_object* v_f_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg(v___x_195_, v_f_196_, v_x_197_);
lean_dec_ref(v___x_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0(lean_object* v___x_200_, lean_object* v_x_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___x_203_; 
v___f_202_ = ((lean_object*)(lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0___closed__0));
v___x_203_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg(v___x_200_, v___f_202_, v_x_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0___boxed(lean_object* v___x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = lp_tree_LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0(v___x_204_, v_x_205_);
lean_dec_ref(v___x_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__2(lean_object* v___x_207_, lean_object* v_00_u03c3_u2081_u2082_208_, lean_object* v_inst_209_, lean_object* v_f_210_, lean_object* v_p_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_box(0);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__2___boxed(lean_object* v___x_213_, lean_object* v_00_u03c3_u2081_u2082_214_, lean_object* v_inst_215_, lean_object* v_f_216_, lean_object* v_p_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__2(v___x_213_, v_00_u03c3_u2081_u2082_214_, v_inst_215_, v_f_216_, v_p_217_);
lean_dec(v_f_216_);
lean_dec(v_00_u03c3_u2081_u2082_214_);
lean_dec_ref(v___x_213_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__3(lean_object* v___x_219_, lean_object* v_p_220_, lean_object* v_s_221_, lean_object* v_hs_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__3___boxed(lean_object* v___x_224_, lean_object* v_p_225_, lean_object* v_s_226_, lean_object* v_hs_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1_spec__3(v___x_224_, v_p_225_, v_s_226_, v_hs_227_);
lean_dec_ref(v___x_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___redArg(lean_object* v___x_229_, lean_object* v_00_u03c4_u2081_u2082_230_, lean_object* v_f_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(0);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___redArg___boxed(lean_object* v___x_233_, lean_object* v_00_u03c4_u2081_u2082_234_, lean_object* v_f_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___redArg(v___x_233_, v_00_u03c4_u2081_u2082_234_, v_f_235_);
lean_dec(v_f_235_);
lean_dec(v_00_u03c4_u2081_u2082_234_);
lean_dec_ref(v___x_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___lam__0(lean_object* v_toSemiring_237_, lean_object* v_toHostAx_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___lam__0___boxed(lean_object* v_toSemiring_241_, lean_object* v_toHostAx_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___lam__0(v_toSemiring_241_, v_toHostAx_242_, v_x_243_);
lean_dec(v_x_243_);
lean_dec_ref(v_toHostAx_242_);
lean_dec_ref(v_toSemiring_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg(lean_object* v_D_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(0);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg___boxed(lean_object* v_D_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___redArg(v_D_247_);
lean_dec_ref(v_D_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL(lean_object* v_D_249_, lean_object* v_N_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL___boxed(lean_object* v_D_252_, lean_object* v_N_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_stdL(v_D_252_, v_N_253_);
lean_dec(v_N_253_);
lean_dec_ref(v_D_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0(lean_object* v___x_255_, lean_object* v_inst_256_, lean_object* v_f_257_, lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___redArg(v___x_255_, v_f_257_, v_x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0___boxed(lean_object* v___x_260_, lean_object* v_inst_261_, lean_object* v_f_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__0_spec__0(v___x_260_, v_inst_261_, v_f_262_, v_x_263_);
lean_dec_ref(v___x_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1(lean_object* v___x_265_, lean_object* v_00_u03c4_u2081_u2082_266_, lean_object* v_inst_267_, lean_object* v_f_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(0);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1___boxed(lean_object* v___x_270_, lean_object* v_00_u03c4_u2081_u2082_271_, lean_object* v_inst_272_, lean_object* v_f_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = lp_tree_LinearMap_range___at___00Formalism_MainNotions_StandardLatticesGL3_stdL_spec__1(v___x_270_, v_00_u03c4_u2081_u2082_271_, v_inst_272_, v_f_273_);
lean_dec(v_f_273_);
lean_dec(v_00_u03c4_u2081_u2082_271_);
lean_dec_ref(v___x_270_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt___redArg(lean_object* v_T_275_, lean_object* v_00_u03b4_276_, lean_object* v_z_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_re_281_; lean_object* v_im_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_re_281_ = lean_ctor_get(v_00_u03b4_276_, 0);
lean_inc(v_re_281_);
v_im_282_ = lean_ctor_get(v_00_u03b4_276_, 1);
lean_inc(v_im_282_);
lean_dec_ref(v_00_u03b4_276_);
v___x_283_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(v_T_275_, v_z_277_, v_a_278_, v_a_279_, v_a_280_);
v___x_284_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_281_, v_im_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt(lean_object* v_D_285_, lean_object* v_T_286_, lean_object* v_00_u03b4_287_, lean_object* v_N_288_, lean_object* v_N_x27_289_, lean_object* v_z_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt___redArg(v_T_286_, v_00_u03b4_287_, v_z_290_, v_a_291_, v_a_292_, v_a_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt___boxed(lean_object* v_D_295_, lean_object* v_T_296_, lean_object* v_00_u03b4_297_, lean_object* v_N_298_, lean_object* v_N_x27_299_, lean_object* v_z_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_pt(v_D_295_, v_T_296_, v_00_u03b4_297_, v_N_298_, v_N_x27_299_, v_z_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_N_x27_299_);
lean_dec(v_N_298_);
lean_dec_ref(v_D_295_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_La0(lean_object* v_D_305_, lean_object* v_T_306_, lean_object* v_N_307_, lean_object* v_N_x27_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLatticesGL3_La0___boxed(lean_object* v_D_310_, lean_object* v_T_311_, lean_object* v_N_312_, lean_object* v_N_x27_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = lp_tree_Formalism_MainNotions_StandardLatticesGL3_La0(v_D_310_, v_T_311_, v_N_312_, v_N_x27_313_);
lean_dec(v_N_x27_313_);
lean_dec(v_N_312_);
lean_dec_ref(v_T_311_);
lean_dec_ref(v_D_310_);
return v_res_314_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_IsDiscriminantTwelfthRootOfIdealLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_TaylorLogMetric(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GL3Theta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_StandardLatticesGL3(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_IsDiscriminantTwelfthRootOfIdealLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_TaylorLogMetric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GL3Theta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
