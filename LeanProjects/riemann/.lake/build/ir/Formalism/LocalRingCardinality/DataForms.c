// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataForms
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.LocalRingCardinality.DataHost public import Formalism.LocalRingCardinality.DataCoeff public import Formalism.LocalRingCardinality.DataArith public import Formalism.LocalRingCardinality.DataKernels public import Formalism.LocalRingCardinality.DataRows
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
extern lean_object* lp_mathlib_Int_instAddCommMonoid;
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_locW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_locW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_S(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_S___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_SP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_SP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_aTop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_aTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_aTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW(lean_object* v_LL_1_, lean_object* v_inst_2_, lean_object* v_Pl_3_, lean_object* v_w_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_intW___boxed(lean_object* v_LL_6_, lean_object* v_inst_7_, lean_object* v_Pl_8_, lean_object* v_w_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_BasicNotions_intW(v_LL_6_, v_inst_7_, v_Pl_8_, v_w_9_);
lean_dec(v_w_9_);
lean_dec_ref(v_Pl_8_);
lean_dec_ref(v_inst_7_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_locW(lean_object* v_LL_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_Pl_14_, lean_object* v_w_15_, lean_object* v_V_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_L_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_locW___boxed(lean_object* v_LL_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_Pl_25_, lean_object* v_w_26_, lean_object* v_V_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_L_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_BasicNotions_locW(v_LL_22_, v_inst_23_, v_inst_24_, v_Pl_25_, v_w_26_, v_V_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_L_31_);
lean_dec(v_inst_30_);
lean_dec(v_inst_29_);
lean_dec_ref(v_inst_28_);
lean_dec(v_w_26_);
lean_dec_ref(v_Pl_25_);
lean_dec_ref(v_inst_23_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_S(lean_object* v_R_33_, lean_object* v_LL_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_embLL_38_, lean_object* v_Pl_39_, lean_object* v_Tau_40_, lean_object* v_inst_41_, lean_object* v_hc_42_, lean_object* v_C_43_, lean_object* v_A_44_, lean_object* v_P_45_, lean_object* v_M_46_, lean_object* v_i_47_, lean_object* v_w_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_S___boxed(lean_object* v_R_50_, lean_object* v_LL_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_embLL_55_, lean_object* v_Pl_56_, lean_object* v_Tau_57_, lean_object* v_inst_58_, lean_object* v_hc_59_, lean_object* v_C_60_, lean_object* v_A_61_, lean_object* v_P_62_, lean_object* v_M_63_, lean_object* v_i_64_, lean_object* v_w_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_BasicNotions_MemberForms_S(v_R_50_, v_LL_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_embLL_55_, v_Pl_56_, v_Tau_57_, v_inst_58_, v_hc_59_, v_C_60_, v_A_61_, v_P_62_, v_M_63_, v_i_64_, v_w_65_);
lean_dec(v_w_65_);
lean_dec(v_i_64_);
lean_dec_ref(v_M_63_);
lean_dec_ref(v_P_62_);
lean_dec_ref(v_A_61_);
lean_dec_ref(v_C_60_);
lean_dec_ref(v_hc_59_);
lean_dec(v_inst_58_);
lean_dec_ref(v_Pl_56_);
lean_dec_ref(v_embLL_55_);
lean_dec(v_inst_54_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_R_50_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_SP(lean_object* v_R_67_, lean_object* v_LL_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_embLL_72_, lean_object* v_Pl_73_, lean_object* v_Tau_74_, lean_object* v_inst_75_, lean_object* v_hc_76_, lean_object* v_C_77_, lean_object* v_A_78_, lean_object* v_P_79_, lean_object* v_M_80_, lean_object* v_w_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_SP___boxed(lean_object* v_R_83_, lean_object* v_LL_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_embLL_88_, lean_object* v_Pl_89_, lean_object* v_Tau_90_, lean_object* v_inst_91_, lean_object* v_hc_92_, lean_object* v_C_93_, lean_object* v_A_94_, lean_object* v_P_95_, lean_object* v_M_96_, lean_object* v_w_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_BasicNotions_MemberForms_SP(v_R_83_, v_LL_84_, v_inst_85_, v_inst_86_, v_inst_87_, v_embLL_88_, v_Pl_89_, v_Tau_90_, v_inst_91_, v_hc_92_, v_C_93_, v_A_94_, v_P_95_, v_M_96_, v_w_97_);
lean_dec(v_w_97_);
lean_dec_ref(v_M_96_);
lean_dec_ref(v_P_95_);
lean_dec_ref(v_A_94_);
lean_dec_ref(v_C_93_);
lean_dec_ref(v_hc_92_);
lean_dec(v_inst_91_);
lean_dec_ref(v_Pl_89_);
lean_dec_ref(v_embLL_88_);
lean_dec(v_inst_87_);
lean_dec_ref(v_inst_85_);
lean_dec_ref(v_R_83_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_aTop___redArg(lean_object* v_M_99_, lean_object* v_00_u03c4_100_){
_start:
{
lean_object* v_lam_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_lam_101_ = lean_ctor_get(v_M_99_, 14);
lean_inc_ref(v_lam_101_);
lean_dec_ref(v_M_99_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_apply_3(v_lam_101_, v___x_102_, v_00_u03c4_100_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_aTop(lean_object* v_R_104_, lean_object* v_LL_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_embLL_109_, lean_object* v_Pl_110_, lean_object* v_Tau_111_, lean_object* v_inst_112_, lean_object* v_hc_113_, lean_object* v_C_114_, lean_object* v_A_115_, lean_object* v_P_116_, lean_object* v_M_117_, lean_object* v_00_u03c4_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_tree_Formalism_BasicNotions_MemberForms_aTop___redArg(v_M_117_, v_00_u03c4_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_aTop___boxed(lean_object* v_R_120_, lean_object* v_LL_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_embLL_125_, lean_object* v_Pl_126_, lean_object* v_Tau_127_, lean_object* v_inst_128_, lean_object* v_hc_129_, lean_object* v_C_130_, lean_object* v_A_131_, lean_object* v_P_132_, lean_object* v_M_133_, lean_object* v_00_u03c4_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_tree_Formalism_BasicNotions_MemberForms_aTop(v_R_120_, v_LL_121_, v_inst_122_, v_inst_123_, v_inst_124_, v_embLL_125_, v_Pl_126_, v_Tau_127_, v_inst_128_, v_hc_129_, v_C_130_, v_A_131_, v_P_132_, v_M_133_, v_00_u03c4_134_);
lean_dec_ref(v_P_132_);
lean_dec_ref(v_A_131_);
lean_dec_ref(v_C_130_);
lean_dec_ref(v_hc_129_);
lean_dec(v_inst_128_);
lean_dec_ref(v_Pl_126_);
lean_dec_ref(v_embLL_125_);
lean_dec(v_inst_124_);
lean_dec_ref(v_inst_122_);
lean_dec_ref(v_R_120_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop___redArg(lean_object* v_R_136_, lean_object* v_M_137_, lean_object* v_00_u03c4_138_){
_start:
{
lean_object* v_lam_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_lam_139_ = lean_ctor_get(v_M_137_, 14);
lean_inc_ref(v_lam_139_);
lean_dec_ref(v_M_137_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_136_, v___x_140_);
v___x_142_ = lean_apply_2(v_lam_139_, v___x_140_, v_00_u03c4_138_);
v___x_143_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v___x_141_, v___x_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_int_neg(v___x_143_);
lean_dec(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop___redArg___boxed(lean_object* v_R_145_, lean_object* v_M_146_, lean_object* v_00_u03c4_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_tree_Formalism_BasicNotions_MemberForms_bTop___redArg(v_R_145_, v_M_146_, v_00_u03c4_147_);
lean_dec_ref(v_R_145_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop(lean_object* v_R_149_, lean_object* v_LL_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_embLL_154_, lean_object* v_Pl_155_, lean_object* v_Tau_156_, lean_object* v_inst_157_, lean_object* v_hc_158_, lean_object* v_C_159_, lean_object* v_A_160_, lean_object* v_P_161_, lean_object* v_M_162_, lean_object* v_00_u03c4_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lp_tree_Formalism_BasicNotions_MemberForms_bTop___redArg(v_R_149_, v_M_162_, v_00_u03c4_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_bTop___boxed(lean_object* v_R_165_, lean_object* v_LL_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_embLL_170_, lean_object* v_Pl_171_, lean_object* v_Tau_172_, lean_object* v_inst_173_, lean_object* v_hc_174_, lean_object* v_C_175_, lean_object* v_A_176_, lean_object* v_P_177_, lean_object* v_M_178_, lean_object* v_00_u03c4_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_tree_Formalism_BasicNotions_MemberForms_bTop(v_R_165_, v_LL_166_, v_inst_167_, v_inst_168_, v_inst_169_, v_embLL_170_, v_Pl_171_, v_Tau_172_, v_inst_173_, v_hc_174_, v_C_175_, v_A_176_, v_P_177_, v_M_178_, v_00_u03c4_179_);
lean_dec_ref(v_P_177_);
lean_dec_ref(v_A_176_);
lean_dec_ref(v_C_175_);
lean_dec_ref(v_hc_174_);
lean_dec(v_inst_173_);
lean_dec_ref(v_Pl_171_);
lean_dec_ref(v_embLL_170_);
lean_dec(v_inst_169_);
lean_dec_ref(v_inst_167_);
lean_dec_ref(v_R_165_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg___lam__0(lean_object* v_M_181_, lean_object* v_00_u03c4_182_, lean_object* v_i_183_){
_start:
{
lean_object* v_sg_184_; lean_object* v___x_185_; 
v_sg_184_ = lean_ctor_get(v_M_181_, 15);
lean_inc_ref(v_sg_184_);
lean_dec_ref(v_M_181_);
v___x_185_ = lean_apply_2(v_sg_184_, v_00_u03c4_182_, v_i_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg___lam__1(lean_object* v_M_186_, lean_object* v_m_187_, lean_object* v_00_u03c4_188_, lean_object* v_i_189_){
_start:
{
lean_object* v_lam_190_; lean_object* v___x_191_; 
v_lam_190_ = lean_ctor_get(v_M_186_, 14);
lean_inc_ref(v_lam_190_);
lean_dec_ref(v_M_186_);
v___x_191_ = lean_apply_3(v_lam_190_, v_m_187_, v_00_u03c4_188_, v_i_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg(lean_object* v_R_192_, lean_object* v_M_193_, lean_object* v_00_u03c4_194_){
_start:
{
lean_object* v___x_195_; lean_object* v_m_196_; lean_object* v_t_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_195_ = lp_mathlib_Int_instAddCommMonoid;
v_m_196_ = lean_ctor_get(v_R_192_, 2);
lean_inc_n(v_m_196_, 2);
v_t_197_ = lean_ctor_get(v_R_192_, 3);
lean_inc(v_t_197_);
lean_inc(v_00_u03c4_194_);
lean_inc_ref(v_M_193_);
v___f_198_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg___lam__0), 3, 2);
lean_closure_set(v___f_198_, 0, v_M_193_);
lean_closure_set(v___f_198_, 1, v_00_u03c4_194_);
v___f_199_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg___lam__1), 4, 3);
lean_closure_set(v___f_199_, 0, v_M_193_);
lean_closure_set(v___f_199_, 1, v_m_196_);
lean_closure_set(v___f_199_, 2, v_00_u03c4_194_);
v___x_200_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_192_, v_m_196_);
lean_dec_ref(v_R_192_);
lean_inc(v___x_200_);
v___x_201_ = l_List_finRange(v___x_200_);
v___x_202_ = lp_mathlib_Finset_sum___redArg(v___x_195_, v___x_201_, v___f_199_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_sub(v___x_200_, v___x_203_);
lean_dec(v___x_200_);
v___x_205_ = l_List_finRange(v___x_204_);
v___x_206_ = lp_mathlib_Finset_sum___redArg(v___x_195_, v___x_205_, v___f_198_);
v___x_207_ = lean_int_sub(v___x_202_, v___x_206_);
lean_dec(v___x_206_);
lean_dec(v___x_202_);
v___x_208_ = lean_nat_add(v_t_197_, v___x_203_);
lean_dec(v_t_197_);
v___x_209_ = lean_nat_mul(v_m_196_, v___x_208_);
lean_dec(v___x_208_);
lean_dec(v_m_196_);
v___x_210_ = lean_nat_shiftr(v___x_209_, v___x_203_);
lean_dec(v___x_209_);
v___x_211_ = lean_nat_to_int(v___x_210_);
v___x_212_ = lean_int_sub(v___x_207_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v___x_207_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg(lean_object* v_R_213_, lean_object* v_LL_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_embLL_218_, lean_object* v_Pl_219_, lean_object* v_Tau_220_, lean_object* v_inst_221_, lean_object* v_hc_222_, lean_object* v_C_223_, lean_object* v_A_224_, lean_object* v_P_225_, lean_object* v_M_226_, lean_object* v_00_u03c4_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lp_tree_Formalism_BasicNotions_MemberForms_deg___redArg(v_R_213_, v_M_226_, v_00_u03c4_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_MemberForms_deg___boxed(lean_object* v_R_229_, lean_object* v_LL_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_embLL_234_, lean_object* v_Pl_235_, lean_object* v_Tau_236_, lean_object* v_inst_237_, lean_object* v_hc_238_, lean_object* v_C_239_, lean_object* v_A_240_, lean_object* v_P_241_, lean_object* v_M_242_, lean_object* v_00_u03c4_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = lp_tree_Formalism_BasicNotions_MemberForms_deg(v_R_229_, v_LL_230_, v_inst_231_, v_inst_232_, v_inst_233_, v_embLL_234_, v_Pl_235_, v_Tau_236_, v_inst_237_, v_hc_238_, v_C_239_, v_A_240_, v_P_241_, v_M_242_, v_00_u03c4_243_);
lean_dec_ref(v_P_241_);
lean_dec_ref(v_A_240_);
lean_dec_ref(v_C_239_);
lean_dec_ref(v_hc_238_);
lean_dec(v_inst_237_);
lean_dec_ref(v_Pl_235_);
lean_dec_ref(v_embLL_234_);
lean_dec(v_inst_233_);
lean_dec_ref(v_inst_231_);
return v_res_244_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataHost(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataCoeff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKernels(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataRows(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForms(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataHost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataCoeff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKernels(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
