// Lean compiler output
// Module: Lib.Adelic.Unitary.ComponentsAndBlockSums
// Imports: public import Init public meta import Init public import Lib.Adelic.Witt.WittTheorem
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
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_mapEquiv___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_subtypeEquiv___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_MonoidHom_prodMap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockGL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_reindexGL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_reindexGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_reindexGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_U_sum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_U_sum___redArg___closed__0 = (const lean_object*)&lp_GRH_New_U_sum___redArg___closed__0_value;
static lean_once_cell_t lp_GRH_New_U_sum___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_U_sum___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_U_sum___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_sum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_sum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_blockSumOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_blockSumOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_blockSumOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_reindex___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_reindex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_reindex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_block___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_block(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_block___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockGL___redArg___lam__0(lean_object* v_toZero_1_, lean_object* v_g_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v_val_5_; lean_object* v_inv_6_; lean_object* v_val_7_; lean_object* v_inv_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_18_; 
v_fst_3_ = lean_ctor_get(v_g_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_g_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_g_2_);
v_val_5_ = lean_ctor_get(v_fst_3_, 0);
lean_inc(v_val_5_);
v_inv_6_ = lean_ctor_get(v_fst_3_, 1);
lean_inc(v_inv_6_);
lean_dec(v_fst_3_);
v_val_7_ = lean_ctor_get(v_snd_4_, 0);
v_inv_8_ = lean_ctor_get(v_snd_4_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_snd_4_);
if (v_isSharedCheck_18_ == 0)
{
v___x_10_ = v_snd_4_;
v_isShared_11_ = v_isSharedCheck_18_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_inv_8_);
lean_inc(v_val_7_);
lean_dec(v_snd_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_18_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_12_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_12_, 0, lean_box(0));
lean_closure_set(v___x_12_, 1, lean_box(0));
lean_closure_set(v___x_12_, 2, lean_box(0));
lean_closure_set(v___x_12_, 3, v_toZero_1_);
lean_inc_ref_n(v___x_12_, 3);
v___x_13_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_13_, 0, lean_box(0));
lean_closure_set(v___x_13_, 1, lean_box(0));
lean_closure_set(v___x_13_, 2, lean_box(0));
lean_closure_set(v___x_13_, 3, lean_box(0));
lean_closure_set(v___x_13_, 4, lean_box(0));
lean_closure_set(v___x_13_, 5, v_val_5_);
lean_closure_set(v___x_13_, 6, v___x_12_);
lean_closure_set(v___x_13_, 7, v___x_12_);
lean_closure_set(v___x_13_, 8, v_val_7_);
v___x_14_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_14_, 0, lean_box(0));
lean_closure_set(v___x_14_, 1, lean_box(0));
lean_closure_set(v___x_14_, 2, lean_box(0));
lean_closure_set(v___x_14_, 3, lean_box(0));
lean_closure_set(v___x_14_, 4, lean_box(0));
lean_closure_set(v___x_14_, 5, v_inv_6_);
lean_closure_set(v___x_14_, 6, v___x_12_);
lean_closure_set(v___x_14_, 7, v___x_12_);
lean_closure_set(v___x_14_, 8, v_inv_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_14_);
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_16_ = v___x_10_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockGL___redArg(lean_object* v_inst_19_){
_start:
{
lean_object* v_toSemiring_20_; lean_object* v___x_21_; lean_object* v_toZero_22_; lean_object* v___f_23_; 
v_toSemiring_20_ = lean_ctor_get(v_inst_19_, 0);
lean_inc_ref(v_toSemiring_20_);
lean_dec_ref(v_inst_19_);
v___x_21_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_20_);
v_toZero_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_toZero_22_);
lean_dec_ref(v___x_21_);
v___f_23_ = lean_alloc_closure((void*)(lp_GRH_New_blockGL___redArg___lam__0), 2, 1);
lean_closure_set(v___f_23_, 0, v_toZero_22_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockGL(lean_object* v_m_24_, lean_object* v_n_25_, lean_object* v_R_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_GRH_New_blockGL___redArg(v_inst_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockGL___boxed(lean_object* v_m_33_, lean_object* v_n_34_, lean_object* v_R_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_GRH_New_blockGL(v_m_33_, v_n_34_, v_R_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_inst_40_);
lean_dec(v_inst_40_);
lean_dec(v_inst_39_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_inst_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_reindexGL___redArg(lean_object* v_e_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc_ref(v_e_42_);
v___x_43_ = lp_mathlib_Matrix_reindex___redArg(v_e_42_, v_e_42_);
v___x_44_ = lp_mathlib_Units_mapEquiv___redArg(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_reindexGL(lean_object* v_m_45_, lean_object* v_n_46_, lean_object* v_R_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_e_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_GRH_New_reindexGL___redArg(v_e_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_reindexGL___boxed(lean_object* v_m_55_, lean_object* v_n_56_, lean_object* v_R_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_e_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_reindexGL(v_m_55_, v_n_56_, v_R_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_inst_62_, v_e_63_);
lean_dec(v_inst_62_);
lean_dec(v_inst_61_);
lean_dec_ref(v_inst_60_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_58_);
return v_res_64_;
}
}
static lean_object* _init_lp_GRH_New_U_sum___redArg___closed__1(void){
_start:
{
lean_object* v___f_66_; lean_object* v___x_67_; 
v___f_66_ = ((lean_object*)(lp_GRH_New_U_sum___redArg___closed__0));
v___x_67_ = lp_mathlib_MonoidHom_prodMap___redArg(v___f_66_, v___f_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_sum___redArg(lean_object* v_inst_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; 
v___x_69_ = lp_GRH_New_blockGL___redArg(v_inst_68_);
v___x_70_ = lean_obj_once(&lp_GRH_New_U_sum___redArg___closed__1, &lp_GRH_New_U_sum___redArg___closed__1_once, _init_lp_GRH_New_U_sum___redArg___closed__1);
v___f_71_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_71_, 0, v___x_70_);
lean_closure_set(v___f_71_, 1, v___x_69_);
v___f_72_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_72_, 0, v___f_71_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_sum(lean_object* v_m_73_, lean_object* v_n_74_, lean_object* v_R_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_J_82_, lean_object* v_J_x27_83_, lean_object* v_J_x27_x27_84_, lean_object* v_h_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_GRH_New_U_sum___redArg(v_inst_78_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_sum___boxed(lean_object* v_m_87_, lean_object* v_n_88_, lean_object* v_R_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_J_96_, lean_object* v_J_x27_97_, lean_object* v_J_x27_x27_98_, lean_object* v_h_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_GRH_New_U_sum(v_m_87_, v_n_88_, v_R_89_, v_inst_90_, v_inst_91_, v_inst_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_J_96_, v_J_x27_97_, v_J_x27_x27_98_, v_h_99_);
lean_dec(v_J_x27_x27_98_);
lean_dec(v_J_x27_97_);
lean_dec(v_J_96_);
lean_dec(v_inst_95_);
lean_dec(v_inst_94_);
lean_dec(v_inst_93_);
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_inst_90_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_blockSumOne___redArg(lean_object* v_inst_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_GRH_New_U_sum___redArg(v_inst_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_blockSumOne(lean_object* v_m_103_, lean_object* v_n_104_, lean_object* v_R_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_GRH_New_U_sum___redArg(v_inst_108_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_blockSumOne___boxed(lean_object* v_m_113_, lean_object* v_n_114_, lean_object* v_R_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_GRH_New_U_blockSumOne(v_m_113_, v_n_114_, v_R_115_, v_inst_116_, v_inst_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_inst_121_);
lean_dec(v_inst_121_);
lean_dec(v_inst_120_);
lean_dec(v_inst_119_);
lean_dec_ref(v_inst_117_);
lean_dec_ref(v_inst_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_reindex___redArg(lean_object* v_e_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lp_GRH_New_reindexGL___redArg(v_e_123_);
v___x_125_ = lp_mathlib_Equiv_subtypeEquiv___redArg(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_reindex(lean_object* v_m_126_, lean_object* v_n_127_, lean_object* v_R_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_e_135_, lean_object* v_J_136_, lean_object* v_J_x27_137_, lean_object* v_h_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lp_GRH_New_U_reindex___redArg(v_e_135_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_reindex___boxed(lean_object* v_m_140_, lean_object* v_n_141_, lean_object* v_R_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_e_149_, lean_object* v_J_150_, lean_object* v_J_x27_151_, lean_object* v_h_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_GRH_New_U_reindex(v_m_140_, v_n_141_, v_R_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_inst_146_, v_inst_147_, v_inst_148_, v_e_149_, v_J_150_, v_J_x27_151_, v_h_152_);
lean_dec(v_J_x27_151_);
lean_dec(v_J_150_);
lean_dec(v_inst_148_);
lean_dec(v_inst_147_);
lean_dec(v_inst_146_);
lean_dec_ref(v_inst_145_);
lean_dec_ref(v_inst_144_);
lean_dec_ref(v_inst_143_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_block___redArg(lean_object* v_inst_154_, lean_object* v_e_155_){
_start:
{
lean_object* v___x_156_; lean_object* v_toFun_157_; lean_object* v___x_158_; lean_object* v___f_159_; 
v___x_156_ = lp_GRH_New_U_reindex___redArg(v_e_155_);
v_toFun_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_toFun_157_);
lean_dec_ref(v___x_156_);
v___x_158_ = lp_GRH_New_U_sum___redArg(v_inst_154_);
v___f_159_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_159_, 0, v___x_158_);
lean_closure_set(v___f_159_, 1, v_toFun_157_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_block(lean_object* v_m_160_, lean_object* v_n_161_, lean_object* v_R_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_l_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_e_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lp_GRH_New_U_block___redArg(v_inst_165_, v_e_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_block___boxed(lean_object* v_m_174_, lean_object* v_n_175_, lean_object* v_R_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_l_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_e_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = lp_GRH_New_U_block(v_m_174_, v_n_175_, v_R_176_, v_inst_177_, v_inst_178_, v_inst_179_, v_inst_180_, v_inst_181_, v_inst_182_, v_l_183_, v_inst_184_, v_inst_185_, v_e_186_);
lean_dec_ref(v_inst_185_);
lean_dec(v_inst_184_);
lean_dec(v_inst_182_);
lean_dec(v_inst_181_);
lean_dec(v_inst_180_);
lean_dec_ref(v_inst_178_);
lean_dec_ref(v_inst_177_);
return v_res_187_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Witt_WittTheorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_Unitary_ComponentsAndBlockSums(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Adelic_Witt_WittTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
