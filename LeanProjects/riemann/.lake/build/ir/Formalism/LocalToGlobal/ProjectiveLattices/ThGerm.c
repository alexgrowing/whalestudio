// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule public import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Pj_c_u03b5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_c_u03b5___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Pj_c_u03b5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_c_u03b5___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_c_u03b5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_c_u03b5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Pj_c_u03b5___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Pj_c_u03b5___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_c_u03b5___closed__0, &lp_tree_Formalism_L2_Pj_c_u03b5___closed__0_once, _init_lp_tree_Formalism_L2_Pj_c_u03b5___closed__0);
v___x_4_ = lean_int_neg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_c_u03b5(lean_object* v_n_5_, lean_object* v_I_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_c_u03b5___closed__1, &lp_tree_Formalism_L2_Pj_c_u03b5___closed__1_once, _init_lp_tree_Formalism_L2_Pj_c_u03b5___closed__1);
v___x_8_ = l_List_lengthTR___redArg(v_I_6_);
v___x_9_ = lean_nat_sub(v_n_5_, v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = l_Int_pow(v___x_7_, v___x_9_);
lean_dec(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_c_u03b5___boxed(lean_object* v_n_11_, lean_object* v_I_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_L2_Pj_c_u03b5(v_n_11_, v_I_12_);
lean_dec(v_I_12_);
lean_dec(v_n_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen___redArg___lam__0(lean_object* v_Y_14_, lean_object* v___x_15_, lean_object* v_u_16_, lean_object* v_g_17_, lean_object* v_j_18_){
_start:
{
lean_object* v_presheaf_19_; lean_object* v_obj_20_; lean_object* v_U_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_toSemiring_24_; lean_object* v_toMonoid_25_; lean_object* v___x_26_; lean_object* v_toMul_27_; lean_object* v___x_28_; lean_object* v___x_180__overap_29_; lean_object* v___x_30_; lean_object* v_val_31_; lean_object* v_inv_32_; lean_object* v___x_33_; lean_object* v_val_34_; lean_object* v_inv_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_44_; 
v_presheaf_19_ = lean_ctor_get(v_Y_14_, 1);
v_obj_20_ = lean_ctor_get(v_presheaf_19_, 0);
v_U_21_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_U_21_);
lean_dec_ref(v___x_15_);
lean_inc(v_j_18_);
v___x_22_ = lean_apply_1(v_U_21_, v_j_18_);
lean_inc(v_obj_20_);
v___x_23_ = lean_apply_1(v_obj_20_, v___x_22_);
v_toSemiring_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_toSemiring_24_);
lean_dec_ref(v___x_23_);
v_toMonoid_25_ = lean_ctor_get(v_toSemiring_24_, 1);
lean_inc_ref(v_toMonoid_25_);
lean_dec_ref(v_toSemiring_24_);
v___x_26_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_25_);
lean_dec_ref(v_toMonoid_25_);
v_toMul_27_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_toMul_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = lean_box(0);
v___x_180__overap_29_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(v_Y_14_, v___x_28_, v___x_22_);
v___x_30_ = lean_apply_1(v___x_180__overap_29_, v_u_16_);
v_val_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_val_31_);
v_inv_32_ = lean_ctor_get(v___x_30_, 1);
lean_inc(v_inv_32_);
lean_dec_ref(v___x_30_);
v___x_33_ = lean_apply_1(v_g_17_, v_j_18_);
v_val_34_ = lean_ctor_get(v___x_33_, 0);
v_inv_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_44_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_inv_35_);
lean_inc(v_val_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
lean_inc(v_toMul_27_);
v___x_39_ = lean_apply_2(v_toMul_27_, v_val_31_, v_val_34_);
v___x_40_ = lean_apply_2(v_toMul_27_, v_inv_35_, v_inv_32_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_40_);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen___redArg(lean_object* v_Xo_45_, lean_object* v_Y_46_, lean_object* v_inst_47_, lean_object* v_00_u03c6_48_, lean_object* v_00_u03b5_49_, lean_object* v_u_50_, lean_object* v_g_51_){
_start:
{
lean_object* v_univ_52_; lean_object* v_t_53_; lean_object* v_G_54_; lean_object* v_PP_55_; lean_object* v_left_56_; lean_object* v_L_57_; lean_object* v___x_58_; lean_object* v___f_59_; 
v_univ_52_ = lean_ctor_get(v_Xo_45_, 2);
lean_inc_ref(v_univ_52_);
lean_dec_ref(v_Xo_45_);
v_t_53_ = lean_ctor_get(v_univ_52_, 0);
lean_inc_ref(v_t_53_);
lean_dec_ref(v_univ_52_);
v_G_54_ = lean_ctor_get(v_t_53_, 0);
lean_inc_ref(v_G_54_);
v_PP_55_ = lean_ctor_get(v_t_53_, 3);
lean_inc_ref(v_PP_55_);
lean_dec_ref(v_t_53_);
v_left_56_ = lean_ctor_get(v_G_54_, 0);
lean_inc(v_left_56_);
lean_dec_ref(v_G_54_);
v_L_57_ = lean_ctor_get(v_PP_55_, 0);
lean_inc_ref(v_L_57_);
lean_dec_ref(v_PP_55_);
lean_inc_ref(v_Y_46_);
v___x_58_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_left_56_, v_Y_46_, v_L_57_, v_inst_47_, v_00_u03c6_48_, v_00_u03b5_49_);
v___f_59_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_scaleGen___redArg___lam__0), 5, 4);
lean_closure_set(v___f_59_, 0, v_Y_46_);
lean_closure_set(v___f_59_, 1, v___x_58_);
lean_closure_set(v___f_59_, 2, v_u_50_);
lean_closure_set(v___f_59_, 3, v_g_51_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen(lean_object* v_E_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_H_64_, lean_object* v_Dw_65_, lean_object* v_l_66_, lean_object* v_Xo_67_, lean_object* v_Y_68_, lean_object* v_K_69_, lean_object* v_inst_70_, lean_object* v_00_u03c6_71_, lean_object* v_00_u03b5_72_, lean_object* v_u_73_, lean_object* v_g_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_tree_Formalism_L2_Pj_scaleGen___redArg(v_Xo_67_, v_Y_68_, v_inst_70_, v_00_u03c6_71_, v_00_u03b5_72_, v_u_73_, v_g_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGen___boxed(lean_object* v_E_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_H_80_, lean_object* v_Dw_81_, lean_object* v_l_82_, lean_object* v_Xo_83_, lean_object* v_Y_84_, lean_object* v_K_85_, lean_object* v_inst_86_, lean_object* v_00_u03c6_87_, lean_object* v_00_u03b5_88_, lean_object* v_u_89_, lean_object* v_g_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_Formalism_L2_Pj_scaleGen(v_E_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_H_80_, v_Dw_81_, v_l_82_, v_Xo_83_, v_Y_84_, v_K_85_, v_inst_86_, v_00_u03c6_87_, v_00_u03b5_88_, v_u_89_, v_g_90_);
lean_dec_ref(v_l_82_);
lean_dec_ref(v_Dw_81_);
lean_dec_ref(v_H_80_);
lean_dec_ref(v_inst_77_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow___redArg___lam__0(lean_object* v_Y_92_, lean_object* v_left_93_, lean_object* v_L_94_, lean_object* v_inst_95_, lean_object* v_00_u03c6_96_, lean_object* v_00_u03b5_97_, lean_object* v_g_98_, lean_object* v_k_99_, lean_object* v_j_100_){
_start:
{
lean_object* v_presheaf_101_; lean_object* v_obj_102_; lean_object* v___x_103_; lean_object* v_U_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_toSemiring_107_; lean_object* v_toMonoid_108_; lean_object* v_toNPow_109_; lean_object* v___x_110_; lean_object* v_val_111_; lean_object* v_inv_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_121_; 
v_presheaf_101_ = lean_ctor_get(v_Y_92_, 1);
v_obj_102_ = lean_ctor_get(v_presheaf_101_, 0);
lean_inc(v_obj_102_);
v___x_103_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_left_93_, v_Y_92_, v_L_94_, v_inst_95_, v_00_u03c6_96_, v_00_u03b5_97_);
v_U_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_U_104_);
lean_dec_ref(v___x_103_);
lean_inc(v_j_100_);
v___x_105_ = lean_apply_1(v_U_104_, v_j_100_);
v___x_106_ = lean_apply_1(v_obj_102_, v___x_105_);
v_toSemiring_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_toSemiring_107_);
lean_dec_ref(v___x_106_);
v_toMonoid_108_ = lean_ctor_get(v_toSemiring_107_, 1);
lean_inc_ref(v_toMonoid_108_);
lean_dec_ref(v_toSemiring_107_);
v_toNPow_109_ = lean_ctor_get(v_toMonoid_108_, 2);
lean_inc(v_toNPow_109_);
lean_dec_ref(v_toMonoid_108_);
v___x_110_ = lean_apply_1(v_g_98_, v_j_100_);
v_val_111_ = lean_ctor_get(v___x_110_, 0);
v_inv_112_ = lean_ctor_get(v___x_110_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_121_ == 0)
{
v___x_114_ = v___x_110_;
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_inv_112_);
lean_inc(v_val_111_);
lean_dec(v___x_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
lean_inc(v_toNPow_109_);
lean_inc(v_k_99_);
v___x_116_ = lean_apply_2(v_toNPow_109_, v_k_99_, v_val_111_);
v___x_117_ = lean_apply_2(v_toNPow_109_, v_k_99_, v_inv_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_117_);
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow___redArg(lean_object* v_Xo_122_, lean_object* v_Y_123_, lean_object* v_inst_124_, lean_object* v_00_u03c6_125_, lean_object* v_00_u03b5_126_, lean_object* v_g_127_, lean_object* v_k_128_){
_start:
{
lean_object* v_univ_129_; lean_object* v_t_130_; lean_object* v_G_131_; lean_object* v_PP_132_; lean_object* v_left_133_; lean_object* v_L_134_; lean_object* v___f_135_; 
v_univ_129_ = lean_ctor_get(v_Xo_122_, 2);
lean_inc_ref(v_univ_129_);
lean_dec_ref(v_Xo_122_);
v_t_130_ = lean_ctor_get(v_univ_129_, 0);
lean_inc_ref(v_t_130_);
lean_dec_ref(v_univ_129_);
v_G_131_ = lean_ctor_get(v_t_130_, 0);
lean_inc_ref(v_G_131_);
v_PP_132_ = lean_ctor_get(v_t_130_, 3);
lean_inc_ref(v_PP_132_);
lean_dec_ref(v_t_130_);
v_left_133_ = lean_ctor_get(v_G_131_, 0);
lean_inc(v_left_133_);
lean_dec_ref(v_G_131_);
v_L_134_ = lean_ctor_get(v_PP_132_, 0);
lean_inc_ref(v_L_134_);
lean_dec_ref(v_PP_132_);
v___f_135_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_genPow___redArg___lam__0), 9, 8);
lean_closure_set(v___f_135_, 0, v_Y_123_);
lean_closure_set(v___f_135_, 1, v_left_133_);
lean_closure_set(v___f_135_, 2, v_L_134_);
lean_closure_set(v___f_135_, 3, v_inst_124_);
lean_closure_set(v___f_135_, 4, v_00_u03c6_125_);
lean_closure_set(v___f_135_, 5, v_00_u03b5_126_);
lean_closure_set(v___f_135_, 6, v_g_127_);
lean_closure_set(v___f_135_, 7, v_k_128_);
return v___f_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow(lean_object* v_E_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_H_140_, lean_object* v_Dw_141_, lean_object* v_l_142_, lean_object* v_Xo_143_, lean_object* v_Y_144_, lean_object* v_K_145_, lean_object* v_inst_146_, lean_object* v_00_u03c6_147_, lean_object* v_00_u03b5_148_, lean_object* v_g_149_, lean_object* v_k_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lp_tree_Formalism_L2_Pj_genPow___redArg(v_Xo_143_, v_Y_144_, v_inst_146_, v_00_u03c6_147_, v_00_u03b5_148_, v_g_149_, v_k_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPow___boxed(lean_object* v_E_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_H_156_, lean_object* v_Dw_157_, lean_object* v_l_158_, lean_object* v_Xo_159_, lean_object* v_Y_160_, lean_object* v_K_161_, lean_object* v_inst_162_, lean_object* v_00_u03c6_163_, lean_object* v_00_u03b5_164_, lean_object* v_g_165_, lean_object* v_k_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lp_tree_Formalism_L2_Pj_genPow(v_E_152_, v_inst_153_, v_inst_154_, v_inst_155_, v_H_156_, v_Dw_157_, v_l_158_, v_Xo_159_, v_Y_160_, v_K_161_, v_inst_162_, v_00_u03c6_163_, v_00_u03b5_164_, v_g_165_, v_k_166_);
lean_dec_ref(v_l_158_);
lean_dec_ref(v_Dw_157_);
lean_dec_ref(v_H_156_);
lean_dec_ref(v_inst_153_);
return v_res_167_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
