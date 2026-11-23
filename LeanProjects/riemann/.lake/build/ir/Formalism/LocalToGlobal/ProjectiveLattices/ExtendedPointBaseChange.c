// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
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
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_withNorm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_withNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_withNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scalarsWithNorm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scalarsWithNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scalarsWithNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplusN___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplusN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplusN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___redArg___lam__0(lean_object* v_E_1_, lean_object* v_pt66_2_, lean_object* v_la_3_, lean_object* v___y_4_){
_start:
{
lean_object* v_extendedPointBaseChange_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_extendedPointBaseChange_5_ = lean_ctor_get(v_E_1_, 0);
lean_inc(v_extendedPointBaseChange_5_);
lean_dec_ref(v_E_1_);
v___x_6_ = lean_apply_1(v_pt66_2_, v_la_3_);
v___x_7_ = lean_apply_1(v_extendedPointBaseChange_5_, v_la_3_);
v___x_8_ = l_Sum_elim___redArg(v___x_6_, v___x_7_, v___y_4_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___redArg___lam__1(lean_object* v_E_9_, lean_object* v_vAt_10_, lean_object* v_la_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_vAt_x27_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_36__overap_17_; lean_object* v___x_18_; 
v_vAt_x27_14_ = lean_ctor_get(v_E_9_, 1);
lean_inc_ref(v_vAt_x27_14_);
lean_dec_ref(v_E_9_);
v___x_15_ = lean_apply_1(v_vAt_10_, v_la_11_);
v___x_16_ = lean_apply_1(v_vAt_x27_14_, v_la_11_);
v___x_36__overap_17_ = l_Sum_elim___redArg(v___x_15_, v___x_16_, v___y_12_);
v___x_18_ = lean_apply_1(v___x_36__overap_17_, v___y_13_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___redArg(lean_object* v_X_19_, lean_object* v_E_20_){
_start:
{
lean_object* v_rF_21_; lean_object* v_aF_22_; lean_object* v_aFO_23_; lean_object* v_inc_24_; lean_object* v_dat_25_; lean_object* v_pt66_26_; lean_object* v_vAt_27_; lean_object* v_thAll_28_; lean_object* v_shortTh_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_38_; 
v_rF_21_ = lean_ctor_get(v_X_19_, 0);
v_aF_22_ = lean_ctor_get(v_X_19_, 1);
v_aFO_23_ = lean_ctor_get(v_X_19_, 2);
v_inc_24_ = lean_ctor_get(v_X_19_, 3);
v_dat_25_ = lean_ctor_get(v_X_19_, 4);
v_pt66_26_ = lean_ctor_get(v_X_19_, 5);
v_vAt_27_ = lean_ctor_get(v_X_19_, 6);
v_thAll_28_ = lean_ctor_get(v_X_19_, 7);
v_shortTh_29_ = lean_ctor_get(v_X_19_, 8);
v_isSharedCheck_38_ = !lean_is_exclusive(v_X_19_);
if (v_isSharedCheck_38_ == 0)
{
v___x_31_ = v_X_19_;
v_isShared_32_ = v_isSharedCheck_38_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_shortTh_29_);
lean_inc(v_thAll_28_);
lean_inc(v_vAt_27_);
lean_inc(v_pt66_26_);
lean_inc(v_dat_25_);
lean_inc(v_inc_24_);
lean_inc(v_aFO_23_);
lean_inc(v_aF_22_);
lean_inc(v_rF_21_);
lean_dec(v_X_19_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_38_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_36_; 
lean_inc_ref(v_E_20_);
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_xplus___redArg___lam__0), 4, 2);
lean_closure_set(v___f_33_, 0, v_E_20_);
lean_closure_set(v___f_33_, 1, v_pt66_26_);
v___f_34_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_xplus___redArg___lam__1), 5, 2);
lean_closure_set(v___f_34_, 0, v_E_20_);
lean_closure_set(v___f_34_, 1, v_vAt_27_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 6, v___f_34_);
lean_ctor_set(v___x_31_, 5, v___f_33_);
v___x_36_ = v___x_31_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_rF_21_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_aF_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_aFO_23_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_inc_24_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_dat_25_);
lean_ctor_set(v_reuseFailAlloc_37_, 5, v___f_33_);
lean_ctor_set(v_reuseFailAlloc_37_, 6, v___f_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 7, v_thAll_28_);
lean_ctor_set(v_reuseFailAlloc_37_, 8, v_shortTh_29_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus(lean_object* v_D_39_, lean_object* v_B_40_, lean_object* v_P_41_, lean_object* v_j_42_, lean_object* v_X_43_, lean_object* v_E_44_, lean_object* v_hM_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_tree_Formalism_L2_Pj_xplus___redArg(v_X_43_, v_E_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplus___boxed(lean_object* v_D_47_, lean_object* v_B_48_, lean_object* v_P_49_, lean_object* v_j_50_, lean_object* v_X_51_, lean_object* v_E_52_, lean_object* v_hM_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_L2_Pj_xplus(v_D_47_, v_B_48_, v_P_49_, v_j_50_, v_X_51_, v_E_52_, v_hM_53_);
lean_dec(v_j_50_);
lean_dec_ref(v_P_49_);
lean_dec_ref(v_B_48_);
lean_dec_ref(v_D_47_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_withNorm___redArg(lean_object* v_B_55_, lean_object* v_N_56_){
_start:
{
lean_object* v_fKO_57_; lean_object* v_eO_58_; lean_object* v_acgC_59_; lean_object* v_modC_60_; lean_object* v_modOC_61_; lean_object* v_Mlat_62_; lean_object* v_supN_63_; lean_object* v_Xc_64_; lean_object* v_acgF_65_; lean_object* v_modF_66_; lean_object* v_sg_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v_fKO_57_ = lean_ctor_get(v_B_55_, 0);
v_eO_58_ = lean_ctor_get(v_B_55_, 1);
v_acgC_59_ = lean_ctor_get(v_B_55_, 2);
v_modC_60_ = lean_ctor_get(v_B_55_, 3);
v_modOC_61_ = lean_ctor_get(v_B_55_, 4);
v_Mlat_62_ = lean_ctor_get(v_B_55_, 5);
v_supN_63_ = lean_ctor_get(v_B_55_, 6);
v_Xc_64_ = lean_ctor_get(v_B_55_, 8);
v_acgF_65_ = lean_ctor_get(v_B_55_, 9);
v_modF_66_ = lean_ctor_get(v_B_55_, 10);
v_sg_67_ = lean_ctor_get(v_B_55_, 11);
v_isSharedCheck_74_ = !lean_is_exclusive(v_B_55_);
if (v_isSharedCheck_74_ == 0)
{
lean_object* v_unused_75_; 
v_unused_75_ = lean_ctor_get(v_B_55_, 7);
lean_dec(v_unused_75_);
v___x_69_ = v_B_55_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_sg_67_);
lean_inc(v_modF_66_);
lean_inc(v_acgF_65_);
lean_inc(v_Xc_64_);
lean_inc(v_supN_63_);
lean_inc(v_Mlat_62_);
lean_inc(v_modOC_61_);
lean_inc(v_modC_60_);
lean_inc(v_acgC_59_);
lean_inc(v_eO_58_);
lean_inc(v_fKO_57_);
lean_dec(v_B_55_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 7, v_N_56_);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_fKO_57_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_eO_58_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v_acgC_59_);
lean_ctor_set(v_reuseFailAlloc_73_, 3, v_modC_60_);
lean_ctor_set(v_reuseFailAlloc_73_, 4, v_modOC_61_);
lean_ctor_set(v_reuseFailAlloc_73_, 5, v_Mlat_62_);
lean_ctor_set(v_reuseFailAlloc_73_, 6, v_supN_63_);
lean_ctor_set(v_reuseFailAlloc_73_, 7, v_N_56_);
lean_ctor_set(v_reuseFailAlloc_73_, 8, v_Xc_64_);
lean_ctor_set(v_reuseFailAlloc_73_, 9, v_acgF_65_);
lean_ctor_set(v_reuseFailAlloc_73_, 10, v_modF_66_);
lean_ctor_set(v_reuseFailAlloc_73_, 11, v_sg_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_withNorm(lean_object* v_D_76_, lean_object* v_B_77_, lean_object* v_N_78_, lean_object* v_h0_79_, lean_object* v_h1_80_, lean_object* v_h2_81_, lean_object* v_h3_82_, lean_object* v_h4_83_){
_start:
{
lean_object* v_fKO_84_; lean_object* v_eO_85_; lean_object* v_acgC_86_; lean_object* v_modC_87_; lean_object* v_modOC_88_; lean_object* v_Mlat_89_; lean_object* v_supN_90_; lean_object* v_Xc_91_; lean_object* v_acgF_92_; lean_object* v_modF_93_; lean_object* v_sg_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
v_fKO_84_ = lean_ctor_get(v_B_77_, 0);
v_eO_85_ = lean_ctor_get(v_B_77_, 1);
v_acgC_86_ = lean_ctor_get(v_B_77_, 2);
v_modC_87_ = lean_ctor_get(v_B_77_, 3);
v_modOC_88_ = lean_ctor_get(v_B_77_, 4);
v_Mlat_89_ = lean_ctor_get(v_B_77_, 5);
v_supN_90_ = lean_ctor_get(v_B_77_, 6);
v_Xc_91_ = lean_ctor_get(v_B_77_, 8);
v_acgF_92_ = lean_ctor_get(v_B_77_, 9);
v_modF_93_ = lean_ctor_get(v_B_77_, 10);
v_sg_94_ = lean_ctor_get(v_B_77_, 11);
v_isSharedCheck_101_ = !lean_is_exclusive(v_B_77_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; 
v_unused_102_ = lean_ctor_get(v_B_77_, 7);
lean_dec(v_unused_102_);
v___x_96_ = v_B_77_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_sg_94_);
lean_inc(v_modF_93_);
lean_inc(v_acgF_92_);
lean_inc(v_Xc_91_);
lean_inc(v_supN_90_);
lean_inc(v_Mlat_89_);
lean_inc(v_modOC_88_);
lean_inc(v_modC_87_);
lean_inc(v_acgC_86_);
lean_inc(v_eO_85_);
lean_inc(v_fKO_84_);
lean_dec(v_B_77_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 7, v_N_78_);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_fKO_84_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_eO_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_acgC_86_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_modC_87_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v_modOC_88_);
lean_ctor_set(v_reuseFailAlloc_100_, 5, v_Mlat_89_);
lean_ctor_set(v_reuseFailAlloc_100_, 6, v_supN_90_);
lean_ctor_set(v_reuseFailAlloc_100_, 7, v_N_78_);
lean_ctor_set(v_reuseFailAlloc_100_, 8, v_Xc_91_);
lean_ctor_set(v_reuseFailAlloc_100_, 9, v_acgF_92_);
lean_ctor_set(v_reuseFailAlloc_100_, 10, v_modF_93_);
lean_ctor_set(v_reuseFailAlloc_100_, 11, v_sg_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_withNorm___boxed(lean_object* v_D_103_, lean_object* v_B_104_, lean_object* v_N_105_, lean_object* v_h0_106_, lean_object* v_h1_107_, lean_object* v_h2_108_, lean_object* v_h3_109_, lean_object* v_h4_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_tree_Formalism_L2_Pj_withNorm(v_D_103_, v_B_104_, v_N_105_, v_h0_106_, v_h1_107_, v_h2_108_, v_h3_109_, v_h4_110_);
lean_dec_ref(v_D_103_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt___redArg(lean_object* v_X_112_){
_start:
{
lean_object* v_rF_113_; lean_object* v_aF_114_; lean_object* v_aFO_115_; lean_object* v_inc_116_; lean_object* v_dat_117_; lean_object* v_pt66_118_; lean_object* v_vAt_119_; lean_object* v_thAll_120_; lean_object* v_shortTh_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_rF_113_ = lean_ctor_get(v_X_112_, 0);
v_aF_114_ = lean_ctor_get(v_X_112_, 1);
v_aFO_115_ = lean_ctor_get(v_X_112_, 2);
v_inc_116_ = lean_ctor_get(v_X_112_, 3);
v_dat_117_ = lean_ctor_get(v_X_112_, 4);
v_pt66_118_ = lean_ctor_get(v_X_112_, 5);
v_vAt_119_ = lean_ctor_get(v_X_112_, 6);
v_thAll_120_ = lean_ctor_get(v_X_112_, 7);
v_shortTh_121_ = lean_ctor_get(v_X_112_, 8);
v_isSharedCheck_128_ = !lean_is_exclusive(v_X_112_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v_X_112_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_shortTh_121_);
lean_inc(v_thAll_120_);
lean_inc(v_vAt_119_);
lean_inc(v_pt66_118_);
lean_inc(v_dat_117_);
lean_inc(v_inc_116_);
lean_inc(v_aFO_115_);
lean_inc(v_aF_114_);
lean_inc(v_rF_113_);
lean_dec(v_X_112_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_rF_113_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_aF_114_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_aFO_115_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_inc_116_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_dat_117_);
lean_ctor_set(v_reuseFailAlloc_127_, 5, v_pt66_118_);
lean_ctor_set(v_reuseFailAlloc_127_, 6, v_vAt_119_);
lean_ctor_set(v_reuseFailAlloc_127_, 7, v_thAll_120_);
lean_ctor_set(v_reuseFailAlloc_127_, 8, v_shortTh_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt(lean_object* v_D_129_, lean_object* v_B_130_, lean_object* v_P_131_, lean_object* v_j_132_, lean_object* v_N_133_, lean_object* v_h0_134_, lean_object* v_h1_135_, lean_object* v_h2_136_, lean_object* v_h3_137_, lean_object* v_h4_138_, lean_object* v_X_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt___redArg(v_X_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt___boxed(lean_object* v_D_141_, lean_object* v_B_142_, lean_object* v_P_143_, lean_object* v_j_144_, lean_object* v_N_145_, lean_object* v_h0_146_, lean_object* v_h1_147_, lean_object* v_h2_148_, lean_object* v_h3_149_, lean_object* v_h4_150_, lean_object* v_X_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt(v_D_141_, v_B_142_, v_P_143_, v_j_144_, v_N_145_, v_h0_146_, v_h1_147_, v_h2_148_, v_h3_149_, v_h4_150_, v_X_151_);
lean_dec(v_N_145_);
lean_dec(v_j_144_);
lean_dec_ref(v_P_143_);
lean_dec_ref(v_B_142_);
lean_dec_ref(v_D_141_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scalarsWithNorm___redArg(lean_object* v_S_153_){
_start:
{
lean_object* v_sW_154_; lean_object* v_sF_155_; lean_object* v_s0_156_; lean_object* v_sK_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_sW_154_ = lean_ctor_get(v_S_153_, 0);
v_sF_155_ = lean_ctor_get(v_S_153_, 1);
v_s0_156_ = lean_ctor_get(v_S_153_, 2);
v_sK_157_ = lean_ctor_get(v_S_153_, 3);
v_isSharedCheck_164_ = !lean_is_exclusive(v_S_153_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v_S_153_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_sK_157_);
lean_inc(v_s0_156_);
lean_inc(v_sF_155_);
lean_inc(v_sW_154_);
lean_dec(v_S_153_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_sW_154_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_sF_155_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v_s0_156_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v_sK_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scalarsWithNorm(lean_object* v_D_165_, lean_object* v_B_166_, lean_object* v_N_167_, lean_object* v_h0_168_, lean_object* v_h1_169_, lean_object* v_h2_170_, lean_object* v_h3_171_, lean_object* v_h4_172_, lean_object* v_S_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lp_tree_Formalism_L2_Pj_scalarsWithNorm___redArg(v_S_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scalarsWithNorm___boxed(lean_object* v_D_175_, lean_object* v_B_176_, lean_object* v_N_177_, lean_object* v_h0_178_, lean_object* v_h1_179_, lean_object* v_h2_180_, lean_object* v_h3_181_, lean_object* v_h4_182_, lean_object* v_S_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = lp_tree_Formalism_L2_Pj_scalarsWithNorm(v_D_175_, v_B_176_, v_N_177_, v_h0_178_, v_h1_179_, v_h2_180_, v_h3_181_, v_h4_182_, v_S_183_);
lean_dec(v_N_177_);
lean_dec_ref(v_B_176_);
lean_dec_ref(v_D_175_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplusN___redArg(lean_object* v_X_185_, lean_object* v_E_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lp_tree_Formalism_L2_Pj_xplus___redArg(v_X_185_, v_E_186_);
v___x_188_ = lp_tree_Formalism_L2_Pj_PJ_tol2NormAlt___redArg(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplusN(lean_object* v_D_189_, lean_object* v_B_190_, lean_object* v_P_191_, lean_object* v_j_192_, lean_object* v_N_193_, lean_object* v_h0_194_, lean_object* v_h1_195_, lean_object* v_h2_196_, lean_object* v_h3_197_, lean_object* v_h4_198_, lean_object* v_X_199_, lean_object* v_E_200_, lean_object* v_hM_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lp_tree_Formalism_L2_Pj_xplusN___redArg(v_X_199_, v_E_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_xplusN___boxed(lean_object* v_D_203_, lean_object* v_B_204_, lean_object* v_P_205_, lean_object* v_j_206_, lean_object* v_N_207_, lean_object* v_h0_208_, lean_object* v_h1_209_, lean_object* v_h2_210_, lean_object* v_h3_211_, lean_object* v_h4_212_, lean_object* v_X_213_, lean_object* v_E_214_, lean_object* v_hM_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_tree_Formalism_L2_Pj_xplusN(v_D_203_, v_B_204_, v_P_205_, v_j_206_, v_N_207_, v_h0_208_, v_h1_209_, v_h2_210_, v_h3_211_, v_h4_212_, v_X_213_, v_E_214_, v_hM_215_);
lean_dec(v_N_207_);
lean_dec(v_j_206_);
lean_dec_ref(v_P_205_);
lean_dec_ref(v_B_204_);
lean_dec_ref(v_D_203_);
return v_res_216_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ExtendedPointBaseChange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
