// Lean compiler output
// Module: Formalism.SizeWindowBrackets.SBrDiv
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic public import Formalism.LogFactorialIndices.StatementSize public import Formalism.HarderNarasimhan.QuotRealize
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_D5_topPl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_D5_topPl, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb___closed__0 = (const lean_object*)&lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV___redArg(lean_object* v_D_1_, lean_object* v_v_2_){
_start:
{
lean_object* v_x_3_; lean_object* v_00_u03b5_4_; lean_object* v_a_5_; lean_object* v_b_6_; lean_object* v_b_x27_7_; lean_object* v_k_8_; lean_object* v_L_9_; lean_object* v_La_10_; lean_object* v_B0_11_; lean_object* v_Nc_12_; lean_object* v_gam_13_; lean_object* v_LpL_14_; lean_object* v_lg_15_; lean_object* v_logGam_16_; lean_object* v_aT_17_; lean_object* v_w_18_; lean_object* v_d_19_; lean_object* v_T_20_; lean_object* v_muN_21_; lean_object* v_muMaxN_22_; lean_object* v_h_23_; lean_object* v_muM_24_; lean_object* v_muMaxM_25_; lean_object* v_EeJ_26_; lean_object* v_muCC_27_; lean_object* v_muMinCC_28_; lean_object* v_Fo_29_; lean_object* v_Ga_30_; lean_object* v_Ta_31_; lean_object* v_ASK_32_; lean_object* v_IO_33_; lean_object* v_HH_34_; lean_object* v_del_35_; lean_object* v_00_u03b7_36_; lean_object* v_e_37_; lean_object* v_delBar_38_; lean_object* v_etaBar_39_; lean_object* v_eBar_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_x_3_ = lean_ctor_get(v_D_1_, 0);
v_00_u03b5_4_ = lean_ctor_get(v_D_1_, 1);
v_a_5_ = lean_ctor_get(v_D_1_, 2);
v_b_6_ = lean_ctor_get(v_D_1_, 3);
v_b_x27_7_ = lean_ctor_get(v_D_1_, 4);
v_k_8_ = lean_ctor_get(v_D_1_, 5);
v_L_9_ = lean_ctor_get(v_D_1_, 6);
v_La_10_ = lean_ctor_get(v_D_1_, 7);
v_B0_11_ = lean_ctor_get(v_D_1_, 8);
v_Nc_12_ = lean_ctor_get(v_D_1_, 9);
v_gam_13_ = lean_ctor_get(v_D_1_, 10);
v_LpL_14_ = lean_ctor_get(v_D_1_, 11);
v_lg_15_ = lean_ctor_get(v_D_1_, 13);
v_logGam_16_ = lean_ctor_get(v_D_1_, 14);
v_aT_17_ = lean_ctor_get(v_D_1_, 15);
v_w_18_ = lean_ctor_get(v_D_1_, 16);
v_d_19_ = lean_ctor_get(v_D_1_, 17);
v_T_20_ = lean_ctor_get(v_D_1_, 18);
v_muN_21_ = lean_ctor_get(v_D_1_, 19);
v_muMaxN_22_ = lean_ctor_get(v_D_1_, 20);
v_h_23_ = lean_ctor_get(v_D_1_, 21);
v_muM_24_ = lean_ctor_get(v_D_1_, 22);
v_muMaxM_25_ = lean_ctor_get(v_D_1_, 23);
v_EeJ_26_ = lean_ctor_get(v_D_1_, 24);
v_muCC_27_ = lean_ctor_get(v_D_1_, 25);
v_muMinCC_28_ = lean_ctor_get(v_D_1_, 26);
v_Fo_29_ = lean_ctor_get(v_D_1_, 27);
v_Ga_30_ = lean_ctor_get(v_D_1_, 28);
v_Ta_31_ = lean_ctor_get(v_D_1_, 29);
v_ASK_32_ = lean_ctor_get(v_D_1_, 30);
v_IO_33_ = lean_ctor_get(v_D_1_, 31);
v_HH_34_ = lean_ctor_get(v_D_1_, 32);
v_del_35_ = lean_ctor_get(v_D_1_, 33);
v_00_u03b7_36_ = lean_ctor_get(v_D_1_, 34);
v_e_37_ = lean_ctor_get(v_D_1_, 35);
v_delBar_38_ = lean_ctor_get(v_D_1_, 36);
v_etaBar_39_ = lean_ctor_get(v_D_1_, 37);
v_eBar_40_ = lean_ctor_get(v_D_1_, 38);
v_isSharedCheck_47_ = !lean_is_exclusive(v_D_1_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v_D_1_, 12);
lean_dec(v_unused_48_);
v___x_42_ = v_D_1_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_eBar_40_);
lean_inc(v_etaBar_39_);
lean_inc(v_delBar_38_);
lean_inc(v_e_37_);
lean_inc(v_00_u03b7_36_);
lean_inc(v_del_35_);
lean_inc(v_HH_34_);
lean_inc(v_IO_33_);
lean_inc(v_ASK_32_);
lean_inc(v_Ta_31_);
lean_inc(v_Ga_30_);
lean_inc(v_Fo_29_);
lean_inc(v_muMinCC_28_);
lean_inc(v_muCC_27_);
lean_inc(v_EeJ_26_);
lean_inc(v_muMaxM_25_);
lean_inc(v_muM_24_);
lean_inc(v_h_23_);
lean_inc(v_muMaxN_22_);
lean_inc(v_muN_21_);
lean_inc(v_T_20_);
lean_inc(v_d_19_);
lean_inc(v_w_18_);
lean_inc(v_aT_17_);
lean_inc(v_logGam_16_);
lean_inc(v_lg_15_);
lean_inc(v_LpL_14_);
lean_inc(v_gam_13_);
lean_inc(v_Nc_12_);
lean_inc(v_B0_11_);
lean_inc(v_La_10_);
lean_inc(v_L_9_);
lean_inc(v_k_8_);
lean_inc(v_b_x27_7_);
lean_inc(v_b_6_);
lean_inc(v_a_5_);
lean_inc(v_00_u03b5_4_);
lean_inc(v_x_3_);
lean_dec(v_D_1_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 12, v_v_2_);
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 39, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_x_3_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_00_u03b5_4_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v_a_5_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v_b_6_);
lean_ctor_set(v_reuseFailAlloc_46_, 4, v_b_x27_7_);
lean_ctor_set(v_reuseFailAlloc_46_, 5, v_k_8_);
lean_ctor_set(v_reuseFailAlloc_46_, 6, v_L_9_);
lean_ctor_set(v_reuseFailAlloc_46_, 7, v_La_10_);
lean_ctor_set(v_reuseFailAlloc_46_, 8, v_B0_11_);
lean_ctor_set(v_reuseFailAlloc_46_, 9, v_Nc_12_);
lean_ctor_set(v_reuseFailAlloc_46_, 10, v_gam_13_);
lean_ctor_set(v_reuseFailAlloc_46_, 11, v_LpL_14_);
lean_ctor_set(v_reuseFailAlloc_46_, 12, v_v_2_);
lean_ctor_set(v_reuseFailAlloc_46_, 13, v_lg_15_);
lean_ctor_set(v_reuseFailAlloc_46_, 14, v_logGam_16_);
lean_ctor_set(v_reuseFailAlloc_46_, 15, v_aT_17_);
lean_ctor_set(v_reuseFailAlloc_46_, 16, v_w_18_);
lean_ctor_set(v_reuseFailAlloc_46_, 17, v_d_19_);
lean_ctor_set(v_reuseFailAlloc_46_, 18, v_T_20_);
lean_ctor_set(v_reuseFailAlloc_46_, 19, v_muN_21_);
lean_ctor_set(v_reuseFailAlloc_46_, 20, v_muMaxN_22_);
lean_ctor_set(v_reuseFailAlloc_46_, 21, v_h_23_);
lean_ctor_set(v_reuseFailAlloc_46_, 22, v_muM_24_);
lean_ctor_set(v_reuseFailAlloc_46_, 23, v_muMaxM_25_);
lean_ctor_set(v_reuseFailAlloc_46_, 24, v_EeJ_26_);
lean_ctor_set(v_reuseFailAlloc_46_, 25, v_muCC_27_);
lean_ctor_set(v_reuseFailAlloc_46_, 26, v_muMinCC_28_);
lean_ctor_set(v_reuseFailAlloc_46_, 27, v_Fo_29_);
lean_ctor_set(v_reuseFailAlloc_46_, 28, v_Ga_30_);
lean_ctor_set(v_reuseFailAlloc_46_, 29, v_Ta_31_);
lean_ctor_set(v_reuseFailAlloc_46_, 30, v_ASK_32_);
lean_ctor_set(v_reuseFailAlloc_46_, 31, v_IO_33_);
lean_ctor_set(v_reuseFailAlloc_46_, 32, v_HH_34_);
lean_ctor_set(v_reuseFailAlloc_46_, 33, v_del_35_);
lean_ctor_set(v_reuseFailAlloc_46_, 34, v_00_u03b7_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 35, v_e_37_);
lean_ctor_set(v_reuseFailAlloc_46_, 36, v_delBar_38_);
lean_ctor_set(v_reuseFailAlloc_46_, 37, v_etaBar_39_);
lean_ctor_set(v_reuseFailAlloc_46_, 38, v_eBar_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV(lean_object* v_U0_49_, lean_object* v_W_50_, lean_object* v_Top_51_, lean_object* v_m_52_, lean_object* v_f_53_, lean_object* v_D_54_, lean_object* v_v_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV___redArg(v_D_54_, v_v_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV___boxed(lean_object* v_U0_57_, lean_object* v_W_58_, lean_object* v_Top_59_, lean_object* v_m_60_, lean_object* v_f_61_, lean_object* v_D_62_, lean_object* v_v_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_Formalism_LFunctionChainParameters_LBrDiv_withV(v_U0_57_, v_W_58_, v_Top_59_, v_m_60_, v_f_61_, v_D_62_, v_v_63_);
lean_dec(v_f_61_);
lean_dec(v_m_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__0(lean_object* v_h_65_, lean_object* v_c_66_, lean_object* v_u0_67_, lean_object* v_u_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; 
lean_inc(v_u0_67_);
v___x_69_ = lean_apply_2(v_h_65_, v_u0_67_, v_u_68_);
v___x_70_ = lean_apply_1(v_c_66_, v_u0_67_);
v___f_71_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_71_, 0, v___x_70_);
v___f_72_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_72_, 0, v___x_69_);
lean_closure_set(v___f_72_, 1, v___f_71_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__1(lean_object* v_muCC_73_, lean_object* v_c_74_, lean_object* v_u0_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___f_78_; 
lean_inc(v_u0_75_);
v___x_76_ = lean_apply_1(v_muCC_73_, v_u0_75_);
v___x_77_ = lean_apply_1(v_c_74_, v_u0_75_);
v___f_78_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_78_, 0, v___x_76_);
lean_closure_set(v___f_78_, 1, v___x_77_);
return v___f_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__2(lean_object* v_muMinCC_79_, lean_object* v_c_80_, lean_object* v_u0_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; 
lean_inc(v_u0_81_);
v___x_82_ = lean_apply_1(v_muMinCC_79_, v_u0_81_);
v___x_83_ = lean_apply_1(v_c_80_, v_u0_81_);
v___f_84_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_84_, 0, v___x_82_);
lean_closure_set(v___f_84_, 1, v___x_83_);
return v___f_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg(lean_object* v_D_85_, lean_object* v_c_86_){
_start:
{
lean_object* v_x_87_; lean_object* v_00_u03b5_88_; lean_object* v_a_89_; lean_object* v_b_90_; lean_object* v_b_x27_91_; lean_object* v_k_92_; lean_object* v_L_93_; lean_object* v_La_94_; lean_object* v_B0_95_; lean_object* v_Nc_96_; lean_object* v_gam_97_; lean_object* v_LpL_98_; lean_object* v_v_99_; lean_object* v_lg_100_; lean_object* v_logGam_101_; lean_object* v_aT_102_; lean_object* v_w_103_; lean_object* v_d_104_; lean_object* v_T_105_; lean_object* v_muN_106_; lean_object* v_muMaxN_107_; lean_object* v_h_108_; lean_object* v_muM_109_; lean_object* v_muMaxM_110_; lean_object* v_EeJ_111_; lean_object* v_muCC_112_; lean_object* v_muMinCC_113_; lean_object* v_Fo_114_; lean_object* v_Ga_115_; lean_object* v_Ta_116_; lean_object* v_ASK_117_; lean_object* v_IO_118_; lean_object* v_HH_119_; lean_object* v_del_120_; lean_object* v_00_u03b7_121_; lean_object* v_e_122_; lean_object* v_delBar_123_; lean_object* v_etaBar_124_; lean_object* v_eBar_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_x_87_ = lean_ctor_get(v_D_85_, 0);
v_00_u03b5_88_ = lean_ctor_get(v_D_85_, 1);
v_a_89_ = lean_ctor_get(v_D_85_, 2);
v_b_90_ = lean_ctor_get(v_D_85_, 3);
v_b_x27_91_ = lean_ctor_get(v_D_85_, 4);
v_k_92_ = lean_ctor_get(v_D_85_, 5);
v_L_93_ = lean_ctor_get(v_D_85_, 6);
v_La_94_ = lean_ctor_get(v_D_85_, 7);
v_B0_95_ = lean_ctor_get(v_D_85_, 8);
v_Nc_96_ = lean_ctor_get(v_D_85_, 9);
v_gam_97_ = lean_ctor_get(v_D_85_, 10);
v_LpL_98_ = lean_ctor_get(v_D_85_, 11);
v_v_99_ = lean_ctor_get(v_D_85_, 12);
v_lg_100_ = lean_ctor_get(v_D_85_, 13);
v_logGam_101_ = lean_ctor_get(v_D_85_, 14);
v_aT_102_ = lean_ctor_get(v_D_85_, 15);
v_w_103_ = lean_ctor_get(v_D_85_, 16);
v_d_104_ = lean_ctor_get(v_D_85_, 17);
v_T_105_ = lean_ctor_get(v_D_85_, 18);
v_muN_106_ = lean_ctor_get(v_D_85_, 19);
v_muMaxN_107_ = lean_ctor_get(v_D_85_, 20);
v_h_108_ = lean_ctor_get(v_D_85_, 21);
v_muM_109_ = lean_ctor_get(v_D_85_, 22);
v_muMaxM_110_ = lean_ctor_get(v_D_85_, 23);
v_EeJ_111_ = lean_ctor_get(v_D_85_, 24);
v_muCC_112_ = lean_ctor_get(v_D_85_, 25);
v_muMinCC_113_ = lean_ctor_get(v_D_85_, 26);
v_Fo_114_ = lean_ctor_get(v_D_85_, 27);
v_Ga_115_ = lean_ctor_get(v_D_85_, 28);
v_Ta_116_ = lean_ctor_get(v_D_85_, 29);
v_ASK_117_ = lean_ctor_get(v_D_85_, 30);
v_IO_118_ = lean_ctor_get(v_D_85_, 31);
v_HH_119_ = lean_ctor_get(v_D_85_, 32);
v_del_120_ = lean_ctor_get(v_D_85_, 33);
v_00_u03b7_121_ = lean_ctor_get(v_D_85_, 34);
v_e_122_ = lean_ctor_get(v_D_85_, 35);
v_delBar_123_ = lean_ctor_get(v_D_85_, 36);
v_etaBar_124_ = lean_ctor_get(v_D_85_, 37);
v_eBar_125_ = lean_ctor_get(v_D_85_, 38);
v_isSharedCheck_135_ = !lean_is_exclusive(v_D_85_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v_D_85_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_eBar_125_);
lean_inc(v_etaBar_124_);
lean_inc(v_delBar_123_);
lean_inc(v_e_122_);
lean_inc(v_00_u03b7_121_);
lean_inc(v_del_120_);
lean_inc(v_HH_119_);
lean_inc(v_IO_118_);
lean_inc(v_ASK_117_);
lean_inc(v_Ta_116_);
lean_inc(v_Ga_115_);
lean_inc(v_Fo_114_);
lean_inc(v_muMinCC_113_);
lean_inc(v_muCC_112_);
lean_inc(v_EeJ_111_);
lean_inc(v_muMaxM_110_);
lean_inc(v_muM_109_);
lean_inc(v_h_108_);
lean_inc(v_muMaxN_107_);
lean_inc(v_muN_106_);
lean_inc(v_T_105_);
lean_inc(v_d_104_);
lean_inc(v_w_103_);
lean_inc(v_aT_102_);
lean_inc(v_logGam_101_);
lean_inc(v_lg_100_);
lean_inc(v_v_99_);
lean_inc(v_LpL_98_);
lean_inc(v_gam_97_);
lean_inc(v_Nc_96_);
lean_inc(v_B0_95_);
lean_inc(v_La_94_);
lean_inc(v_L_93_);
lean_inc(v_k_92_);
lean_inc(v_b_x27_91_);
lean_inc(v_b_90_);
lean_inc(v_a_89_);
lean_inc(v_00_u03b5_88_);
lean_inc(v_x_87_);
lean_dec(v_D_85_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___x_133_; 
lean_inc_n(v_c_86_, 2);
v___f_129_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__0), 4, 2);
lean_closure_set(v___f_129_, 0, v_h_108_);
lean_closure_set(v___f_129_, 1, v_c_86_);
v___f_130_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__1), 3, 2);
lean_closure_set(v___f_130_, 0, v_muCC_112_);
lean_closure_set(v___f_130_, 1, v_c_86_);
v___f_131_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg___lam__2), 3, 2);
lean_closure_set(v___f_131_, 0, v_muMinCC_113_);
lean_closure_set(v___f_131_, 1, v_c_86_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 26, v___f_131_);
lean_ctor_set(v___x_127_, 25, v___f_130_);
lean_ctor_set(v___x_127_, 21, v___f_129_);
v___x_133_ = v___x_127_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 39, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_x_87_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_00_u03b5_88_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_a_89_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_b_90_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_b_x27_91_);
lean_ctor_set(v_reuseFailAlloc_134_, 5, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_134_, 6, v_L_93_);
lean_ctor_set(v_reuseFailAlloc_134_, 7, v_La_94_);
lean_ctor_set(v_reuseFailAlloc_134_, 8, v_B0_95_);
lean_ctor_set(v_reuseFailAlloc_134_, 9, v_Nc_96_);
lean_ctor_set(v_reuseFailAlloc_134_, 10, v_gam_97_);
lean_ctor_set(v_reuseFailAlloc_134_, 11, v_LpL_98_);
lean_ctor_set(v_reuseFailAlloc_134_, 12, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_134_, 13, v_lg_100_);
lean_ctor_set(v_reuseFailAlloc_134_, 14, v_logGam_101_);
lean_ctor_set(v_reuseFailAlloc_134_, 15, v_aT_102_);
lean_ctor_set(v_reuseFailAlloc_134_, 16, v_w_103_);
lean_ctor_set(v_reuseFailAlloc_134_, 17, v_d_104_);
lean_ctor_set(v_reuseFailAlloc_134_, 18, v_T_105_);
lean_ctor_set(v_reuseFailAlloc_134_, 19, v_muN_106_);
lean_ctor_set(v_reuseFailAlloc_134_, 20, v_muMaxN_107_);
lean_ctor_set(v_reuseFailAlloc_134_, 21, v___f_129_);
lean_ctor_set(v_reuseFailAlloc_134_, 22, v_muM_109_);
lean_ctor_set(v_reuseFailAlloc_134_, 23, v_muMaxM_110_);
lean_ctor_set(v_reuseFailAlloc_134_, 24, v_EeJ_111_);
lean_ctor_set(v_reuseFailAlloc_134_, 25, v___f_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 26, v___f_131_);
lean_ctor_set(v_reuseFailAlloc_134_, 27, v_Fo_114_);
lean_ctor_set(v_reuseFailAlloc_134_, 28, v_Ga_115_);
lean_ctor_set(v_reuseFailAlloc_134_, 29, v_Ta_116_);
lean_ctor_set(v_reuseFailAlloc_134_, 30, v_ASK_117_);
lean_ctor_set(v_reuseFailAlloc_134_, 31, v_IO_118_);
lean_ctor_set(v_reuseFailAlloc_134_, 32, v_HH_119_);
lean_ctor_set(v_reuseFailAlloc_134_, 33, v_del_120_);
lean_ctor_set(v_reuseFailAlloc_134_, 34, v_00_u03b7_121_);
lean_ctor_set(v_reuseFailAlloc_134_, 35, v_e_122_);
lean_ctor_set(v_reuseFailAlloc_134_, 36, v_delBar_123_);
lean_ctor_set(v_reuseFailAlloc_134_, 37, v_etaBar_124_);
lean_ctor_set(v_reuseFailAlloc_134_, 38, v_eBar_125_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows(lean_object* v_U0_136_, lean_object* v_W_137_, lean_object* v_Top_138_, lean_object* v_m_139_, lean_object* v_f_140_, lean_object* v_D_141_, lean_object* v_c_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___redArg(v_D_141_, v_c_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows___boxed(lean_object* v_U0_144_, lean_object* v_W_145_, lean_object* v_Top_146_, lean_object* v_m_147_, lean_object* v_f_148_, lean_object* v_D_149_, lean_object* v_c_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = lp_tree_Formalism_LFunctionChainParameters_LBrDiv_shiftRows(v_U0_144_, v_W_145_, v_Top_146_, v_m_147_, v_f_148_, v_D_149_, v_c_150_);
lean_dec(v_f_148_);
lean_dec(v_m_147_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf___redArg(lean_object* v_w_152_){
_start:
{
return v_w_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf(lean_object* v_K_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_w_156_){
_start:
{
return v_w_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf___boxed(lean_object* v_K_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_w_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_tree_Formalism_LFunctionChainParameters_LBrDiv_plOf(v_K_157_, v_inst_158_, v_inst_159_, v_w_160_);
lean_dec_ref(v_inst_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb(lean_object* v_H_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb___closed__0));
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb___boxed(lean_object* v_H_166_, lean_object* v_inst_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_tree_Formalism_LFunctionChainParameters_LBrDiv_topEmb(v_H_166_, v_inst_167_);
lean_dec_ref(v_inst_167_);
return v_res_168_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogFactorialIndices_StatementSize(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_QuotRealize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_SBrDiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogFactorialIndices_StatementSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_QuotRealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
