// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG___redArg___lam__0(lean_object* v_Y_1_, lean_object* v___x_2_, lean_object* v_u_3_, lean_object* v_g_4_, lean_object* v_j_5_){
_start:
{
lean_object* v_presheaf_6_; lean_object* v_obj_7_; lean_object* v_U_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toSemiring_11_; lean_object* v_toMonoid_12_; lean_object* v___x_13_; lean_object* v_toMul_14_; lean_object* v___x_15_; lean_object* v___x_174__overap_16_; lean_object* v___x_17_; lean_object* v_val_18_; lean_object* v_inv_19_; lean_object* v___x_20_; lean_object* v_val_21_; lean_object* v_inv_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_31_; 
v_presheaf_6_ = lean_ctor_get(v_Y_1_, 1);
v_obj_7_ = lean_ctor_get(v_presheaf_6_, 0);
v_U_8_ = lean_ctor_get(v___x_2_, 0);
lean_inc_ref(v_U_8_);
lean_dec_ref(v___x_2_);
lean_inc(v_j_5_);
v___x_9_ = lean_apply_1(v_U_8_, v_j_5_);
lean_inc(v_obj_7_);
v___x_10_ = lean_apply_1(v_obj_7_, v___x_9_);
v_toSemiring_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_ref(v_toSemiring_11_);
lean_dec_ref(v___x_10_);
v_toMonoid_12_ = lean_ctor_get(v_toSemiring_11_, 1);
lean_inc_ref(v_toMonoid_12_);
lean_dec_ref(v_toSemiring_11_);
v___x_13_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_12_);
lean_dec_ref(v_toMonoid_12_);
v_toMul_14_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_toMul_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lean_box(0);
v___x_174__overap_16_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(v_Y_1_, v___x_15_, v___x_9_);
v___x_17_ = lean_apply_1(v___x_174__overap_16_, v_u_3_);
v_val_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_val_18_);
v_inv_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_inv_19_);
lean_dec_ref(v___x_17_);
v___x_20_ = lean_apply_1(v_g_4_, v_j_5_);
v_val_21_ = lean_ctor_get(v___x_20_, 0);
v_inv_22_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_31_ == 0)
{
v___x_24_ = v___x_20_;
v_isShared_25_ = v_isSharedCheck_31_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_inv_22_);
lean_inc(v_val_21_);
lean_dec(v___x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_31_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
lean_inc(v_toMul_14_);
v___x_26_ = lean_apply_2(v_toMul_14_, v_val_18_, v_val_21_);
v___x_27_ = lean_apply_2(v_toMul_14_, v_inv_22_, v_inv_19_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v___x_27_);
lean_ctor_set(v___x_24_, 0, v___x_26_);
v___x_29_ = v___x_24_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG___redArg(lean_object* v_t_32_, lean_object* v_Y_33_, lean_object* v_inst_34_, lean_object* v_00_u03c6_35_, lean_object* v_00_u03b5_36_, lean_object* v_u_37_, lean_object* v_g_38_){
_start:
{
lean_object* v_G_39_; lean_object* v_PP_40_; lean_object* v_left_41_; lean_object* v_L_42_; lean_object* v___x_43_; lean_object* v___f_44_; 
v_G_39_ = lean_ctor_get(v_t_32_, 0);
lean_inc_ref(v_G_39_);
v_PP_40_ = lean_ctor_get(v_t_32_, 3);
lean_inc_ref(v_PP_40_);
lean_dec_ref(v_t_32_);
v_left_41_ = lean_ctor_get(v_G_39_, 0);
lean_inc(v_left_41_);
lean_dec_ref(v_G_39_);
v_L_42_ = lean_ctor_get(v_PP_40_, 0);
lean_inc_ref(v_L_42_);
lean_dec_ref(v_PP_40_);
lean_inc_ref(v_Y_33_);
v___x_43_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_left_41_, v_Y_33_, v_L_42_, v_inst_34_, v_00_u03c6_35_, v_00_u03b5_36_);
v___f_44_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_scaleGenG___redArg___lam__0), 5, 4);
lean_closure_set(v___f_44_, 0, v_Y_33_);
lean_closure_set(v___f_44_, 1, v___x_43_);
lean_closure_set(v___f_44_, 2, v_u_37_);
lean_closure_set(v___f_44_, 3, v_g_38_);
return v___f_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG(lean_object* v_E_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_H_49_, lean_object* v_X0_50_, lean_object* v_t_51_, lean_object* v_Y_52_, lean_object* v_K_53_, lean_object* v_inst_54_, lean_object* v_00_u03c6_55_, lean_object* v_00_u03b5_56_, lean_object* v_u_57_, lean_object* v_g_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_L2_Pj_scaleGenG___redArg(v_t_51_, v_Y_52_, v_inst_54_, v_00_u03c6_55_, v_00_u03b5_56_, v_u_57_, v_g_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_scaleGenG___boxed(lean_object* v_E_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_H_64_, lean_object* v_X0_65_, lean_object* v_t_66_, lean_object* v_Y_67_, lean_object* v_K_68_, lean_object* v_inst_69_, lean_object* v_00_u03c6_70_, lean_object* v_00_u03b5_71_, lean_object* v_u_72_, lean_object* v_g_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_L2_Pj_scaleGenG(v_E_60_, v_inst_61_, v_inst_62_, v_inst_63_, v_H_64_, v_X0_65_, v_t_66_, v_Y_67_, v_K_68_, v_inst_69_, v_00_u03c6_70_, v_00_u03b5_71_, v_u_72_, v_g_73_);
lean_dec_ref(v_X0_65_);
lean_dec_ref(v_H_64_);
lean_dec_ref(v_inst_61_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG___redArg___lam__0(lean_object* v_Y_75_, lean_object* v_left_76_, lean_object* v_L_77_, lean_object* v_inst_78_, lean_object* v_00_u03c6_79_, lean_object* v_00_u03b5_80_, lean_object* v_g_81_, lean_object* v_k_82_, lean_object* v_j_83_){
_start:
{
lean_object* v_presheaf_84_; lean_object* v_obj_85_; lean_object* v___x_86_; lean_object* v_U_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_toSemiring_90_; lean_object* v_toMonoid_91_; lean_object* v_toNPow_92_; lean_object* v___x_93_; lean_object* v_val_94_; lean_object* v_inv_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_104_; 
v_presheaf_84_ = lean_ctor_get(v_Y_75_, 1);
v_obj_85_ = lean_ctor_get(v_presheaf_84_, 0);
lean_inc(v_obj_85_);
v___x_86_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_left_76_, v_Y_75_, v_L_77_, v_inst_78_, v_00_u03c6_79_, v_00_u03b5_80_);
v_U_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref(v_U_87_);
lean_dec_ref(v___x_86_);
lean_inc(v_j_83_);
v___x_88_ = lean_apply_1(v_U_87_, v_j_83_);
v___x_89_ = lean_apply_1(v_obj_85_, v___x_88_);
v_toSemiring_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_toSemiring_90_);
lean_dec_ref(v___x_89_);
v_toMonoid_91_ = lean_ctor_get(v_toSemiring_90_, 1);
lean_inc_ref(v_toMonoid_91_);
lean_dec_ref(v_toSemiring_90_);
v_toNPow_92_ = lean_ctor_get(v_toMonoid_91_, 2);
lean_inc(v_toNPow_92_);
lean_dec_ref(v_toMonoid_91_);
v___x_93_ = lean_apply_1(v_g_81_, v_j_83_);
v_val_94_ = lean_ctor_get(v___x_93_, 0);
v_inv_95_ = lean_ctor_get(v___x_93_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_104_ == 0)
{
v___x_97_ = v___x_93_;
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_inv_95_);
lean_inc(v_val_94_);
lean_dec(v___x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
lean_inc(v_toNPow_92_);
lean_inc(v_k_82_);
v___x_99_ = lean_apply_2(v_toNPow_92_, v_k_82_, v_val_94_);
v___x_100_ = lean_apply_2(v_toNPow_92_, v_k_82_, v_inv_95_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_100_);
lean_ctor_set(v___x_97_, 0, v___x_99_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG___redArg(lean_object* v_t_105_, lean_object* v_Y_106_, lean_object* v_inst_107_, lean_object* v_00_u03c6_108_, lean_object* v_00_u03b5_109_, lean_object* v_g_110_, lean_object* v_k_111_){
_start:
{
lean_object* v_G_112_; lean_object* v_PP_113_; lean_object* v_left_114_; lean_object* v_L_115_; lean_object* v___f_116_; 
v_G_112_ = lean_ctor_get(v_t_105_, 0);
lean_inc_ref(v_G_112_);
v_PP_113_ = lean_ctor_get(v_t_105_, 3);
lean_inc_ref(v_PP_113_);
lean_dec_ref(v_t_105_);
v_left_114_ = lean_ctor_get(v_G_112_, 0);
lean_inc(v_left_114_);
lean_dec_ref(v_G_112_);
v_L_115_ = lean_ctor_get(v_PP_113_, 0);
lean_inc_ref(v_L_115_);
lean_dec_ref(v_PP_113_);
v___f_116_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_genPowG___redArg___lam__0), 9, 8);
lean_closure_set(v___f_116_, 0, v_Y_106_);
lean_closure_set(v___f_116_, 1, v_left_114_);
lean_closure_set(v___f_116_, 2, v_L_115_);
lean_closure_set(v___f_116_, 3, v_inst_107_);
lean_closure_set(v___f_116_, 4, v_00_u03c6_108_);
lean_closure_set(v___f_116_, 5, v_00_u03b5_109_);
lean_closure_set(v___f_116_, 6, v_g_110_);
lean_closure_set(v___f_116_, 7, v_k_111_);
return v___f_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG(lean_object* v_E_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_H_121_, lean_object* v_X0_122_, lean_object* v_t_123_, lean_object* v_Y_124_, lean_object* v_K_125_, lean_object* v_inst_126_, lean_object* v_00_u03c6_127_, lean_object* v_00_u03b5_128_, lean_object* v_g_129_, lean_object* v_k_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lp_tree_Formalism_L2_Pj_genPowG___redArg(v_t_123_, v_Y_124_, v_inst_126_, v_00_u03c6_127_, v_00_u03b5_128_, v_g_129_, v_k_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_genPowG___boxed(lean_object* v_E_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_H_136_, lean_object* v_X0_137_, lean_object* v_t_138_, lean_object* v_Y_139_, lean_object* v_K_140_, lean_object* v_inst_141_, lean_object* v_00_u03c6_142_, lean_object* v_00_u03b5_143_, lean_object* v_g_144_, lean_object* v_k_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_tree_Formalism_L2_Pj_genPowG(v_E_132_, v_inst_133_, v_inst_134_, v_inst_135_, v_H_136_, v_X0_137_, v_t_138_, v_Y_139_, v_K_140_, v_inst_141_, v_00_u03c6_142_, v_00_u03b5_143_, v_g_144_, v_k_145_);
lean_dec_ref(v_X0_137_);
lean_dec_ref(v_H_136_);
lean_dec_ref(v_inst_133_);
return v_res_146_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
