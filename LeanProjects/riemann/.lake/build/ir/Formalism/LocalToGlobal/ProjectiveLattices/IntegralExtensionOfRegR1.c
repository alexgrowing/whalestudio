// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2Xplus___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2Xplus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2Xplus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2XplusN___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2XplusN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2XplusN___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2Xplus___redArg(lean_object* v_G_1_){
_start:
{
lean_object* v_N_2_; lean_object* v_w_3_; lean_object* v_del_4_; lean_object* v_th_x27_5_; lean_object* v_rz_6_; lean_object* v_alz_7_; lean_object* v_th0_8_; lean_object* v_zc_9_; lean_object* v_rq_10_; lean_object* v_th_11_; lean_object* v_iet_12_; lean_object* v_et_13_; lean_object* v_mx_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_N_2_ = lean_ctor_get(v_G_1_, 0);
v_w_3_ = lean_ctor_get(v_G_1_, 1);
v_del_4_ = lean_ctor_get(v_G_1_, 2);
v_th_x27_5_ = lean_ctor_get(v_G_1_, 3);
v_rz_6_ = lean_ctor_get(v_G_1_, 4);
v_alz_7_ = lean_ctor_get(v_G_1_, 5);
v_th0_8_ = lean_ctor_get(v_G_1_, 6);
v_zc_9_ = lean_ctor_get(v_G_1_, 7);
v_rq_10_ = lean_ctor_get(v_G_1_, 8);
v_th_11_ = lean_ctor_get(v_G_1_, 9);
v_iet_12_ = lean_ctor_get(v_G_1_, 10);
v_et_13_ = lean_ctor_get(v_G_1_, 11);
v_mx_14_ = lean_ctor_get(v_G_1_, 12);
v_isSharedCheck_21_ = !lean_is_exclusive(v_G_1_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v_G_1_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_mx_14_);
lean_inc(v_et_13_);
lean_inc(v_iet_12_);
lean_inc(v_th_11_);
lean_inc(v_rq_10_);
lean_inc(v_zc_9_);
lean_inc(v_th0_8_);
lean_inc(v_alz_7_);
lean_inc(v_rz_6_);
lean_inc(v_th_x27_5_);
lean_inc(v_del_4_);
lean_inc(v_w_3_);
lean_inc(v_N_2_);
lean_dec(v_G_1_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_N_2_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_w_3_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_del_4_);
lean_ctor_set(v_reuseFailAlloc_20_, 3, v_th_x27_5_);
lean_ctor_set(v_reuseFailAlloc_20_, 4, v_rz_6_);
lean_ctor_set(v_reuseFailAlloc_20_, 5, v_alz_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 6, v_th0_8_);
lean_ctor_set(v_reuseFailAlloc_20_, 7, v_zc_9_);
lean_ctor_set(v_reuseFailAlloc_20_, 8, v_rq_10_);
lean_ctor_set(v_reuseFailAlloc_20_, 9, v_th_11_);
lean_ctor_set(v_reuseFailAlloc_20_, 10, v_iet_12_);
lean_ctor_set(v_reuseFailAlloc_20_, 11, v_et_13_);
lean_ctor_set(v_reuseFailAlloc_20_, 12, v_mx_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2Xplus(lean_object* v_D_22_, lean_object* v_B_23_, lean_object* v_P_24_, lean_object* v_j_25_, lean_object* v_ka_26_, lean_object* v_wL_27_, lean_object* v_wF_28_, lean_object* v_X_29_, lean_object* v_G_30_, lean_object* v_E_31_, lean_object* v_hM_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_L2_Pj_gd2Xplus___redArg(v_G_30_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2Xplus___boxed(lean_object* v_D_34_, lean_object* v_B_35_, lean_object* v_P_36_, lean_object* v_j_37_, lean_object* v_ka_38_, lean_object* v_wL_39_, lean_object* v_wF_40_, lean_object* v_X_41_, lean_object* v_G_42_, lean_object* v_E_43_, lean_object* v_hM_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_L2_Pj_gd2Xplus(v_D_34_, v_B_35_, v_P_36_, v_j_37_, v_ka_38_, v_wL_39_, v_wF_40_, v_X_41_, v_G_42_, v_E_43_, v_hM_44_);
lean_dec_ref(v_E_43_);
lean_dec_ref(v_X_41_);
lean_dec_ref(v_wF_40_);
lean_dec_ref(v_wL_39_);
lean_dec_ref(v_ka_38_);
lean_dec(v_j_37_);
lean_dec_ref(v_P_36_);
lean_dec_ref(v_B_35_);
lean_dec_ref(v_D_34_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2XplusN___redArg(lean_object* v_G_46_){
_start:
{
lean_object* v_N_47_; lean_object* v_w_48_; lean_object* v_del_49_; lean_object* v_th_x27_50_; lean_object* v_rz_51_; lean_object* v_alz_52_; lean_object* v_th0_53_; lean_object* v_zc_54_; lean_object* v_rq_55_; lean_object* v_th_56_; lean_object* v_iet_57_; lean_object* v_et_58_; lean_object* v_mx_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_N_47_ = lean_ctor_get(v_G_46_, 0);
v_w_48_ = lean_ctor_get(v_G_46_, 1);
v_del_49_ = lean_ctor_get(v_G_46_, 2);
v_th_x27_50_ = lean_ctor_get(v_G_46_, 3);
v_rz_51_ = lean_ctor_get(v_G_46_, 4);
v_alz_52_ = lean_ctor_get(v_G_46_, 5);
v_th0_53_ = lean_ctor_get(v_G_46_, 6);
v_zc_54_ = lean_ctor_get(v_G_46_, 7);
v_rq_55_ = lean_ctor_get(v_G_46_, 8);
v_th_56_ = lean_ctor_get(v_G_46_, 9);
v_iet_57_ = lean_ctor_get(v_G_46_, 10);
v_et_58_ = lean_ctor_get(v_G_46_, 11);
v_mx_59_ = lean_ctor_get(v_G_46_, 12);
v_isSharedCheck_66_ = !lean_is_exclusive(v_G_46_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v_G_46_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_mx_59_);
lean_inc(v_et_58_);
lean_inc(v_iet_57_);
lean_inc(v_th_56_);
lean_inc(v_rq_55_);
lean_inc(v_zc_54_);
lean_inc(v_th0_53_);
lean_inc(v_alz_52_);
lean_inc(v_rz_51_);
lean_inc(v_th_x27_50_);
lean_inc(v_del_49_);
lean_inc(v_w_48_);
lean_inc(v_N_47_);
lean_dec(v_G_46_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_N_47_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_w_48_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v_del_49_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v_th_x27_50_);
lean_ctor_set(v_reuseFailAlloc_65_, 4, v_rz_51_);
lean_ctor_set(v_reuseFailAlloc_65_, 5, v_alz_52_);
lean_ctor_set(v_reuseFailAlloc_65_, 6, v_th0_53_);
lean_ctor_set(v_reuseFailAlloc_65_, 7, v_zc_54_);
lean_ctor_set(v_reuseFailAlloc_65_, 8, v_rq_55_);
lean_ctor_set(v_reuseFailAlloc_65_, 9, v_th_56_);
lean_ctor_set(v_reuseFailAlloc_65_, 10, v_iet_57_);
lean_ctor_set(v_reuseFailAlloc_65_, 11, v_et_58_);
lean_ctor_set(v_reuseFailAlloc_65_, 12, v_mx_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2XplusN(lean_object* v_D_67_, lean_object* v_B_68_, lean_object* v_P_69_, lean_object* v_j_70_, lean_object* v_N_71_, lean_object* v_h0_72_, lean_object* v_h1_73_, lean_object* v_h2_74_, lean_object* v_h3_75_, lean_object* v_h4_76_, lean_object* v_ka_77_, lean_object* v_wL_78_, lean_object* v_wF_79_, lean_object* v_X_80_, lean_object* v_G_81_, lean_object* v_E_82_, lean_object* v_hM_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_tree_Formalism_L2_Pj_gd2XplusN___redArg(v_G_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_gd2XplusN___boxed(lean_object** _args){
lean_object* v_D_85_ = _args[0];
lean_object* v_B_86_ = _args[1];
lean_object* v_P_87_ = _args[2];
lean_object* v_j_88_ = _args[3];
lean_object* v_N_89_ = _args[4];
lean_object* v_h0_90_ = _args[5];
lean_object* v_h1_91_ = _args[6];
lean_object* v_h2_92_ = _args[7];
lean_object* v_h3_93_ = _args[8];
lean_object* v_h4_94_ = _args[9];
lean_object* v_ka_95_ = _args[10];
lean_object* v_wL_96_ = _args[11];
lean_object* v_wF_97_ = _args[12];
lean_object* v_X_98_ = _args[13];
lean_object* v_G_99_ = _args[14];
lean_object* v_E_100_ = _args[15];
lean_object* v_hM_101_ = _args[16];
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_tree_Formalism_L2_Pj_gd2XplusN(v_D_85_, v_B_86_, v_P_87_, v_j_88_, v_N_89_, v_h0_90_, v_h1_91_, v_h2_92_, v_h3_93_, v_h4_94_, v_ka_95_, v_wL_96_, v_wF_97_, v_X_98_, v_G_99_, v_E_100_, v_hM_101_);
lean_dec_ref(v_E_100_);
lean_dec_ref(v_X_98_);
lean_dec_ref(v_wF_97_);
lean_dec_ref(v_wL_96_);
lean_dec_ref(v_ka_95_);
lean_dec(v_N_89_);
lean_dec(v_j_88_);
lean_dec_ref(v_P_87_);
lean_dec_ref(v_B_86_);
lean_dec_ref(v_D_85_);
return v_res_102_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ExtendedPointBaseChange(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_WeightedPrimeSumBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntegralExtensionOfRegR1(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ExtendedPointBaseChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_WeightedPrimeSumBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
