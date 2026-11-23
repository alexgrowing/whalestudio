// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyZeroChoice public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ___redArg(lean_object* v_G_1_, lean_object* v_rz_2_, lean_object* v_alz_3_, lean_object* v_th0_4_, lean_object* v_zc_5_, lean_object* v_rq_6_, lean_object* v_th_7_){
_start:
{
lean_object* v_N_8_; lean_object* v_w_9_; lean_object* v_del_10_; lean_object* v_th_x27_11_; lean_object* v_iet_12_; lean_object* v_et_13_; lean_object* v_mx_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_N_8_ = lean_ctor_get(v_G_1_, 0);
v_w_9_ = lean_ctor_get(v_G_1_, 1);
v_del_10_ = lean_ctor_get(v_G_1_, 2);
v_th_x27_11_ = lean_ctor_get(v_G_1_, 3);
v_iet_12_ = lean_ctor_get(v_G_1_, 10);
v_et_13_ = lean_ctor_get(v_G_1_, 11);
v_mx_14_ = lean_ctor_get(v_G_1_, 12);
v_isSharedCheck_21_ = !lean_is_exclusive(v_G_1_);
if (v_isSharedCheck_21_ == 0)
{
lean_object* v_unused_22_; lean_object* v_unused_23_; lean_object* v_unused_24_; lean_object* v_unused_25_; lean_object* v_unused_26_; lean_object* v_unused_27_; 
v_unused_22_ = lean_ctor_get(v_G_1_, 9);
lean_dec(v_unused_22_);
v_unused_23_ = lean_ctor_get(v_G_1_, 8);
lean_dec(v_unused_23_);
v_unused_24_ = lean_ctor_get(v_G_1_, 7);
lean_dec(v_unused_24_);
v_unused_25_ = lean_ctor_get(v_G_1_, 6);
lean_dec(v_unused_25_);
v_unused_26_ = lean_ctor_get(v_G_1_, 5);
lean_dec(v_unused_26_);
v_unused_27_ = lean_ctor_get(v_G_1_, 4);
lean_dec(v_unused_27_);
v___x_16_ = v_G_1_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_mx_14_);
lean_inc(v_et_13_);
lean_inc(v_iet_12_);
lean_inc(v_th_x27_11_);
lean_inc(v_del_10_);
lean_inc(v_w_9_);
lean_inc(v_N_8_);
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
lean_ctor_set(v___x_16_, 9, v_th_7_);
lean_ctor_set(v___x_16_, 8, v_rq_6_);
lean_ctor_set(v___x_16_, 7, v_zc_5_);
lean_ctor_set(v___x_16_, 6, v_th0_4_);
lean_ctor_set(v___x_16_, 5, v_alz_3_);
lean_ctor_set(v___x_16_, 4, v_rz_2_);
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_N_8_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_w_9_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_del_10_);
lean_ctor_set(v_reuseFailAlloc_20_, 3, v_th_x27_11_);
lean_ctor_set(v_reuseFailAlloc_20_, 4, v_rz_2_);
lean_ctor_set(v_reuseFailAlloc_20_, 5, v_alz_3_);
lean_ctor_set(v_reuseFailAlloc_20_, 6, v_th0_4_);
lean_ctor_set(v_reuseFailAlloc_20_, 7, v_zc_5_);
lean_ctor_set(v_reuseFailAlloc_20_, 8, v_rq_6_);
lean_ctor_set(v_reuseFailAlloc_20_, 9, v_th_7_);
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ(lean_object* v_D_28_, lean_object* v_B_29_, lean_object* v_P_30_, lean_object* v_j_31_, lean_object* v_X_32_, lean_object* v_ka_33_, lean_object* v_wL_34_, lean_object* v_wF_35_, lean_object* v_G_36_, lean_object* v_rz_37_, lean_object* v_alz_38_, lean_object* v_th0_39_, lean_object* v_zc_40_, lean_object* v_rq_41_, lean_object* v_th_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ___redArg(v_G_36_, v_rz_37_, v_alz_38_, v_th0_39_, v_zc_40_, v_rq_41_, v_th_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ___boxed(lean_object* v_D_44_, lean_object* v_B_45_, lean_object* v_P_46_, lean_object* v_j_47_, lean_object* v_X_48_, lean_object* v_ka_49_, lean_object* v_wL_50_, lean_object* v_wF_51_, lean_object* v_G_52_, lean_object* v_rz_53_, lean_object* v_alz_54_, lean_object* v_th0_55_, lean_object* v_zc_56_, lean_object* v_rq_57_, lean_object* v_th_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_GlobalFamilyData_setZQ(v_D_44_, v_B_45_, v_P_46_, v_j_47_, v_X_48_, v_ka_49_, v_wL_50_, v_wF_51_, v_G_52_, v_rz_53_, v_alz_54_, v_th0_55_, v_zc_56_, v_rq_57_, v_th_58_);
lean_dec_ref(v_wF_51_);
lean_dec_ref(v_wL_50_);
lean_dec_ref(v_ka_49_);
lean_dec_ref(v_X_48_);
lean_dec(v_j_47_);
lean_dec_ref(v_P_46_);
lean_dec_ref(v_B_45_);
lean_dec_ref(v_D_44_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr___redArg(lean_object* v_Q_60_){
_start:
{
lean_object* v_y_61_; lean_object* v_g0_62_; lean_object* v_c_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_y_61_ = lean_ctor_get(v_Q_60_, 0);
v_g0_62_ = lean_ctor_get(v_Q_60_, 1);
v_c_63_ = lean_ctor_get(v_Q_60_, 2);
v_isSharedCheck_70_ = !lean_is_exclusive(v_Q_60_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v_Q_60_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_c_63_);
lean_inc(v_g0_62_);
lean_inc(v_y_61_);
lean_dec(v_Q_60_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_y_61_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_g0_62_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_c_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr(lean_object* v_D_71_, lean_object* v_B_72_, lean_object* v_P_73_, lean_object* v_j_74_, lean_object* v_X_75_, lean_object* v_ka_76_, lean_object* v_wL_77_, lean_object* v_wF_78_, lean_object* v_G_79_, lean_object* v_rz_80_, lean_object* v_alz_81_, lean_object* v_th0_82_, lean_object* v_zc_83_, lean_object* v_rq_84_, lean_object* v_th_85_, lean_object* v_la_86_, lean_object* v_Q_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr___redArg(v_Q_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr___boxed(lean_object** _args){
lean_object* v_D_89_ = _args[0];
lean_object* v_B_90_ = _args[1];
lean_object* v_P_91_ = _args[2];
lean_object* v_j_92_ = _args[3];
lean_object* v_X_93_ = _args[4];
lean_object* v_ka_94_ = _args[5];
lean_object* v_wL_95_ = _args[6];
lean_object* v_wF_96_ = _args[7];
lean_object* v_G_97_ = _args[8];
lean_object* v_rz_98_ = _args[9];
lean_object* v_alz_99_ = _args[10];
lean_object* v_th0_100_ = _args[11];
lean_object* v_zc_101_ = _args[12];
lean_object* v_rq_102_ = _args[13];
lean_object* v_th_103_ = _args[14];
lean_object* v_la_104_ = _args[15];
lean_object* v_Q_105_ = _args[16];
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_Formalism_MainNotions_Gaps_EtaleWeightGaps_LocalPointData_tr(v_D_89_, v_B_90_, v_P_91_, v_j_92_, v_X_93_, v_ka_94_, v_wL_95_, v_wF_96_, v_G_97_, v_rz_98_, v_alz_99_, v_th0_100_, v_zc_101_, v_rq_102_, v_th_103_, v_la_104_, v_Q_105_);
lean_dec(v_th_103_);
lean_dec(v_rq_102_);
lean_dec_ref(v_zc_101_);
lean_dec(v_th0_100_);
lean_dec_ref(v_alz_99_);
lean_dec(v_rz_98_);
lean_dec_ref(v_G_97_);
lean_dec_ref(v_wF_96_);
lean_dec_ref(v_wL_95_);
lean_dec_ref(v_ka_94_);
lean_dec_ref(v_X_93_);
lean_dec(v_j_92_);
lean_dec_ref(v_P_91_);
lean_dec_ref(v_B_90_);
lean_dec_ref(v_D_89_);
return v_res_106_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroBundledOfLift(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsGlobalFamilyZeroChoice(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsGlobalFamilyQuotientBounded(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroOfReducedInputs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroBundledOfLift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsGlobalFamilyZeroChoice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsGlobalFamilyQuotientBounded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
