// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
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
lean_object* lp_tree_GlobalTheory_EX_OB_divTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_layObj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_layObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_layObj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_divXtr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_divXtr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_divXtr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_ofObj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_ofObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_ofObj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_pointObj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_pointObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_pointObj___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_layObj___redArg(lean_object* v_Y_1_){
_start:
{
lean_object* v_gatT_2_; lean_object* v_X_3_; lean_object* v_lev_4_; lean_object* v_th_5_; lean_object* v_cmp_6_; lean_object* v_tw_7_; lean_object* v_Gy_8_; lean_object* v_ker_9_; lean_object* v_errX_10_; lean_object* v_nch_11_; lean_object* v_xd_12_; lean_object* v_p0_13_; lean_object* v_amb_14_; lean_object* v_amb0_15_; lean_object* v_gauge_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_23_; 
v_gatT_2_ = lean_ctor_get(v_Y_1_, 0);
v_X_3_ = lean_ctor_get(v_Y_1_, 1);
v_lev_4_ = lean_ctor_get(v_Y_1_, 2);
v_th_5_ = lean_ctor_get(v_Y_1_, 3);
v_cmp_6_ = lean_ctor_get(v_Y_1_, 4);
v_tw_7_ = lean_ctor_get(v_Y_1_, 5);
v_Gy_8_ = lean_ctor_get(v_Y_1_, 6);
v_ker_9_ = lean_ctor_get(v_Y_1_, 7);
v_errX_10_ = lean_ctor_get(v_Y_1_, 8);
v_nch_11_ = lean_ctor_get(v_Y_1_, 9);
v_xd_12_ = lean_ctor_get(v_Y_1_, 10);
v_p0_13_ = lean_ctor_get(v_Y_1_, 11);
v_amb_14_ = lean_ctor_get(v_Y_1_, 12);
v_amb0_15_ = lean_ctor_get(v_Y_1_, 13);
v_gauge_16_ = lean_ctor_get(v_Y_1_, 14);
v_isSharedCheck_23_ = !lean_is_exclusive(v_Y_1_);
if (v_isSharedCheck_23_ == 0)
{
v___x_18_ = v_Y_1_;
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_gauge_16_);
lean_inc(v_amb0_15_);
lean_inc(v_amb_14_);
lean_inc(v_p0_13_);
lean_inc(v_xd_12_);
lean_inc(v_nch_11_);
lean_inc(v_errX_10_);
lean_inc(v_ker_9_);
lean_inc(v_Gy_8_);
lean_inc(v_tw_7_);
lean_inc(v_cmp_6_);
lean_inc(v_th_5_);
lean_inc(v_lev_4_);
lean_inc(v_X_3_);
lean_inc(v_gatT_2_);
lean_dec(v_Y_1_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 11, v_ker_9_);
lean_ctor_set(v___x_18_, 10, v_p0_13_);
lean_ctor_set(v___x_18_, 9, v_X_3_);
lean_ctor_set(v___x_18_, 8, v_lev_4_);
lean_ctor_set(v___x_18_, 7, v_xd_12_);
lean_ctor_set(v___x_18_, 6, v_nch_11_);
lean_ctor_set(v___x_18_, 5, v_errX_10_);
lean_ctor_set(v___x_18_, 4, v_Gy_8_);
lean_ctor_set(v___x_18_, 3, v_tw_7_);
lean_ctor_set(v___x_18_, 2, v_cmp_6_);
lean_ctor_set(v___x_18_, 1, v_th_5_);
v___x_21_ = v___x_18_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_gatT_2_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_th_5_);
lean_ctor_set(v_reuseFailAlloc_22_, 2, v_cmp_6_);
lean_ctor_set(v_reuseFailAlloc_22_, 3, v_tw_7_);
lean_ctor_set(v_reuseFailAlloc_22_, 4, v_Gy_8_);
lean_ctor_set(v_reuseFailAlloc_22_, 5, v_errX_10_);
lean_ctor_set(v_reuseFailAlloc_22_, 6, v_nch_11_);
lean_ctor_set(v_reuseFailAlloc_22_, 7, v_xd_12_);
lean_ctor_set(v_reuseFailAlloc_22_, 8, v_lev_4_);
lean_ctor_set(v_reuseFailAlloc_22_, 9, v_X_3_);
lean_ctor_set(v_reuseFailAlloc_22_, 10, v_p0_13_);
lean_ctor_set(v_reuseFailAlloc_22_, 11, v_ker_9_);
lean_ctor_set(v_reuseFailAlloc_22_, 12, v_amb_14_);
lean_ctor_set(v_reuseFailAlloc_22_, 13, v_amb0_15_);
lean_ctor_set(v_reuseFailAlloc_22_, 14, v_gauge_16_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_layObj(lean_object* v_D_24_, lean_object* v_Y_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_GlobalTheory_Mem_Top_layObj___redArg(v_Y_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_layObj___boxed(lean_object* v_D_27_, lean_object* v_Y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_GlobalTheory_Mem_Top_layObj(v_D_27_, v_Y_28_);
lean_dec_ref(v_D_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_divXtr___redArg(lean_object* v_X_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_GlobalTheory_EX_OB_divTr___redArg(v_X_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_divXtr(lean_object* v_D_32_, lean_object* v_X_33_, lean_object* v_N_34_, lean_object* v_h_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_GlobalTheory_EX_OB_divTr___redArg(v_X_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_divXtr___boxed(lean_object* v_D_37_, lean_object* v_X_38_, lean_object* v_N_39_, lean_object* v_h_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_GlobalTheory_Mem_Top_divXtr(v_D_37_, v_X_38_, v_N_39_, v_h_40_);
lean_dec(v_h_40_);
lean_dec_ref(v_N_39_);
lean_dec_ref(v_D_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj___redArg(lean_object* v_gatT_42_, lean_object* v_Gy_43_, lean_object* v_X_44_, lean_object* v_ex_45_){
_start:
{
lean_object* v_lev_46_; lean_object* v_th_47_; lean_object* v_cmp_48_; lean_object* v_tw_49_; lean_object* v_ker_50_; lean_object* v_errX_51_; lean_object* v_nch_52_; lean_object* v_xd_53_; lean_object* v_p0_54_; lean_object* v_amb_55_; lean_object* v_amb0_56_; lean_object* v_gauge_57_; lean_object* v___x_58_; 
v_lev_46_ = lean_ctor_get(v_ex_45_, 0);
v_th_47_ = lean_ctor_get(v_ex_45_, 1);
v_cmp_48_ = lean_ctor_get(v_ex_45_, 2);
v_tw_49_ = lean_ctor_get(v_ex_45_, 3);
v_ker_50_ = lean_ctor_get(v_ex_45_, 4);
v_errX_51_ = lean_ctor_get(v_ex_45_, 5);
v_nch_52_ = lean_ctor_get(v_ex_45_, 6);
v_xd_53_ = lean_ctor_get(v_ex_45_, 7);
lean_inc(v_xd_53_);
v_p0_54_ = lean_ctor_get(v_ex_45_, 8);
v_amb_55_ = lean_ctor_get(v_ex_45_, 9);
v_amb0_56_ = lean_ctor_get(v_ex_45_, 10);
v_gauge_57_ = lean_ctor_get(v_ex_45_, 11);
lean_inc_ref(v_gauge_57_);
lean_inc_ref(v_amb0_56_);
lean_inc_ref(v_amb_55_);
lean_inc_ref(v_ker_50_);
lean_inc_ref(v_p0_54_);
lean_inc_ref(v_lev_46_);
lean_inc_ref(v_nch_52_);
lean_inc_ref(v_errX_51_);
lean_inc_ref(v_tw_49_);
lean_inc_ref(v_cmp_48_);
lean_inc_ref(v_th_47_);
v___x_58_ = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(v___x_58_, 0, v_gatT_42_);
lean_ctor_set(v___x_58_, 1, v_th_47_);
lean_ctor_set(v___x_58_, 2, v_cmp_48_);
lean_ctor_set(v___x_58_, 3, v_tw_49_);
lean_ctor_set(v___x_58_, 4, v_Gy_43_);
lean_ctor_set(v___x_58_, 5, v_errX_51_);
lean_ctor_set(v___x_58_, 6, v_nch_52_);
lean_ctor_set(v___x_58_, 7, v_xd_53_);
lean_ctor_set(v___x_58_, 8, v_lev_46_);
lean_ctor_set(v___x_58_, 9, v_X_44_);
lean_ctor_set(v___x_58_, 10, v_p0_54_);
lean_ctor_set(v___x_58_, 11, v_ker_50_);
lean_ctor_set(v___x_58_, 12, v_amb_55_);
lean_ctor_set(v___x_58_, 13, v_amb0_56_);
lean_ctor_set(v___x_58_, 14, v_gauge_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj___redArg___boxed(lean_object* v_gatT_59_, lean_object* v_Gy_60_, lean_object* v_X_61_, lean_object* v_ex_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_tree_GlobalTheory_Mem_Top_extraObj___redArg(v_gatT_59_, v_Gy_60_, v_X_61_, v_ex_62_);
lean_dec_ref(v_ex_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj(lean_object* v_D_64_, lean_object* v_L_65_, lean_object* v_gatT_66_, lean_object* v_Gx_67_, lean_object* v_Gy_68_, lean_object* v_K_69_, lean_object* v_X_70_, lean_object* v_cX_71_, lean_object* v_ex_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_tree_GlobalTheory_Mem_Top_extraObj___redArg(v_gatT_66_, v_Gy_68_, v_X_70_, v_ex_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_extraObj___boxed(lean_object* v_D_74_, lean_object* v_L_75_, lean_object* v_gatT_76_, lean_object* v_Gx_77_, lean_object* v_Gy_78_, lean_object* v_K_79_, lean_object* v_X_80_, lean_object* v_cX_81_, lean_object* v_ex_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_tree_GlobalTheory_Mem_Top_extraObj(v_D_74_, v_L_75_, v_gatT_76_, v_Gx_77_, v_Gy_78_, v_K_79_, v_X_80_, v_cX_81_, v_ex_82_);
lean_dec_ref(v_ex_82_);
lean_dec_ref(v_cX_81_);
lean_dec_ref(v_K_79_);
lean_dec_ref(v_Gx_77_);
lean_dec_ref(v_L_75_);
lean_dec_ref(v_D_74_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_ofObj___redArg(lean_object* v_O_84_){
_start:
{
lean_object* v_gatT_85_; lean_object* v_Gy_86_; lean_object* v_X_87_; lean_object* v_ex_88_; lean_object* v___x_89_; 
v_gatT_85_ = lean_ctor_get(v_O_84_, 1);
lean_inc_ref(v_gatT_85_);
v_Gy_86_ = lean_ctor_get(v_O_84_, 3);
lean_inc_ref(v_Gy_86_);
v_X_87_ = lean_ctor_get(v_O_84_, 5);
lean_inc_ref(v_X_87_);
v_ex_88_ = lean_ctor_get(v_O_84_, 7);
lean_inc_ref(v_ex_88_);
lean_dec_ref(v_O_84_);
v___x_89_ = lp_tree_GlobalTheory_Mem_Top_extraObj___redArg(v_gatT_85_, v_Gy_86_, v_X_87_, v_ex_88_);
lean_dec_ref(v_ex_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_ofObj(lean_object* v_D_90_, lean_object* v_O_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_tree_GlobalTheory_Mem_Top_ofObj___redArg(v_O_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_ofObj___boxed(lean_object* v_D_93_, lean_object* v_O_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_tree_GlobalTheory_Mem_Top_ofObj(v_D_93_, v_O_94_);
lean_dec_ref(v_D_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_pointObj___redArg(lean_object* v_p_96_){
_start:
{
lean_object* v_ta_97_; lean_object* v_xa_98_; lean_object* v_gatT_99_; lean_object* v_Gy_100_; lean_object* v_X_101_; lean_object* v_ex_102_; lean_object* v___x_103_; 
v_ta_97_ = lean_ctor_get(v_p_96_, 3);
lean_inc_ref(v_ta_97_);
v_xa_98_ = lean_ctor_get(v_p_96_, 4);
lean_inc_ref(v_xa_98_);
v_gatT_99_ = lean_ctor_get(v_p_96_, 2);
lean_inc_ref(v_gatT_99_);
lean_dec_ref(v_p_96_);
v_Gy_100_ = lean_ctor_get(v_ta_97_, 1);
lean_inc_ref(v_Gy_100_);
lean_dec_ref(v_ta_97_);
v_X_101_ = lean_ctor_get(v_xa_98_, 0);
lean_inc_ref(v_X_101_);
v_ex_102_ = lean_ctor_get(v_xa_98_, 1);
lean_inc_ref(v_ex_102_);
lean_dec_ref(v_xa_98_);
v___x_103_ = lp_tree_GlobalTheory_Mem_Top_extraObj___redArg(v_gatT_99_, v_Gy_100_, v_X_101_, v_ex_102_);
lean_dec_ref(v_ex_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_pointObj(lean_object* v_C_104_, lean_object* v_p_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lp_tree_GlobalTheory_Mem_Top_pointObj___redArg(v_p_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_pointObj___boxed(lean_object* v_C_107_, lean_object* v_p_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_GlobalTheory_Mem_Top_pointObj(v_C_107_, v_p_108_);
lean_dec_ref(v_C_107_);
return v_res_109_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_PointPropertyEqSizeFree(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
