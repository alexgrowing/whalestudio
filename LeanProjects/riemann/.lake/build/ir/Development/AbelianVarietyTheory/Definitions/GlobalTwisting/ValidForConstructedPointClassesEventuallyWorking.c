// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth public import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_objAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_objAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_objAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_RawSel_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_RawSel_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_objAt___redArg(lean_object* v_Fm_1_, lean_object* v_x_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_toFamCore_4_; lean_object* v_gatT_5_; lean_object* v_X_6_; lean_object* v_Gx_7_; lean_object* v_Gy_8_; lean_object* v_GK_9_; lean_object* v_cX_10_; lean_object* v_ex_11_; lean_object* v_L_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_toFamCore_4_ = lean_ctor_get(v_Fm_1_, 0);
lean_inc_ref(v_toFamCore_4_);
v_gatT_5_ = lean_ctor_get(v_Fm_1_, 6);
lean_inc_ref(v_gatT_5_);
v_X_6_ = lean_ctor_get(v_Fm_1_, 7);
lean_inc_ref(v_X_6_);
v_Gx_7_ = lean_ctor_get(v_Fm_1_, 8);
lean_inc_ref(v_Gx_7_);
v_Gy_8_ = lean_ctor_get(v_Fm_1_, 9);
lean_inc_ref(v_Gy_8_);
v_GK_9_ = lean_ctor_get(v_Fm_1_, 10);
lean_inc_ref(v_GK_9_);
v_cX_10_ = lean_ctor_get(v_Fm_1_, 12);
lean_inc_ref(v_cX_10_);
v_ex_11_ = lean_ctor_get(v_Fm_1_, 13);
lean_inc_ref(v_ex_11_);
lean_dec_ref(v_Fm_1_);
v_L_12_ = lean_ctor_get(v_toFamCore_4_, 2);
lean_inc_ref(v_L_12_);
lean_dec_ref(v_toFamCore_4_);
lean_inc_n(v_i_3_, 5);
lean_inc_n(v_x_2_, 5);
v___x_13_ = lean_apply_2(v_L_12_, v_x_2_, v_i_3_);
v___x_14_ = lean_apply_2(v_gatT_5_, v_x_2_, v_i_3_);
v___x_15_ = lean_apply_2(v_Gx_7_, v_x_2_, v_i_3_);
v___x_16_ = lean_apply_2(v_Gy_8_, v_x_2_, v_i_3_);
v___x_17_ = lean_apply_2(v_X_6_, v_x_2_, v_i_3_);
v___x_18_ = lean_apply_3(v_ex_11_, v_x_2_, lean_box(0), v_i_3_);
v___x_19_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_19_, 0, v___x_13_);
lean_ctor_set(v___x_19_, 1, v___x_14_);
lean_ctor_set(v___x_19_, 2, v___x_15_);
lean_ctor_set(v___x_19_, 3, v___x_16_);
lean_ctor_set(v___x_19_, 4, v_GK_9_);
lean_ctor_set(v___x_19_, 5, v___x_17_);
lean_ctor_set(v___x_19_, 6, v_cX_10_);
lean_ctor_set(v___x_19_, 7, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_objAt(lean_object* v_eps_20_, lean_object* v_Fm_21_, lean_object* v_x_22_, lean_object* v_hx_23_, lean_object* v_i_24_){
_start:
{
lean_object* v_toFamCore_25_; lean_object* v_gatT_26_; lean_object* v_X_27_; lean_object* v_Gx_28_; lean_object* v_Gy_29_; lean_object* v_GK_30_; lean_object* v_cX_31_; lean_object* v_ex_32_; lean_object* v_L_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_toFamCore_25_ = lean_ctor_get(v_Fm_21_, 0);
lean_inc_ref(v_toFamCore_25_);
v_gatT_26_ = lean_ctor_get(v_Fm_21_, 6);
lean_inc_ref(v_gatT_26_);
v_X_27_ = lean_ctor_get(v_Fm_21_, 7);
lean_inc_ref(v_X_27_);
v_Gx_28_ = lean_ctor_get(v_Fm_21_, 8);
lean_inc_ref(v_Gx_28_);
v_Gy_29_ = lean_ctor_get(v_Fm_21_, 9);
lean_inc_ref(v_Gy_29_);
v_GK_30_ = lean_ctor_get(v_Fm_21_, 10);
lean_inc_ref(v_GK_30_);
v_cX_31_ = lean_ctor_get(v_Fm_21_, 12);
lean_inc_ref(v_cX_31_);
v_ex_32_ = lean_ctor_get(v_Fm_21_, 13);
lean_inc_ref(v_ex_32_);
lean_dec_ref(v_Fm_21_);
v_L_33_ = lean_ctor_get(v_toFamCore_25_, 2);
lean_inc_ref(v_L_33_);
lean_dec_ref(v_toFamCore_25_);
lean_inc_n(v_i_24_, 5);
lean_inc_n(v_x_22_, 5);
v___x_34_ = lean_apply_2(v_L_33_, v_x_22_, v_i_24_);
v___x_35_ = lean_apply_2(v_gatT_26_, v_x_22_, v_i_24_);
v___x_36_ = lean_apply_2(v_Gx_28_, v_x_22_, v_i_24_);
v___x_37_ = lean_apply_2(v_Gy_29_, v_x_22_, v_i_24_);
v___x_38_ = lean_apply_2(v_X_27_, v_x_22_, v_i_24_);
v___x_39_ = lean_apply_3(v_ex_32_, v_x_22_, lean_box(0), v_i_24_);
v___x_40_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_40_, 0, v___x_34_);
lean_ctor_set(v___x_40_, 1, v___x_35_);
lean_ctor_set(v___x_40_, 2, v___x_36_);
lean_ctor_set(v___x_40_, 3, v___x_37_);
lean_ctor_set(v___x_40_, 4, v_GK_30_);
lean_ctor_set(v___x_40_, 5, v___x_38_);
lean_ctor_set(v___x_40_, 6, v_cX_31_);
lean_ctor_set(v___x_40_, 7, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_objAt___boxed(lean_object* v_eps_41_, lean_object* v_Fm_42_, lean_object* v_x_43_, lean_object* v_hx_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_GlobalTheory_Fc_objAt(v_eps_41_, v_Fm_42_, v_x_43_, v_hx_44_, v_i_45_);
lean_dec(v_eps_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_RawSel_map___redArg(lean_object* v_00_u03c0_47_, lean_object* v_00_u03c3_48_, lean_object* v_eps_49_, lean_object* v_Fm_50_, lean_object* v_x_51_, lean_object* v_i_52_){
_start:
{
lean_object* v_toFamCore_53_; lean_object* v_gatT_54_; lean_object* v_X_55_; lean_object* v_Gx_56_; lean_object* v_Gy_57_; lean_object* v_GK_58_; lean_object* v_Csz_59_; lean_object* v_cX_60_; lean_object* v_ex_61_; lean_object* v_D_62_; lean_object* v_L_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_toFamCore_53_ = lean_ctor_get(v_Fm_50_, 0);
v_gatT_54_ = lean_ctor_get(v_Fm_50_, 6);
v_X_55_ = lean_ctor_get(v_Fm_50_, 7);
v_Gx_56_ = lean_ctor_get(v_Fm_50_, 8);
v_Gy_57_ = lean_ctor_get(v_Fm_50_, 9);
v_GK_58_ = lean_ctor_get(v_Fm_50_, 10);
v_Csz_59_ = lean_ctor_get(v_Fm_50_, 11);
lean_inc(v_Csz_59_);
v_cX_60_ = lean_ctor_get(v_Fm_50_, 12);
v_ex_61_ = lean_ctor_get(v_Fm_50_, 13);
v_D_62_ = lean_ctor_get(v_toFamCore_53_, 1);
v_L_63_ = lean_ctor_get(v_toFamCore_53_, 2);
lean_inc_ref(v_D_62_);
lean_inc_n(v_i_52_, 7);
lean_inc_n(v_x_51_, 7);
v___x_64_ = lean_apply_2(v_D_62_, v_x_51_, v_i_52_);
lean_inc_ref(v_L_63_);
v___x_65_ = lean_apply_2(v_L_63_, v_x_51_, v_i_52_);
lean_inc_ref(v_gatT_54_);
v___x_66_ = lean_apply_2(v_gatT_54_, v_x_51_, v_i_52_);
lean_inc_ref(v_Gx_56_);
v___x_67_ = lean_apply_2(v_Gx_56_, v_x_51_, v_i_52_);
lean_inc_ref(v_Gy_57_);
v___x_68_ = lean_apply_2(v_Gy_57_, v_x_51_, v_i_52_);
lean_inc_ref(v_X_55_);
v___x_69_ = lean_apply_2(v_X_55_, v_x_51_, v_i_52_);
lean_inc_ref(v_ex_61_);
v___x_70_ = lean_apply_3(v_ex_61_, v_x_51_, lean_box(0), v_i_52_);
lean_inc_ref(v_cX_60_);
lean_inc_ref(v_GK_58_);
v___x_71_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_71_, 0, v___x_65_);
lean_ctor_set(v___x_71_, 1, v___x_66_);
lean_ctor_set(v___x_71_, 2, v___x_67_);
lean_ctor_set(v___x_71_, 3, v___x_68_);
lean_ctor_set(v___x_71_, 4, v_GK_58_);
lean_ctor_set(v___x_71_, 5, v___x_69_);
lean_ctor_set(v___x_71_, 6, v_cX_60_);
lean_ctor_set(v___x_71_, 7, v___x_70_);
v___x_72_ = lean_apply_6(v_00_u03c3_48_, v_eps_49_, v_Fm_50_, lean_box(0), v_x_51_, lean_box(0), v_i_52_);
v___x_73_ = lean_apply_4(v_00_u03c0_47_, v___x_64_, v___x_71_, v_Csz_59_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Fc_RawSel_map(lean_object* v_Bd_74_, lean_object* v_Bd_x27_75_, lean_object* v_00_u03c0_76_, lean_object* v_00_U0001d49c_77_, lean_object* v_00_u03c3_78_, lean_object* v_eps_79_, lean_object* v_Fm_80_, lean_object* v_hc_81_, lean_object* v_x_82_, lean_object* v_hx_83_, lean_object* v_i_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_tree_GlobalTheory_Fc_RawSel_map___redArg(v_00_u03c0_76_, v_00_u03c3_78_, v_eps_79_, v_Fm_80_, v_x_82_, v_i_84_);
return v___x_85_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_RationalRootsDef(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_FamilyClassSevenDutiesAndStableLattices(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_SmoothDesignExistence_DGamSmooth(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_PrimeDiscriminants_Scales(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ValidForConstructedPointClassesEventuallyWorking(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_RationalRootsDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_FamilyClassSevenDutiesAndStableLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_SmoothDesignExistence_DGamSmooth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_PrimeDiscriminants_Scales(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
