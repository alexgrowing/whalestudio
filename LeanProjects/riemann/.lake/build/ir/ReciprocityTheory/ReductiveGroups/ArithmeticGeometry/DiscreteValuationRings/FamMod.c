// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secZero___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secAdd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secAdd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secNeg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secNeg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_CategoryTheory_homOfLE___at___00ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secZero___lam__0(lean_object* v_X_1_, lean_object* v_L_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_presheaf_4_; lean_object* v_obj_5_; lean_object* v_U_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toSemiring_9_; lean_object* v___x_10_; lean_object* v_toZero_11_; 
v_presheaf_4_ = lean_ctor_get(v_X_1_, 1);
lean_inc_ref(v_presheaf_4_);
lean_dec_ref(v_X_1_);
v_obj_5_ = lean_ctor_get(v_presheaf_4_, 0);
lean_inc(v_obj_5_);
lean_dec_ref(v_presheaf_4_);
v_U_6_ = lean_ctor_get(v_L_2_, 0);
lean_inc_ref(v_U_6_);
lean_dec_ref(v_L_2_);
v___x_7_ = lean_apply_1(v_U_6_, v_x_3_);
v___x_8_ = lean_apply_1(v_obj_5_, v___x_7_);
v_toSemiring_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_toSemiring_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_9_);
v_toZero_11_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_toZero_11_);
lean_dec_ref(v___x_10_);
return v_toZero_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secZero(lean_object* v_X_12_, lean_object* v_L_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secZero___lam__0), 3, 2);
lean_closure_set(v___f_14_, 0, v_X_12_);
lean_closure_set(v___f_14_, 1, v_L_13_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secAdd___lam__0(lean_object* v_X_15_, lean_object* v_L_16_, lean_object* v_s_17_, lean_object* v_t_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_presheaf_20_; lean_object* v_obj_21_; lean_object* v_U_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toSemiring_25_; lean_object* v___x_26_; lean_object* v_toAdd_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_presheaf_20_ = lean_ctor_get(v_X_15_, 1);
lean_inc_ref(v_presheaf_20_);
lean_dec_ref(v_X_15_);
v_obj_21_ = lean_ctor_get(v_presheaf_20_, 0);
lean_inc(v_obj_21_);
lean_dec_ref(v_presheaf_20_);
v_U_22_ = lean_ctor_get(v_L_16_, 0);
lean_inc_ref(v_U_22_);
lean_dec_ref(v_L_16_);
lean_inc_n(v_i_19_, 2);
v___x_23_ = lean_apply_1(v_U_22_, v_i_19_);
v___x_24_ = lean_apply_1(v_obj_21_, v___x_23_);
v_toSemiring_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_toSemiring_25_);
lean_dec_ref(v___x_24_);
v___x_26_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_25_);
v_toAdd_27_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_toAdd_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = lean_apply_1(v_s_17_, v_i_19_);
v___x_29_ = lean_apply_1(v_t_18_, v_i_19_);
v___x_30_ = lean_apply_2(v_toAdd_27_, v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secAdd(lean_object* v_X_31_, lean_object* v_L_32_, lean_object* v_s_33_, lean_object* v_t_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secAdd___lam__0), 5, 4);
lean_closure_set(v___f_35_, 0, v_X_31_);
lean_closure_set(v___f_35_, 1, v_L_32_);
lean_closure_set(v___f_35_, 2, v_s_33_);
lean_closure_set(v___f_35_, 3, v_t_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secNeg___lam__0(lean_object* v_X_36_, lean_object* v_L_37_, lean_object* v_s_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_presheaf_40_; lean_object* v_obj_41_; lean_object* v_U_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toNeg_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_presheaf_40_ = lean_ctor_get(v_X_36_, 1);
lean_inc_ref(v_presheaf_40_);
lean_dec_ref(v_X_36_);
v_obj_41_ = lean_ctor_get(v_presheaf_40_, 0);
lean_inc(v_obj_41_);
lean_dec_ref(v_presheaf_40_);
v_U_42_ = lean_ctor_get(v_L_37_, 0);
lean_inc_ref(v_U_42_);
lean_dec_ref(v_L_37_);
lean_inc(v_i_39_);
v___x_43_ = lean_apply_1(v_U_42_, v_i_39_);
v___x_44_ = lean_apply_1(v_obj_41_, v___x_43_);
v___x_45_ = lp_mathlib_Ring_toAddCommGroup___redArg(v___x_44_);
lean_dec_ref(v___x_44_);
v___x_46_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_45_);
lean_dec_ref(v___x_45_);
v_toNeg_47_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_toNeg_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_apply_1(v_s_38_, v_i_39_);
v___x_49_ = lean_apply_1(v_toNeg_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secNeg(lean_object* v_X_50_, lean_object* v_L_51_, lean_object* v_s_52_){
_start:
{
lean_object* v___f_53_; 
v___f_53_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secNeg___lam__0), 4, 3);
lean_closure_set(v___f_53_, 0, v_X_50_);
lean_closure_set(v___f_53_, 1, v_L_51_);
lean_closure_set(v___f_53_, 2, v_s_52_);
return v___f_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_CategoryTheory_homOfLE___at___00ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale_spec__0(lean_object* v___x_54_, lean_object* v_x_55_, lean_object* v_y_56_, lean_object* v_h_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale___lam__0(lean_object* v_X_59_, lean_object* v_L_60_, lean_object* v_c_61_, lean_object* v_s_62_, lean_object* v_i_63_){
_start:
{
lean_object* v_presheaf_64_; lean_object* v_obj_65_; lean_object* v_map_66_; lean_object* v_U_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_toSemiring_70_; lean_object* v___x_71_; lean_object* v_toMul_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_presheaf_64_ = lean_ctor_get(v_X_59_, 1);
lean_inc_ref(v_presheaf_64_);
lean_dec_ref(v_X_59_);
v_obj_65_ = lean_ctor_get(v_presheaf_64_, 0);
lean_inc(v_obj_65_);
v_map_66_ = lean_ctor_get(v_presheaf_64_, 1);
lean_inc(v_map_66_);
lean_dec_ref(v_presheaf_64_);
v_U_67_ = lean_ctor_get(v_L_60_, 0);
lean_inc_ref(v_U_67_);
lean_dec_ref(v_L_60_);
lean_inc(v_i_63_);
v___x_68_ = lean_apply_1(v_U_67_, v_i_63_);
v___x_69_ = lean_apply_1(v_obj_65_, v___x_68_);
v_toSemiring_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_toSemiring_70_);
lean_dec_ref(v___x_69_);
v___x_71_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_70_);
v_toMul_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_toMul_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_4(v_map_66_, v___x_73_, v___x_68_, lean_box(0), v_c_61_);
v___x_75_ = lean_apply_1(v_s_62_, v_i_63_);
v___x_76_ = lean_apply_2(v_toMul_72_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale(lean_object* v_X_77_, lean_object* v_L_78_, lean_object* v_c_79_, lean_object* v_s_80_){
_start:
{
lean_object* v___f_81_; 
v___f_81_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_SecOps_secScale___lam__0), 5, 4);
lean_closure_set(v___f_81_, 0, v_X_77_);
lean_closure_set(v___f_81_, 1, v_L_78_);
lean_closure_set(v___f_81_, 2, v_c_79_);
lean_closure_set(v___f_81_, 3, v_s_80_);
return v___f_81_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
