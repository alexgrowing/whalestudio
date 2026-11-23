// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
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
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__0(lean_object* v_00_u03b5_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; 
v_fst_3_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_p_2_);
v___x_5_ = lean_apply_2(v_00_u03b5_1_, v_fst_3_, v_snd_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__1(lean_object* v_00_u03c6_6_, lean_object* v_p_7_){
_start:
{
lean_object* v_fst_8_; lean_object* v_snd_9_; lean_object* v___x_10_; 
v_fst_8_ = lean_ctor_get(v_p_7_, 0);
lean_inc(v_fst_8_);
v_snd_9_ = lean_ctor_get(v_p_7_, 1);
lean_inc(v_snd_9_);
lean_dec_ref(v_p_7_);
v___x_10_ = lean_apply_2(v_00_u03c6_6_, v_fst_8_, v_snd_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__2(lean_object* v_i_11_, lean_object* v_j_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_i_11_);
lean_ctor_set(v___x_14_, 1, v_k_13_);
v___x_15_ = lean_apply_1(v_j_12_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__3(lean_object* v_00_u03c6_16_, lean_object* v_00_u03b5_17_, lean_object* v_X_18_, lean_object* v_Y_19_, lean_object* v_L_20_, lean_object* v_inst_21_, lean_object* v_j_22_, lean_object* v_t_23_, lean_object* v___x_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v_U_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_97__overap_33_; lean_object* v___x_34_; 
lean_inc_n(v_i_25_, 3);
v___x_26_ = lean_apply_1(v_00_u03c6_16_, v_i_25_);
v___x_27_ = lean_apply_1(v_00_u03b5_17_, v_i_25_);
lean_inc_ref(v_Y_19_);
v___x_28_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_X_18_, v_Y_19_, v_L_20_, v_inst_21_, v___x_26_, v___x_27_);
v_U_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc_ref(v_U_29_);
lean_dec_ref(v___x_28_);
v___f_30_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__2), 3, 2);
lean_closure_set(v___f_30_, 0, v_i_25_);
lean_closure_set(v___f_30_, 1, v_j_22_);
lean_inc_ref(v___f_30_);
v___x_31_ = lean_apply_1(v_U_29_, v___f_30_);
v___x_32_ = lean_apply_2(v_t_23_, v_i_25_, v___f_30_);
v___x_97__overap_33_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(v_Y_19_, v___x_31_, v___x_24_);
v___x_34_ = lean_apply_1(v___x_97__overap_33_, v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__4(lean_object* v_Y_35_, lean_object* v_X_36_, lean_object* v_L_37_, lean_object* v___x_38_, lean_object* v___f_39_, lean_object* v___f_40_, lean_object* v_00_u03c6_41_, lean_object* v_00_u03b5_42_, lean_object* v_inst_43_, lean_object* v_t_44_, lean_object* v_inst_45_, lean_object* v_j_46_){
_start:
{
lean_object* v_presheaf_47_; lean_object* v_obj_48_; lean_object* v___x_49_; lean_object* v_U_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_toMonoid_55_; lean_object* v___f_56_; lean_object* v___x_57_; 
v_presheaf_47_ = lean_ctor_get(v_Y_35_, 1);
v_obj_48_ = lean_ctor_get(v_presheaf_47_, 0);
lean_inc_ref(v_L_37_);
lean_inc_ref(v_Y_35_);
lean_inc_ref(v_X_36_);
v___x_49_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___redArg(v_X_36_, v_Y_35_, v_L_37_, v___x_38_, v___f_39_, v___f_40_);
v_U_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_U_50_);
lean_dec_ref(v___x_49_);
lean_inc(v_j_46_);
v___x_51_ = lean_apply_1(v_U_50_, v_j_46_);
lean_inc(v_obj_48_);
v___x_52_ = lean_apply_1(v_obj_48_, v___x_51_);
v___x_53_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_52_);
lean_dec_ref(v___x_52_);
v___x_54_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_53_);
v_toMonoid_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_toMonoid_55_);
lean_dec_ref(v___x_54_);
v___f_56_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__3), 10, 9);
lean_closure_set(v___f_56_, 0, v_00_u03c6_41_);
lean_closure_set(v___f_56_, 1, v_00_u03b5_42_);
lean_closure_set(v___f_56_, 2, v_X_36_);
lean_closure_set(v___f_56_, 3, v_Y_35_);
lean_closure_set(v___f_56_, 4, v_L_37_);
lean_closure_set(v___f_56_, 5, v_inst_43_);
lean_closure_set(v___f_56_, 6, v_j_46_);
lean_closure_set(v___f_56_, 7, v_t_44_);
lean_closure_set(v___f_56_, 8, v___x_51_);
v___x_57_ = lp_mathlib_Finset_prod___redArg(v_toMonoid_55_, v_inst_45_, v___f_56_);
lean_dec_ref(v_toMonoid_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg(lean_object* v_X_58_, lean_object* v_Y_59_, lean_object* v_L_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_00_u03c6_63_, lean_object* v_00_u03b5_64_, lean_object* v_t_65_){
_start:
{
lean_object* v___f_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___f_69_; 
lean_inc_ref(v_00_u03b5_64_);
v___f_66_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__0), 2, 1);
lean_closure_set(v___f_66_, 0, v_00_u03b5_64_);
lean_inc_ref(v_00_u03c6_63_);
v___f_67_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__1), 2, 1);
lean_closure_set(v___f_67_, 0, v_00_u03c6_63_);
lean_inc(v_inst_61_);
lean_inc(v_inst_62_);
v___x_68_ = lp_mathlib_Multiset_product___redArg(v_inst_62_, v_inst_61_);
v___f_69_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg___lam__4), 12, 11);
lean_closure_set(v___f_69_, 0, v_Y_59_);
lean_closure_set(v___f_69_, 1, v_X_58_);
lean_closure_set(v___f_69_, 2, v_L_60_);
lean_closure_set(v___f_69_, 3, v___x_68_);
lean_closure_set(v___f_69_, 4, v___f_67_);
lean_closure_set(v___f_69_, 5, v___f_66_);
lean_closure_set(v___f_69_, 6, v_00_u03c6_63_);
lean_closure_set(v___f_69_, 7, v_00_u03b5_64_);
lean_closure_set(v___f_69_, 8, v_inst_61_);
lean_closure_set(v___f_69_, 9, v_t_65_);
lean_closure_set(v___f_69_, 10, v_inst_62_);
return v___f_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen(lean_object* v_X_70_, lean_object* v_Y_71_, lean_object* v_L_72_, lean_object* v_K_73_, lean_object* v_inst_74_, lean_object* v_J_75_, lean_object* v_inst_76_, lean_object* v_00_u03c6_77_, lean_object* v_00_u03b5_78_, lean_object* v_t_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_GeneratorPullback_finProdGen___redArg(v_X_70_, v_Y_71_, v_L_72_, v_inst_74_, v_inst_76_, v_00_u03c6_77_, v_00_u03b5_78_, v_t_79_);
return v___x_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd(builtin);
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
