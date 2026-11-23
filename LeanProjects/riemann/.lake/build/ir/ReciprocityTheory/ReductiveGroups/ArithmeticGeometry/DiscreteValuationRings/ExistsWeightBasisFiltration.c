// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_Ov(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_Ov___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___closed__0 = (const lean_object*)&lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_Ov(lean_object* v_F_1_, lean_object* v_inst_2_, lean_object* v_v_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_Ov___boxed(lean_object* v_F_5_, lean_object* v_inst_6_, lean_object* v_v_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_Ov(v_F_5_, v_inst_6_, v_v_7_);
lean_dec_ref(v_v_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___lam__0(lean_object* v_toOne_9_, lean_object* v_r_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_r_10_);
lean_ctor_set(v___x_11_, 1, v_toOne_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg(lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v_toSemiring_15_; lean_object* v_algebraMap_16_; lean_object* v_toMonoid_17_; lean_object* v___x_18_; lean_object* v_toOne_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; 
v_toSemiring_15_ = lean_ctor_get(v_inst_13_, 0);
v_algebraMap_16_ = lean_ctor_get(v_inst_14_, 1);
lean_inc(v_algebraMap_16_);
lean_dec_ref(v_inst_14_);
v_toMonoid_17_ = lean_ctor_get(v_toSemiring_15_, 1);
v___x_18_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_17_);
v_toOne_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_toOne_19_);
lean_dec_ref(v___x_18_);
v___f_20_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___lam__0), 2, 1);
lean_closure_set(v___f_20_, 0, v_toOne_19_);
v___f_21_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___closed__0));
v___f_22_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v___f_21_);
lean_closure_set(v___f_22_, 1, v___f_20_);
v___f_23_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_23_, 0, v___f_22_);
lean_closure_set(v___f_23_, 1, v_algebraMap_16_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___boxed(lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg(v_inst_24_, v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF(lean_object* v_F_27_, lean_object* v_inst_28_, lean_object* v_V_29_, lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v_toSemiring_32_; lean_object* v_algebraMap_33_; lean_object* v_toMonoid_34_; lean_object* v___x_35_; lean_object* v_toOne_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; 
v_toSemiring_32_ = lean_ctor_get(v_inst_30_, 0);
v_algebraMap_33_ = lean_ctor_get(v_inst_31_, 1);
lean_inc(v_algebraMap_33_);
lean_dec_ref(v_inst_31_);
v_toMonoid_34_ = lean_ctor_get(v_toSemiring_32_, 1);
v___x_35_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_34_);
v_toOne_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_toOne_36_);
lean_dec_ref(v___x_35_);
v___f_37_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___lam__0), 2, 1);
lean_closure_set(v___f_37_, 0, v_toOne_36_);
v___f_38_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___closed__0));
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_39_, 0, v___f_38_);
lean_closure_set(v___f_39_, 1, v___f_37_);
v___f_40_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_40_, 0, v___f_39_);
lean_closure_set(v___f_40_, 1, v_algebraMap_33_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___boxed(lean_object* v_F_41_, lean_object* v_inst_42_, lean_object* v_V_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF(v_F_41_, v_inst_42_, v_V_43_, v_inst_44_, v_inst_45_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_42_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___redArg(lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v_toSemiring_49_; lean_object* v_algebraMap_50_; lean_object* v_toMonoid_51_; lean_object* v___x_52_; lean_object* v_toOne_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; 
v_toSemiring_49_ = lean_ctor_get(v_inst_47_, 0);
v_algebraMap_50_ = lean_ctor_get(v_inst_48_, 1);
lean_inc(v_algebraMap_50_);
lean_dec_ref(v_inst_48_);
v_toMonoid_51_ = lean_ctor_get(v_toSemiring_49_, 1);
v___x_52_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_51_);
v_toOne_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_toOne_53_);
lean_dec_ref(v___x_52_);
v___f_54_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___lam__0), 2, 1);
lean_closure_set(v___f_54_, 0, v_toOne_53_);
v___f_55_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_algVF___redArg___closed__0));
v___f_56_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_56_, 0, v___f_55_);
lean_closure_set(v___f_56_, 1, v___f_54_);
v___f_57_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_57_, 0, v___f_56_);
lean_closure_set(v___f_57_, 1, v_algebraMap_50_);
v___f_58_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_58_, 0, v___f_57_);
return v___f_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___redArg___boxed(lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___redArg(v_inst_59_, v_inst_60_);
lean_dec_ref(v_inst_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO(lean_object* v_F_62_, lean_object* v_inst_63_, lean_object* v_v_64_, lean_object* v_V_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_00_u03d6_69_, lean_object* v_inst_70_, lean_object* v_h_u03d6_71_, lean_object* v_hv_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___redArg(v_inst_66_, v_inst_70_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO___boxed(lean_object* v_F_74_, lean_object* v_inst_75_, lean_object* v_v_76_, lean_object* v_V_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_00_u03d6_81_, lean_object* v_inst_82_, lean_object* v_h_u03d6_83_, lean_object* v_hv_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO(v_F_74_, v_inst_75_, v_v_76_, v_V_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_00_u03d6_81_, v_inst_82_, v_h_u03d6_83_, v_hv_84_);
lean_dec(v_00_u03d6_81_);
lean_dec_ref(v_inst_78_);
lean_dec_ref(v_v_76_);
lean_dec_ref(v_inst_75_);
return v_res_85_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_ValuativeCriterion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_ValuativeCriterion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
