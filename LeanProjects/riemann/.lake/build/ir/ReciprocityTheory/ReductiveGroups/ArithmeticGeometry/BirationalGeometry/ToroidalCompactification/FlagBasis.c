// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
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
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toOppositeModule___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg___closed__0 = (const lean_object*)&lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul___redArg___lam__0(lean_object* v___x_1_, lean_object* v_c_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toMul_5_; lean_object* v___x_6_; 
v___x_4_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_1_);
v_toMul_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toMul_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_apply_2(v_toMul_5_, v_c_2_, v___y_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul___redArg(lean_object* v_inst_7_, lean_object* v_c_8_){
_start:
{
lean_object* v_toSemiring_9_; lean_object* v_toAddCommMonoid_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v_toSemiring_9_ = lean_ctor_get(v_inst_7_, 0);
lean_inc_ref(v_toSemiring_9_);
v_toAddCommMonoid_10_ = lean_ctor_get(v_toSemiring_9_, 0);
lean_inc_ref_n(v_toAddCommMonoid_10_, 2);
v___x_11_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_9_);
v___x_12_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toSemiring_9_);
v___x_13_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_7_);
lean_dec_ref(v_inst_7_);
v___x_14_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_13_);
v___f_15_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul___redArg___lam__0), 3, 2);
lean_closure_set(v___f_15_, 0, v___x_14_);
lean_closure_set(v___f_15_, 1, v_c_8_);
v___x_16_ = lp_mathlib_TrivSqZeroExt_map___redArg(v_toSemiring_9_, v_toAddCommMonoid_10_, v_toAddCommMonoid_10_, v___x_11_, v___x_12_, v___f_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul(lean_object* v_R_17_, lean_object* v_inst_18_, lean_object* v_c_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsMul___redArg(v_inst_18_, v_c_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg(lean_object* v_00_u03c4_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___f_24_; 
v___f_23_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg___closed__0));
v___f_24_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_24_, 0, v_00_u03c4_22_);
lean_closure_set(v___f_24_, 1, v___f_23_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb(lean_object* v_E_25_, lean_object* v_inst_26_, lean_object* v_00_u03c4_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___redArg(v_00_u03c4_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_00_u03c4_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_conjEmb(v_E_29_, v_inst_30_, v_00_u03c4_31_);
lean_dec_ref(v_inst_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row___redArg(lean_object* v_x_33_){
_start:
{
lean_object* v_snd_34_; lean_object* v_fst_35_; lean_object* v_fst_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_snd_34_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_snd_34_);
v_fst_35_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_fst_35_);
lean_dec_ref(v_x_33_);
v_fst_36_ = lean_ctor_get(v_snd_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_snd_34_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v_snd_34_, 1);
lean_dec(v_unused_44_);
v___x_38_ = v_snd_34_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_fst_36_);
lean_dec(v_snd_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v_fst_36_);
lean_ctor_set(v___x_38_, 0, v_fst_35_);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_fst_35_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_fst_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row(lean_object* v_E_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_H_49_, lean_object* v_D_50_, lean_object* v_n_51_, lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row___redArg(v_x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row___boxed(lean_object* v_E_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_H_58_, lean_object* v_D_59_, lean_object* v_n_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Letter_row(v_E_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_H_58_, v_D_59_, v_n_60_, v_x_61_);
lean_dec(v_n_60_);
lean_dec_ref(v_D_59_);
lean_dec_ref(v_H_58_);
lean_dec_ref(v_inst_55_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter___redArg(lean_object* v_00_u03c4_63_, lean_object* v_i_64_, lean_object* v_b_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_i_64_);
lean_ctor_set(v___x_66_, 1, v_b_65_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_00_u03c4_63_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter(lean_object* v_E_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_H_72_, lean_object* v_D_73_, lean_object* v_n_74_, lean_object* v_00_u03c4_75_, lean_object* v_i_76_, lean_object* v_b_77_, lean_object* v_h_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter___redArg(v_00_u03c4_75_, v_i_76_, v_b_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter___boxed(lean_object* v_E_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_H_84_, lean_object* v_D_85_, lean_object* v_n_86_, lean_object* v_00_u03c4_87_, lean_object* v_i_88_, lean_object* v_b_89_, lean_object* v_h_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_letter(v_E_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_H_84_, v_D_85_, v_n_86_, v_00_u03c4_87_, v_i_88_, v_b_89_, v_h_90_);
lean_dec(v_n_86_);
lean_dec_ref(v_D_85_);
lean_dec_ref(v_H_84_);
lean_dec_ref(v_inst_81_);
return v_res_91_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
