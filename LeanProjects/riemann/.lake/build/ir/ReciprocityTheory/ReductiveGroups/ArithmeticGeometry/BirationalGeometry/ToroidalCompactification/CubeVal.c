// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg___lam__0(lean_object* v_toNPow_1_, lean_object* v_m_2_, lean_object* v_toMul_3_, lean_object* v_a_4_, lean_object* v_00_u03b8_5_, lean_object* v_x_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc(v_m_2_);
v___x_8_ = lean_apply_2(v_toNPow_1_, v_i_7_, v_m_2_);
v___x_9_ = lean_apply_2(v_toMul_3_, v_a_4_, v___x_8_);
v___x_10_ = lean_apply_3(v_00_u03b8_5_, v___x_9_, v_m_2_, v_x_6_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg(lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_00_u03b8_13_, lean_object* v_k_14_, lean_object* v_a_15_, lean_object* v_m_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_toMonoid_18_; lean_object* v_toMonoid_19_; lean_object* v___x_20_; lean_object* v_toMul_21_; lean_object* v_toNPow_22_; lean_object* v___x_23_; lean_object* v___f_24_; lean_object* v___x_25_; 
v_toMonoid_18_ = lean_ctor_get(v_inst_12_, 0);
v_toMonoid_19_ = lean_ctor_get(v_inst_11_, 0);
lean_inc_ref(v_toMonoid_19_);
lean_dec_ref(v_inst_11_);
v___x_20_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_19_);
v_toMul_21_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_toMul_21_);
lean_dec_ref(v___x_20_);
v_toNPow_22_ = lean_ctor_get(v_toMonoid_19_, 2);
lean_inc(v_toNPow_22_);
lean_dec_ref(v_toMonoid_19_);
v___x_23_ = l_List_range(v_k_14_);
v___f_24_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg___lam__0), 7, 6);
lean_closure_set(v___f_24_, 0, v_toNPow_22_);
lean_closure_set(v___f_24_, 1, v_m_16_);
lean_closure_set(v___f_24_, 2, v_toMul_21_);
lean_closure_set(v___f_24_, 3, v_a_15_);
lean_closure_set(v___f_24_, 4, v_00_u03b8_13_);
lean_closure_set(v___f_24_, 5, v_x_17_);
v___x_25_ = lp_mathlib_Finset_prod___redArg(v_toMonoid_18_, v___x_23_, v___f_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg___boxed(lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_00_u03b8_28_, lean_object* v_k_29_, lean_object* v_a_30_, lean_object* v_m_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg(v_inst_26_, v_inst_27_, v_00_u03b8_28_, v_k_29_, v_a_30_, v_m_31_, v_x_32_);
lean_dec_ref(v_inst_27_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN(lean_object* v_A_34_, lean_object* v_U_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_00_u03b8_38_, lean_object* v_k_39_, lean_object* v_a_40_, lean_object* v_m_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___redArg(v_inst_36_, v_inst_37_, v_00_u03b8_38_, v_k_39_, v_a_40_, v_m_41_, v_x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN___boxed(lean_object* v_A_44_, lean_object* v_U_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_00_u03b8_48_, lean_object* v_k_49_, lean_object* v_a_50_, lean_object* v_m_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubN(v_A_44_, v_U_45_, v_inst_46_, v_inst_47_, v_00_u03b8_48_, v_k_49_, v_a_50_, v_m_51_, v_x_52_);
lean_dec_ref(v_inst_47_);
return v_res_53_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
