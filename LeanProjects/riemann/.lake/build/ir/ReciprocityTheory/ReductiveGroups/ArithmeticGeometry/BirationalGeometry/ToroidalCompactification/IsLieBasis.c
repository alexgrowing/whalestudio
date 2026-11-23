// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toOppositeModule___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR___redArg___lam__0(lean_object* v___x_1_, lean_object* v_c_2_, lean_object* v___y_3_){
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
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR___redArg(lean_object* v_inst_7_, lean_object* v_c_8_){
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
v___f_15_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR___redArg___lam__0), 3, 2);
lean_closure_set(v___f_15_, 0, v___x_14_);
lean_closure_set(v___f_15_, 1, v_c_8_);
v___x_16_ = lp_mathlib_TrivSqZeroExt_map___redArg(v_toSemiring_9_, v_toAddCommMonoid_10_, v_toAddCommMonoid_10_, v___x_11_, v___x_12_, v___f_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR(lean_object* v_R_17_, lean_object* v_inst_18_, lean_object* v_c_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Geo_Tor_epsScaleR___redArg(v_inst_18_, v_c_19_);
return v___x_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
