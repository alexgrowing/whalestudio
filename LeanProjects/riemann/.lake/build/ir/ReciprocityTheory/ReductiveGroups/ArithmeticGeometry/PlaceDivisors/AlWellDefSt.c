// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective public import Mathlib.Algebra.DualNumber public import Mathlib.RingTheory.Valuation.Integers
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
lean_object* lp_mathlib_TrivSqZeroExt_semiring___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_inlAlgHom___redArg(lean_object*);
lean_object* lp_mathlib_AlgHom_comp___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_inrHom___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_restrictScalars___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_AlgHom_toLinearMap___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_lift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_TrivSqZeroExt_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_omega(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_omega___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_htSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_htSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC___redArg(lean_object* v_inst_1_, lean_object* v_00_u03c6_2_){
_start:
{
lean_object* v_toSemiring_3_; lean_object* v_toAddCommMonoid_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
v_toSemiring_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref_n(v_toSemiring_3_, 2);
lean_dec_ref(v_inst_1_);
v_toAddCommMonoid_4_ = lean_ctor_get(v_toSemiring_3_, 0);
v___x_5_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_3_);
v___x_6_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toSemiring_3_);
lean_inc_ref(v_toAddCommMonoid_4_);
v___x_7_ = lp_mathlib_TrivSqZeroExt_semiring___redArg(v_toSemiring_3_, v_toAddCommMonoid_4_, v___x_5_, v___x_6_);
v___x_8_ = lp_mathlib_TrivSqZeroExt_inlAlgHom___redArg(v_toAddCommMonoid_4_);
lean_inc(v_00_u03c6_2_);
v___x_9_ = lp_mathlib_AlgHom_comp___redArg(v___x_8_, v_00_u03c6_2_);
v___x_10_ = lp_mathlib_TrivSqZeroExt_inrHom___redArg(v_toSemiring_3_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_restrictScalars___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v___x_10_);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_AlgHom_toLinearMap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_12_, 0, v_00_u03c6_2_);
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v___f_12_);
lean_closure_set(v___f_13_, 1, v___f_11_);
v___x_14_ = lp_mathlib_TrivSqZeroExt_lift___redArg(v___x_7_, v___x_9_, v___f_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC(lean_object* v_O_15_, lean_object* v_inst_16_, lean_object* v_R_17_, lean_object* v_R_x27_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_00_u03c6_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC___redArg(v_inst_21_, v_00_u03c6_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC___boxed(lean_object* v_O_25_, lean_object* v_inst_26_, lean_object* v_R_27_, lean_object* v_R_x27_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_00_u03c6_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualBC(v_O_25_, v_inst_26_, v_R_27_, v_R_x27_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_00_u03c6_33_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
lean_dec_ref(v_inst_26_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale___redArg___lam__0(lean_object* v___x_35_, lean_object* v_a_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_38_; lean_object* v_toMul_39_; lean_object* v___x_40_; 
v___x_38_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_35_);
v_toMul_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_toMul_39_);
lean_dec_ref(v___x_38_);
v___x_40_ = lean_apply_2(v_toMul_39_, v_a_36_, v___y_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale___redArg(lean_object* v_inst_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_toSemiring_43_; lean_object* v_toAddCommMonoid_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v_toSemiring_43_ = lean_ctor_get(v_inst_41_, 0);
lean_inc_ref(v_toSemiring_43_);
v_toAddCommMonoid_44_ = lean_ctor_get(v_toSemiring_43_, 0);
lean_inc_ref_n(v_toAddCommMonoid_44_, 2);
v___x_45_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_43_);
v___x_46_ = lp_mathlib_Semiring_toOppositeModule___redArg(v_toSemiring_43_);
v___x_47_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_41_);
lean_dec_ref(v_inst_41_);
v___x_48_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_47_);
v___f_49_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale___redArg___lam__0), 3, 2);
lean_closure_set(v___f_49_, 0, v___x_48_);
lean_closure_set(v___f_49_, 1, v_a_42_);
v___x_50_ = lp_mathlib_TrivSqZeroExt_map___redArg(v_toSemiring_43_, v_toAddCommMonoid_44_, v_toAddCommMonoid_44_, v___x_45_, v___x_46_, v___f_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale(lean_object* v_O_51_, lean_object* v_inst_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_dualScale___redArg(v_inst_52_, v_a_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_omega(lean_object* v_O_55_, lean_object* v_inst_56_, lean_object* v_G_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_omega___boxed(lean_object* v_O_60_, lean_object* v_inst_61_, lean_object* v_G_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_omega(v_O_60_, v_inst_61_, v_G_62_, v_inst_63_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_G_62_);
lean_dec_ref(v_inst_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_htSpan(lean_object* v_O_65_, lean_object* v_inst_66_, lean_object* v_G_67_, lean_object* v_inst_68_, lean_object* v_p_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_htSpan___boxed(lean_object* v_O_71_, lean_object* v_inst_72_, lean_object* v_G_73_, lean_object* v_inst_74_, lean_object* v_p_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Pdiv_htSpan(v_O_71_, v_inst_72_, v_G_73_, v_inst_74_, v_p_75_);
lean_dec(v_p_75_);
lean_dec_ref(v_inst_74_);
lean_dec_ref(v_G_73_);
lean_dec_ref(v_inst_72_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_DualNumber(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Valuation_Integers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_DualNumber(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Valuation_Integers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
