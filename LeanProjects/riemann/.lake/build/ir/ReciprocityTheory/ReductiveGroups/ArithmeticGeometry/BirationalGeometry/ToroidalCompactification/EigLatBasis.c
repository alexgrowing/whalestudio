// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___redArg___lam__0(lean_object* v_00_u03c6_1_, lean_object* v_toAdd_2_, lean_object* v_toZero_3_, lean_object* v_a_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_17_; 
v_fst_5_ = lean_ctor_get(v_a_4_, 0);
v_snd_6_ = lean_ctor_get(v_a_4_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_17_ == 0)
{
v___x_8_ = v_a_4_;
v_isShared_9_ = v_isSharedCheck_17_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
lean_dec(v_a_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_17_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_inc(v_00_u03c6_1_);
v___x_10_ = lean_apply_1(v_00_u03c6_1_, v_fst_5_);
v___x_11_ = lean_apply_1(v_00_u03c6_1_, v_snd_6_);
lean_inc(v_toAdd_2_);
lean_inc(v_toZero_3_);
v___x_12_ = lean_apply_2(v_toAdd_2_, v___x_10_, v_toZero_3_);
v___x_13_ = lean_apply_2(v_toAdd_2_, v_toZero_3_, v___x_11_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_13_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___redArg(lean_object* v_inst_18_, lean_object* v_00_u03c6_19_){
_start:
{
lean_object* v_toSemiring_20_; lean_object* v___x_21_; lean_object* v_toAdd_22_; lean_object* v___x_23_; lean_object* v_toZero_24_; lean_object* v___f_25_; 
v_toSemiring_20_ = lean_ctor_get(v_inst_18_, 0);
lean_inc_ref_n(v_toSemiring_20_, 2);
lean_dec_ref(v_inst_18_);
v___x_21_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_20_);
v_toAdd_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_toAdd_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_20_);
v_toZero_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_toZero_24_);
lean_dec_ref(v___x_23_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___redArg___lam__0), 4, 3);
lean_closure_set(v___f_25_, 0, v_00_u03c6_19_);
lean_closure_set(v___f_25_, 1, v_toAdd_22_);
lean_closure_set(v___f_25_, 2, v_toZero_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR(lean_object* v_R_26_, lean_object* v_R_x27_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_00_u03c6_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___redArg(v_inst_29_, v_00_u03c6_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR___boxed(lean_object* v_R_32_, lean_object* v_R_x27_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_00_u03c6_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Chart_dualMapR(v_R_32_, v_R_x27_33_, v_inst_34_, v_inst_35_, v_00_u03c6_36_);
lean_dec_ref(v_inst_34_);
return v_res_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
