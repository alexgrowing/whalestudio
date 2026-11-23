// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
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
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_CompRat_wE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_CompRat_wE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_CompRat_wE___redArg(lean_object* v_inst_1_, lean_object* v_H_2_, lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_toCommRing_6_; lean_object* v_toSemiring_7_; lean_object* v_toMonoid_8_; lean_object* v_toIntCast_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v_w0_12_; lean_object* v_toSemigroup_13_; lean_object* v___x_14_; lean_object* v_toNonUnitalNonAssocSemiring_15_; lean_object* v_toAddCommMonoid_16_; lean_object* v_toAddSemigroup_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_ref(v_inst_1_);
v___x_4_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_1_);
v___x_5_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_4_);
v_toCommRing_6_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toCommRing_6_);
lean_dec_ref(v_inst_1_);
v_toSemiring_7_ = lean_ctor_get(v_toCommRing_6_, 0);
lean_inc_ref(v_toSemiring_7_);
lean_dec_ref(v_toCommRing_6_);
v_toMonoid_8_ = lean_ctor_get(v_toSemiring_7_, 1);
v_toIntCast_9_ = lean_ctor_get(v___x_5_, 0);
lean_inc_n(v_toIntCast_9_, 2);
lean_dec_ref(v___x_5_);
v_fst_10_ = lean_ctor_get(v_s_3_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v_s_3_, 1);
lean_inc(v_snd_11_);
lean_dec_ref(v_s_3_);
v_w0_12_ = lean_ctor_get(v_H_2_, 2);
lean_inc(v_w0_12_);
lean_dec_ref(v_H_2_);
v_toSemigroup_13_ = lean_ctor_get(v_toMonoid_8_, 0);
lean_inc(v_toSemigroup_13_);
v___x_14_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_7_);
v_toNonUnitalNonAssocSemiring_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toNonUnitalNonAssocSemiring_15_);
lean_dec_ref(v___x_14_);
v_toAddCommMonoid_16_ = lean_ctor_get(v_toNonUnitalNonAssocSemiring_15_, 0);
lean_inc_ref(v_toAddCommMonoid_16_);
lean_dec_ref(v_toNonUnitalNonAssocSemiring_15_);
v_toAddSemigroup_17_ = lean_ctor_get(v_toAddCommMonoid_16_, 0);
lean_inc(v_toAddSemigroup_17_);
lean_dec_ref(v_toAddCommMonoid_16_);
v___x_18_ = lean_apply_1(v_toIntCast_9_, v_fst_10_);
v___x_19_ = lean_apply_1(v_toIntCast_9_, v_snd_11_);
v___x_20_ = lean_apply_2(v_toSemigroup_13_, v___x_19_, v_w0_12_);
v___x_21_ = lean_apply_2(v_toAddSemigroup_17_, v___x_18_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_CompRat_wE(lean_object* v_E_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_H_26_, lean_object* v_s_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_GlobalTheory_CompRat_wE___redArg(v_inst_23_, v_H_26_, v_s_27_);
return v___x_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CompHt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CompHt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
