// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementI
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementG public import Formalism.GaussJetBounds.StatementH
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_mfact___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_jetPair___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_jetPair___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_jetPair(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_jetPair___redArg___lam__0(lean_object* v_P_1_, lean_object* v_toNatCast_2_, lean_object* v_toMul_3_, lean_object* v_Th_4_, lean_object* v_00_u03ba_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
lean_inc_ref_n(v_00_u03ba_5_, 2);
v___x_6_ = lp_mathlib_MvPolynomial_coeff___redArg(v_00_u03ba_5_, v_P_1_);
v___x_7_ = lp_tree_Formalism_DworkPowerSeriesWeights_mfact___redArg(v_00_u03ba_5_);
v___x_8_ = lean_apply_1(v_toNatCast_2_, v___x_7_);
lean_inc(v_toMul_3_);
v___x_9_ = lean_apply_2(v_toMul_3_, v___x_6_, v___x_8_);
v___x_10_ = lean_apply_1(v_Th_4_, v_00_u03ba_5_);
v___x_11_ = lean_apply_2(v_toMul_3_, v___x_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_jetPair___redArg(lean_object* v_inst_12_, lean_object* v_P_13_, lean_object* v_Th_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toSemiring_17_; lean_object* v_toAddCommMonoid_18_; lean_object* v_support_19_; lean_object* v___x_20_; lean_object* v_toMul_21_; lean_object* v___x_22_; lean_object* v_toRing_23_; lean_object* v___x_24_; lean_object* v_toAddMonoidWithOne_25_; lean_object* v_toNatCast_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v___x_15_ = lp_mathlib_Field_toSemifield___redArg(v_inst_12_);
v___x_16_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_15_);
v_toSemiring_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v___x_16_);
v_toAddCommMonoid_18_ = lean_ctor_get(v_toSemiring_17_, 0);
lean_inc_ref(v_toAddCommMonoid_18_);
v_support_19_ = lean_ctor_get(v_P_13_, 0);
lean_inc(v_support_19_);
v___x_20_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_17_);
v_toMul_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_toMul_21_);
lean_dec_ref(v___x_20_);
v___x_22_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_12_);
v_toRing_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_toRing_23_);
lean_dec_ref(v___x_22_);
v___x_24_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_23_);
v_toAddMonoidWithOne_25_ = lean_ctor_get(v___x_24_, 1);
lean_inc_ref(v_toAddMonoidWithOne_25_);
lean_dec_ref(v___x_24_);
v_toNatCast_26_ = lean_ctor_get(v_toAddMonoidWithOne_25_, 0);
lean_inc(v_toNatCast_26_);
lean_dec_ref(v_toAddMonoidWithOne_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_jetPair___redArg___lam__0), 5, 4);
lean_closure_set(v___f_27_, 0, v_P_13_);
lean_closure_set(v___f_27_, 1, v_toNatCast_26_);
lean_closure_set(v___f_27_, 2, v_toMul_21_);
lean_closure_set(v___f_27_, 3, v_Th_14_);
v___x_28_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_18_, v_support_19_, v___f_27_);
lean_dec_ref(v_toAddCommMonoid_18_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_jetPair(lean_object* v_K_29_, lean_object* v_inst_30_, lean_object* v_00_u03b9_31_, lean_object* v_P_32_, lean_object* v_Th_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_DworkPowerSeriesWeights_jetPair___redArg(v_inst_30_, v_P_32_, v_Th_33_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementG(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementH(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
