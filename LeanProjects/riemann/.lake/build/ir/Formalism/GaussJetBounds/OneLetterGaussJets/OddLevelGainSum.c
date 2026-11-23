// Lean compiler output
// Module: Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.Statement
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
extern lean_object* lp_mathlib_Nat_instLattice;
lean_object* lp_mathlib_Finset_sup___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_tree_Formalism_IncomingBounds_capL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_log(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_dot_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_kaMaxOneLetter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_kaMaxOneLetter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_kaMaxOneLetter___redArg(lean_object* v_d_1_, lean_object* v_TT_2_, lean_object* v_nu1_3_, lean_object* v_nu2_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toSemilatticeSup_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_5_ = lp_mathlib_Nat_instLattice;
v_toSemilatticeSup_6_ = lean_ctor_get(v___x_5_, 0);
v___x_7_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_nu1_3_);
lean_inc(v_TT_2_);
lean_inc_ref_n(v_toSemilatticeSup_6_, 2);
v___x_8_ = lp_mathlib_Finset_sup___redArg(v_toSemilatticeSup_6_, v___x_7_, v_TT_2_, v_nu1_3_);
v___x_9_ = lp_mathlib_ZMod_fintype___redArg(v_d_1_);
v___x_10_ = lean_alloc_closure((void*)(lp_tree_Formalism_IncomingBounds_capL), 5, 4);
lean_closure_set(v___x_10_, 0, v_d_1_);
lean_closure_set(v___x_10_, 1, v_TT_2_);
lean_closure_set(v___x_10_, 2, v_nu1_3_);
lean_closure_set(v___x_10_, 3, v_nu2_4_);
v___x_11_ = lp_mathlib_Finset_sup___redArg(v_toSemilatticeSup_6_, v___x_7_, v___x_9_, v___x_10_);
v___x_12_ = lean_nat_dec_le(v___x_8_, v___x_11_);
if (v___x_12_ == 0)
{
lean_dec(v___x_11_);
return v___x_8_;
}
else
{
lean_dec(v___x_8_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_kaMaxOneLetter(lean_object* v_d_13_, lean_object* v_inst_14_, lean_object* v_TT_15_, lean_object* v_nu1_16_, lean_object* v_nu2_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_kaMaxOneLetter___redArg(v_d_13_, v_TT_15_, v_nu1_16_, v_nu2_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg___lam__0(lean_object* v_toFun_19_, lean_object* v_l_20_, lean_object* v_i_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___f_26_; 
v___x_22_ = lean_apply_1(v_toFun_19_, v_i_21_);
v___x_23_ = lp_mathlib_Nat_log(v_l_20_, v___x_22_);
v___x_24_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_23_);
v___x_25_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_26_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_26_, 0, v___x_24_);
lean_closure_set(v___f_26_, 1, v___x_25_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg___lam__0___boxed(lean_object* v_toFun_27_, lean_object* v_l_28_, lean_object* v_i_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg___lam__0(v_toFun_27_, v_l_28_, v_i_29_);
lean_dec(v_l_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg(lean_object* v_l_31_, lean_object* v_00_u03ba_32_){
_start:
{
lean_object* v_support_33_; lean_object* v_toFun_34_; lean_object* v___f_35_; lean_object* v___x_36_; 
v_support_33_ = lean_ctor_get(v_00_u03ba_32_, 0);
lean_inc(v_support_33_);
v_toFun_34_ = lean_ctor_get(v_00_u03ba_32_, 1);
lean_inc(v_toFun_34_);
lean_dec_ref(v_00_u03ba_32_);
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_35_, 0, v_toFun_34_);
lean_closure_set(v___f_35_, 1, v_l_31_);
v___x_36_ = lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_dot_spec__0_spec__0___redArg(v_support_33_, v___f_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter(lean_object* v_00_u03b9_37_, lean_object* v_l_38_, lean_object* v_00_u03ba_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_tree_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_digitLossOneLetter___redArg(v_l_38_, v_00_u03ba_39_);
return v___x_40_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterGaussJets_OddLevelGainSum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
