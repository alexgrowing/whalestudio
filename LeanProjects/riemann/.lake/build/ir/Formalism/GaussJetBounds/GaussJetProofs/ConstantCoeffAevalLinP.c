// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementJ public import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genA___redArg(lean_object* v_inst_1_, lean_object* v_d_2_, lean_object* v_TT_3_, lean_object* v_T_4_, lean_object* v_y_5_, lean_object* v_y_x27_6_){
_start:
{
lean_object* v_fst_13_; lean_object* v_snd_14_; lean_object* v_fst_15_; lean_object* v_snd_16_; uint8_t v___x_17_; 
v_fst_13_ = lean_ctor_get(v_y_x27_6_, 0);
lean_inc(v_fst_13_);
v_snd_14_ = lean_ctor_get(v_y_x27_6_, 1);
lean_inc(v_snd_14_);
lean_dec_ref(v_y_x27_6_);
v_fst_15_ = lean_ctor_get(v_y_5_, 0);
lean_inc(v_fst_15_);
v_snd_16_ = lean_ctor_get(v_y_5_, 1);
lean_inc(v_snd_16_);
lean_dec_ref(v_y_5_);
v___x_17_ = lp_mathlib_ZMod_decidableEq(v_d_2_, v_fst_13_, v_fst_15_);
lean_dec(v_fst_13_);
if (v___x_17_ == 0)
{
lean_dec(v_snd_16_);
lean_dec(v_fst_15_);
lean_dec(v_snd_14_);
lean_dec(v_T_4_);
lean_dec(v_TT_3_);
lean_dec(v_d_2_);
goto v___jp_7_;
}
else
{
lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v_fst_20_; lean_object* v_snd_21_; uint8_t v___x_22_; 
v_fst_18_ = lean_ctor_get(v_snd_14_, 0);
lean_inc(v_fst_18_);
v_snd_19_ = lean_ctor_get(v_snd_14_, 1);
lean_inc(v_snd_19_);
lean_dec(v_snd_14_);
v_fst_20_ = lean_ctor_get(v_snd_16_, 0);
lean_inc(v_fst_20_);
v_snd_21_ = lean_ctor_get(v_snd_16_, 1);
lean_inc(v_snd_21_);
lean_dec(v_snd_16_);
v___x_22_ = lean_nat_dec_eq(v_snd_19_, v_snd_21_);
lean_dec(v_snd_21_);
lean_dec(v_snd_19_);
if (v___x_22_ == 0)
{
lean_dec(v_fst_20_);
lean_dec(v_fst_18_);
lean_dec(v_fst_15_);
lean_dec(v_T_4_);
lean_dec(v_TT_3_);
lean_dec(v_d_2_);
goto v___jp_7_;
}
else
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Formalism_DworkPowerSeriesWeights_effMat___redArg(v_inst_1_, v_d_2_, v_TT_3_, v_T_4_, v_fst_15_, v_fst_20_, v_fst_18_);
return v___x_23_;
}
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toSemiring_10_; lean_object* v___x_11_; lean_object* v_toZero_12_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
lean_dec_ref(v_inst_1_);
v___x_9_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_8_);
v_toSemiring_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toSemiring_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_10_);
v_toZero_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_toZero_12_);
lean_dec_ref(v___x_11_);
return v_toZero_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genA(lean_object* v_K_24_, lean_object* v_inst_25_, lean_object* v_d_26_, lean_object* v_N0_27_, lean_object* v_N1_28_, lean_object* v_TT_29_, lean_object* v_T_30_, lean_object* v_y_31_, lean_object* v_y_x27_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_DworkPowerSeriesWeights_genA___redArg(v_inst_25_, v_d_26_, v_TT_29_, v_T_30_, v_y_31_, v_y_x27_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genA___boxed(lean_object* v_K_34_, lean_object* v_inst_35_, lean_object* v_d_36_, lean_object* v_N0_37_, lean_object* v_N1_38_, lean_object* v_TT_39_, lean_object* v_T_40_, lean_object* v_y_41_, lean_object* v_y_x27_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_DworkPowerSeriesWeights_genA(v_K_34_, v_inst_35_, v_d_36_, v_N0_37_, v_N1_38_, v_TT_39_, v_T_40_, v_y_41_, v_y_x27_42_);
lean_dec(v_N1_38_);
lean_dec(v_N0_37_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementJ(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementJ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
