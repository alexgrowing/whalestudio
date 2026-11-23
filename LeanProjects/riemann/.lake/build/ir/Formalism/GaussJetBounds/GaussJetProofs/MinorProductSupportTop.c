// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.MinorProductSupportTop
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Formalism.GaussJetBounds.StatementH
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop___redArg(lean_object* v_inst_1_, lean_object* v_T_2_, lean_object* v_i_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_4_) == 0)
{
lean_object* v___x_5_; uint8_t v___x_6_; 
lean_dec(v_T_2_);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_dec_eq(v_i_3_, v___x_5_);
lean_dec(v_i_3_);
if (v___x_6_ == 0)
{
lean_object* v_toSemiring_7_; lean_object* v___x_8_; lean_object* v_toZero_9_; 
v_toSemiring_7_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_7_);
lean_dec_ref(v_inst_1_);
v___x_8_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_7_);
v_toZero_9_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_toZero_9_);
lean_dec_ref(v___x_8_);
return v_toZero_9_;
}
else
{
lean_object* v___x_10_; lean_object* v_toAddMonoidWithOne_11_; lean_object* v_toOne_12_; 
v___x_10_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_11_ = lean_ctor_get(v___x_10_, 1);
lean_inc_ref(v_toAddMonoidWithOne_11_);
lean_dec_ref(v___x_10_);
v_toOne_12_ = lean_ctor_get(v_toAddMonoidWithOne_11_, 2);
lean_inc(v_toOne_12_);
lean_dec_ref(v_toAddMonoidWithOne_11_);
return v_toOne_12_;
}
}
else
{
lean_object* v_val_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_val_13_ = lean_ctor_get(v_x_4_, 0);
lean_inc(v_val_13_);
lean_dec_ref_known(v_x_4_, 1);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_dec_eq(v_i_3_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_dec_ref(v_inst_1_);
v___x_16_ = lean_apply_2(v_T_2_, v_i_3_, v_val_13_);
return v___x_16_;
}
else
{
lean_object* v_toSemiring_17_; lean_object* v___x_18_; lean_object* v_toZero_19_; 
lean_dec(v_val_13_);
lean_dec(v_i_3_);
lean_dec(v_T_2_);
v_toSemiring_17_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v_inst_1_);
v___x_18_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_17_);
v_toZero_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_toZero_19_);
lean_dec_ref(v___x_18_);
return v_toZero_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop(lean_object* v_R_20_, lean_object* v_inst_21_, lean_object* v_N0_22_, lean_object* v_m_23_, lean_object* v_T_24_, lean_object* v_i_25_, lean_object* v_x_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop___redArg(v_inst_21_, v_T_24_, v_i_25_, v_x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop___boxed(lean_object* v_R_28_, lean_object* v_inst_29_, lean_object* v_N0_30_, lean_object* v_m_31_, lean_object* v_T_32_, lean_object* v_i_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Formalism_DworkPowerSeriesWeights_shapeATop(v_R_28_, v_inst_29_, v_N0_30_, v_m_31_, v_T_32_, v_i_33_, v_x_34_);
lean_dec(v_m_31_);
lean_dec(v_N0_30_);
return v_res_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementH(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GenLogInverse(builtin);
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
