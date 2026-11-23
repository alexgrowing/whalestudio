// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.Special
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Formalism.GaussJetBounds.StatementB
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg___redArg___lam__0(lean_object* v_lt_1_, lean_object* v_inst_2_, lean_object* v_t_3_, lean_object* v_n_4_, lean_object* v_k_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
lean_inc(v_k_5_);
v___x_6_ = lean_apply_1(v_lt_1_, v_k_5_);
v___x_7_ = lean_apply_2(v_inst_2_, v___x_6_, v_t_3_);
v___x_8_ = lean_unbox(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec(v_k_5_);
lean_dec_ref(v_n_4_);
v___x_9_ = lean_unsigned_to_nat(0u);
return v___x_9_;
}
else
{
lean_object* v_toFun_10_; lean_object* v___x_11_; 
v_toFun_10_ = lean_ctor_get(v_n_4_, 1);
lean_inc(v_toFun_10_);
lean_dec_ref(v_n_4_);
v___x_11_ = lean_apply_1(v_toFun_10_, v_k_5_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg___redArg(lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_lt_14_, lean_object* v_t_15_, lean_object* v_n_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg___redArg___lam__0), 5, 4);
lean_closure_set(v___f_17_, 0, v_lt_14_);
lean_closure_set(v___f_17_, 1, v_inst_12_);
lean_closure_set(v___f_17_, 2, v_t_15_);
lean_closure_set(v___f_17_, 3, v_n_16_);
v___x_18_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_19_ = lp_mathlib_Finset_sum___redArg(v___x_18_, v_inst_13_, v___f_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg(lean_object* v_00_u03c3_20_, lean_object* v_inst_21_, lean_object* v_00_u03b9_22_, lean_object* v_inst_23_, lean_object* v_lt_24_, lean_object* v_t_25_, lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_DworkPowerSeriesWeights_spLdeg___redArg(v_inst_21_, v_inst_23_, v_lt_24_, v_t_25_, v_n_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo___redArg(lean_object* v_inst_28_, lean_object* v_top_29_, lean_object* v_o_30_, lean_object* v_c_31_){
_start:
{
lean_object* v___x_32_; lean_object* v_toAddMonoidWithOne_33_; 
v___x_32_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_28_);
v_toAddMonoidWithOne_33_ = lean_ctor_get(v___x_32_, 1);
lean_inc_ref(v_toAddMonoidWithOne_33_);
lean_dec_ref(v___x_32_);
if (lean_obj_tag(v_o_30_) == 0)
{
lean_object* v___x_34_; 
lean_dec_ref(v_toAddMonoidWithOne_33_);
v___x_34_ = lean_apply_1(v_top_29_, v_c_31_);
return v___x_34_;
}
else
{
lean_object* v_toOne_35_; 
lean_dec(v_c_31_);
lean_dec(v_top_29_);
v_toOne_35_ = lean_ctor_get(v_toAddMonoidWithOne_33_, 2);
lean_inc(v_toOne_35_);
lean_dec_ref(v_toAddMonoidWithOne_33_);
return v_toOne_35_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo___redArg___boxed(lean_object* v_inst_36_, lean_object* v_top_37_, lean_object* v_o_38_, lean_object* v_c_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_DworkPowerSeriesWeights_spCo___redArg(v_inst_36_, v_top_37_, v_o_38_, v_c_39_);
lean_dec(v_o_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo(lean_object* v_R_41_, lean_object* v_inst_42_, lean_object* v_m_43_, lean_object* v_p_44_, lean_object* v_top_45_, lean_object* v_o_46_, lean_object* v_c_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_DworkPowerSeriesWeights_spCo___redArg(v_inst_42_, v_top_45_, v_o_46_, v_c_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_spCo___boxed(lean_object* v_R_49_, lean_object* v_inst_50_, lean_object* v_m_51_, lean_object* v_p_52_, lean_object* v_top_53_, lean_object* v_o_54_, lean_object* v_c_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_Formalism_DworkPowerSeriesWeights_spCo(v_R_49_, v_inst_50_, v_m_51_, v_p_52_, v_top_53_, v_o_54_, v_c_55_);
lean_dec(v_o_54_);
lean_dec(v_p_52_);
lean_dec(v_m_51_);
return v_res_56_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_Special(uint8_t builtin) {
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
res = initialize_tree_Formalism_GaussJetBounds_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
