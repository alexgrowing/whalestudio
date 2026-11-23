// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Formalism.GaussJetBounds.StatementA public import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd
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
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v_fst_7_ = lean_ctor_get(v_val_6_, 0);
lean_inc(v_fst_7_);
v_snd_8_ = lean_ctor_get(v_val_6_, 1);
lean_inc(v_snd_8_);
lean_dec(v_val_6_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_fst_7_, v_snd_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter(lean_object* v_d_10_, lean_object* v_motive_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_14_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_apply_1(v_h__1_13_, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v_val_17_; lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_13_);
v_val_17_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_x_12_, 1);
v_fst_18_ = lean_ctor_get(v_val_17_, 0);
lean_inc(v_fst_18_);
v_snd_19_ = lean_ctor_get(v_val_17_, 1);
lean_inc(v_snd_19_);
lean_dec(v_val_17_);
v___x_20_ = lean_apply_2(v_h__2_14_, v_fst_18_, v_snd_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter___boxed(lean_object* v_d_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree___private_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity_0__Formalism_DworkPowerSeriesWeights_asmA__cost_match__1_splitter(v_d_21_, v_motive_22_, v_x_23_, v_h__1_24_, v_h__2_25_);
lean_dec(v_d_21_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementA(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity(uint8_t builtin) {
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
res = initialize_tree_Formalism_GaussJetBounds_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
