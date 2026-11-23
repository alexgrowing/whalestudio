// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementE
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementA public import Formalism.GaussJetBounds.StatementC
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
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_frameTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___redArg(lean_object* v_d_1_, lean_object* v_TT_2_, lean_object* v_y_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_fst_4_ = lean_ctor_get(v_y_3_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_y_3_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_y_3_);
v___x_6_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_6_, 0, v_d_1_);
v___x_7_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_6_, v_fst_4_, v_TT_2_);
if (v___x_7_ == 0)
{
lean_dec(v_snd_5_);
return v___x_7_;
}
else
{
lean_object* v_fst_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_fst_8_ = lean_ctor_get(v_snd_5_, 0);
lean_inc(v_fst_8_);
lean_dec(v_snd_5_);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_dec_eq(v_fst_8_, v___x_9_);
lean_dec(v_fst_8_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___redArg___boxed(lean_object* v_d_11_, lean_object* v_TT_12_, lean_object* v_y_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___redArg(v_d_11_, v_TT_12_, v_y_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_frameTop(lean_object* v_d_16_, lean_object* v_N0_17_, lean_object* v_N1_18_, lean_object* v_TT_19_, lean_object* v_y_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___redArg(v_d_16_, v_TT_19_, v_y_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameTop___boxed(lean_object* v_d_22_, lean_object* v_N0_23_, lean_object* v_N1_24_, lean_object* v_TT_25_, lean_object* v_y_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = lp_tree_Formalism_DworkPowerSeriesWeights_frameTop(v_d_22_, v_N0_23_, v_N1_24_, v_TT_25_, v_y_26_);
lean_dec(v_N1_24_);
lean_dec(v_N0_23_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementE(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
