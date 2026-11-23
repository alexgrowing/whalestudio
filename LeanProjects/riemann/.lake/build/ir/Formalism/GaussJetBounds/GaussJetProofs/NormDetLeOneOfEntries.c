// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Formalism.GaussJetBounds.StatementD
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
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__0(lean_object* v_blk_1_, lean_object* v_k_2_, lean_object* v_inst_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_apply_1(v_blk_1_, v_a_4_);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_k_2_);
v___x_7_ = l_Option_instDecidableEq___redArg(v_inst_3_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__0___boxed(lean_object* v_blk_8_, lean_object* v_k_9_, lean_object* v_inst_10_, lean_object* v_a_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__0(v_blk_8_, v_k_9_, v_inst_10_, v_a_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__1(lean_object* v_toFun_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_1(v_toFun_14_, v___y_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg(lean_object* v_inst_17_, lean_object* v_blk_18_, lean_object* v_k_19_, lean_object* v_mono_20_){
_start:
{
lean_object* v___x_21_; lean_object* v_support_22_; lean_object* v_toFun_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_21_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v_support_22_ = lean_ctor_get(v_mono_20_, 0);
lean_inc(v_support_22_);
v_toFun_23_ = lean_ctor_get(v_mono_20_, 1);
lean_inc(v_toFun_23_);
lean_dec_ref(v_mono_20_);
v___f_24_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_24_, 0, v_blk_18_);
lean_closure_set(v___f_24_, 1, v_k_19_);
lean_closure_set(v___f_24_, 2, v_inst_17_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg___lam__1), 2, 1);
lean_closure_set(v___f_25_, 0, v_toFun_23_);
v___x_26_ = lp_mathlib_Multiset_filter___redArg(v___f_24_, v_support_22_);
v___x_27_ = lp_mathlib_Finset_sum___redArg(v___x_21_, v___x_26_, v___f_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_bdeg(lean_object* v_00_u03c3_28_, lean_object* v_00_u03ba_29_, lean_object* v_inst_30_, lean_object* v_blk_31_, lean_object* v_k_32_, lean_object* v_mono_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_DworkPowerSeriesWeights_bdeg___redArg(v_inst_30_, v_blk_31_, v_k_32_, v_mono_33_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementD(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries(uint8_t builtin) {
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
res = initialize_tree_Formalism_GaussJetBounds_StatementD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
