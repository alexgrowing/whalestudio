// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum___redArg___lam__0(lean_object* v_w_1_, lean_object* v_x_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_nat_to_int(v_k_3_);
v___x_5_ = lean_apply_1(v_w_1_, v_x_2_);
v___x_6_ = lean_int_mul(v___x_4_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg___lam__0(lean_object* v_toFun_7_, lean_object* v_g_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_inc(v_a_9_);
v___x_10_ = lean_apply_1(v_toFun_7_, v_a_9_);
v___x_11_ = lean_apply_2(v_g_8_, v_a_9_, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1(lean_object* v_s_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__0));
v___x_17_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1___closed__1);
v___x_18_ = l_List_foldrTR___redArg(v___f_16_, v___x_17_, v_s_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0___redArg(lean_object* v_s_19_, lean_object* v_f_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lp_mathlib_Multiset_map___redArg(v_f_20_, v_s_19_);
v___x_22_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0_spec__1(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg(lean_object* v_f_23_, lean_object* v_g_24_){
_start:
{
lean_object* v_support_25_; lean_object* v_toFun_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
v_support_25_ = lean_ctor_get(v_f_23_, 0);
lean_inc(v_support_25_);
v_toFun_26_ = lean_ctor_get(v_f_23_, 1);
lean_inc(v_toFun_26_);
lean_dec_ref(v_f_23_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_27_, 0, v_toFun_26_);
lean_closure_set(v___f_27_, 1, v_g_24_);
v___x_28_ = lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0___redArg(v_support_25_, v___f_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum___redArg(lean_object* v_w_29_, lean_object* v_n_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; 
v___f_31_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_31_, 0, v_w_29_);
v___x_32_ = lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg(v_n_30_, v___f_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum(lean_object* v_00_u03b9_33_, lean_object* v_w_34_, lean_object* v_n_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum___redArg(v_w_34_, v_n_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0(lean_object* v_00_u03b1_37_, lean_object* v_f_38_, lean_object* v_g_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_tree_Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0___redArg(v_f_38_, v_g_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0(lean_object* v_00_u03b9_41_, lean_object* v_s_42_, lean_object* v_f_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_Finset_sum___at___00Finsupp_sum___at___00Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_wsum_spec__0_spec__0___redArg(v_s_42_, v_f_43_);
return v___x_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero(uint8_t builtin) {
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
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
