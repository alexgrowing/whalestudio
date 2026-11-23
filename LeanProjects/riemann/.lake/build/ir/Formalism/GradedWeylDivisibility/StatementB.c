// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.StatementB
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementA
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
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00Nat_multinomial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sum___at___00Finset_sum___at___00bernoulli_x27_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_GradedWeylDivisibility_fockQ_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_GradedWeylDivisibility_fockQ_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0___redArg(lean_object* v_m_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_toFun_3_);
lean_dec_ref(v_p_2_);
v___x_4_ = lean_apply_1(v_toFun_3_, v_m_1_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0(lean_object* v_00_u03c3_5_, lean_object* v_m_6_, lean_object* v_p_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0___redArg(v_m_6_, v_p_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___redArg(lean_object* v_p_9_){
_start:
{
lean_object* v_support_10_; 
v_support_10_ = lean_ctor_get(v_p_9_, 0);
lean_inc(v_support_10_);
return v_support_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___redArg___boxed(lean_object* v_p_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___redArg(v_p_11_);
lean_dec_ref(v_p_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1(lean_object* v_00_u03c3_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_support_15_; 
v_support_15_ = lean_ctor_get(v_p_14_, 0);
lean_inc(v_support_15_);
return v_support_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1___boxed(lean_object* v_00_u03c3_16_, lean_object* v_p_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_MvPolynomial_support___at___00Formalism_GradedWeylDivisibility_fockQ_spec__1(v_00_u03c3_16_, v_p_17_);
lean_dec_ref(v_p_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg___lam__0(lean_object* v_toFun_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_apply_1(v_toFun_19_, v_k_20_);
v___x_22_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_21_);
lean_dec(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg___lam__1(lean_object* v_f_23_, lean_object* v_g_24_, lean_object* v_m_25_){
_start:
{
lean_object* v_support_26_; lean_object* v_toFun_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_support_26_ = lean_ctor_get(v_m_25_, 0);
lean_inc(v_support_26_);
v_toFun_27_ = lean_ctor_get(v_m_25_, 1);
lean_inc_ref(v_m_25_);
v___x_28_ = lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0___redArg(v_m_25_, v_f_23_);
lean_inc(v_toFun_27_);
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg___lam__0), 2, 1);
lean_closure_set(v___f_29_, 0, v_toFun_27_);
v___x_30_ = lp_tree_MvPolynomial_coeff___at___00Formalism_GradedWeylDivisibility_fockQ_spec__0___redArg(v_m_25_, v_g_24_);
v___x_31_ = l_Rat_mul(v___x_28_, v___x_30_);
lean_dec_ref(v___x_28_);
v___x_32_ = lp_mathlib_Finset_prod___at___00Nat_multinomial_spec__1___redArg(v_support_26_, v___f_29_);
v___x_33_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_32_);
v___x_34_ = l_Rat_mul(v___x_31_, v___x_33_);
lean_dec_ref(v___x_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_GradedWeylDivisibility_fockQ_spec__2___redArg(lean_object* v_s_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lp_mathlib_Multiset_map___redArg(v_f_36_, v_s_35_);
v___x_38_ = lp_mathlib_Multiset_sum___at___00Finset_sum___at___00bernoulli_x27_spec__1_spec__2(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg(lean_object* v_f_39_, lean_object* v_g_40_){
_start:
{
lean_object* v_support_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v_support_41_ = lean_ctor_get(v_f_39_, 0);
lean_inc(v_support_41_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg___lam__1), 3, 2);
lean_closure_set(v___f_42_, 0, v_f_39_);
lean_closure_set(v___f_42_, 1, v_g_40_);
v___x_43_ = lp_tree_Finset_sum___at___00Formalism_GradedWeylDivisibility_fockQ_spec__2___redArg(v_support_41_, v___f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_fockQ(lean_object* v_00_u03c3_44_, lean_object* v_f_45_, lean_object* v_g_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_GradedWeylDivisibility_fockQ___redArg(v_f_45_, v_g_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_GradedWeylDivisibility_fockQ_spec__2(lean_object* v_00_u03b9_48_, lean_object* v_s_49_, lean_object* v_f_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Finset_sum___at___00Formalism_GradedWeylDivisibility_fockQ_spec__2___redArg(v_s_49_, v_f_50_);
return v___x_51_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
