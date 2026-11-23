// Lean compiler output
// Module: Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SubgroupCount
// Imports: public import Init public meta import Init public import Formalism.HyperbolicPlaceProducts.Statement public import Mathlib
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
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_tail___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv___lam__1(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_SLP_P_consEquiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_SLP_P_consEquiv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_SLP_P_consEquiv___closed__0 = (const lean_object*)&lp_tree_Formalism_SLP_P_consEquiv___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv___lam__0(lean_object* v_p_1_, lean_object* v___y_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; 
v_fst_3_ = lean_ctor_get(v_p_1_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_p_1_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_p_1_);
v___x_5_ = l_Fin_cases___redArg(v_fst_3_, v_snd_4_, v___y_2_);
lean_dec(v_fst_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv___lam__0___boxed(lean_object* v_p_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_SLP_P_consEquiv___lam__0(v_p_6_, v___y_7_);
lean_dec(v___y_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv___lam__1(lean_object* v_n_9_, lean_object* v_f_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_n_9_, v___x_11_);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_mod(v___x_13_, v___x_12_);
lean_dec(v___x_12_);
lean_inc_ref(v_f_10_);
v___x_15_ = lean_apply_1(v_f_10_, v___x_14_);
v___x_16_ = lean_alloc_closure((void*)(lp_mathlib_Fin_tail___boxed), 4, 3);
lean_closure_set(v___x_16_, 0, v_n_9_);
lean_closure_set(v___x_16_, 1, lean_box(0));
lean_closure_set(v___x_16_, 2, v_f_10_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_SLP_P_consEquiv(lean_object* v_n_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v___f_20_ = ((lean_object*)(lp_tree_Formalism_SLP_P_consEquiv___closed__0));
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Formalism_SLP_P_consEquiv___lam__1), 2, 1);
lean_closure_set(v___f_21_, 0, v_n_19_);
v___x_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_22_, 0, v___f_21_);
lean_ctor_set(v___x_22_, 1, v___f_20_);
return v___x_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
