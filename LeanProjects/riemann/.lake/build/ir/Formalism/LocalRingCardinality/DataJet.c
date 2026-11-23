// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataJet
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.LocalRingCardinality.DataHost
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
lean_object* lp_mathlib_Finsupp_sum___at___00Finsupp_multinomial_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BasicNotions_JetTdeg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_JetTdeg___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_BasicNotions_JetTdeg___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg___lam__0(lean_object* v_x_1_, lean_object* v_k_2_){
_start:
{
lean_inc(v_k_2_);
return v_k_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg___lam__0___boxed(lean_object* v_x_3_, lean_object* v_k_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_BasicNotions_JetTdeg___redArg___lam__0(v_x_3_, v_k_4_);
lean_dec(v_k_4_);
lean_dec(v_x_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg___redArg(lean_object* v_m_7_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_9_; 
v___f_8_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_JetTdeg___redArg___closed__0));
v___x_9_ = lp_mathlib_Finsupp_sum___at___00Finsupp_multinomial_spec__0___redArg(v_m_7_, v___f_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_JetTdeg(lean_object* v_00_u03c3_10_, lean_object* v_m_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_BasicNotions_JetTdeg___redArg(v_m_11_);
return v___x_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataHost(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataJet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataHost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
