// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetdomLemmas
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
lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowDeg___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowPart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowTot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__0(lean_object* v_k_1_, lean_object* v_a_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_a_2_, v_k_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__0___boxed(lean_object* v_k_4_, lean_object* v_a_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__0(v_k_4_, v_a_5_);
lean_dec(v_a_5_);
lean_dec(v_k_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__1(lean_object* v_n_8_, lean_object* v_m_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_tree_Formalism_GradedWeylDivisibility_rowDeg___redArg(v_n_8_, v_m_9_, v_a_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowPart(lean_object* v_r_12_, lean_object* v_n_13_, lean_object* v_k_14_, lean_object* v_m_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v_k_14_);
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__1), 3, 2);
lean_closure_set(v___f_17_, 0, v_n_13_);
lean_closure_set(v___f_17_, 1, v_m_15_);
v___x_18_ = l_List_finRange(v_r_12_);
v___x_19_ = lp_mathlib_Multiset_filter___redArg(v___f_16_, v___x_18_);
v___x_20_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_19_, v___f_17_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_rowTot(lean_object* v_r_21_, lean_object* v_n_22_, lean_object* v_m_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___f_24_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_rowPart___lam__1), 3, 2);
lean_closure_set(v___f_24_, 0, v_n_22_);
lean_closure_set(v___f_24_, 1, v_m_23_);
v___x_25_ = l_List_finRange(v_r_21_);
v___x_26_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_25_, v___f_24_);
return v___x_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas(uint8_t builtin) {
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
