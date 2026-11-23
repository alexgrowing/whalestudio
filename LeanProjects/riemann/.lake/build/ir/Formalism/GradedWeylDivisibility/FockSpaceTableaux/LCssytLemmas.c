// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCssytLemmas
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementC
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
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___redArg(lean_object* v_c_1_, lean_object* v_I_2_, lean_object* v_k_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_2__overap_5_; lean_object* v___x_6_; 
v___x_2__overap_5_ = l_Fin_cases___redArg(v_c_1_, v_I_2_, v_k_3_);
v___x_6_ = lean_apply_1(v___x_2__overap_5_, v_a_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___redArg___boxed(lean_object* v_c_7_, lean_object* v_I_8_, lean_object* v_k_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___redArg(v_c_7_, v_I_8_, v_k_9_, v_a_10_);
lean_dec(v_k_9_);
lean_dec_ref(v_c_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI(lean_object* v_r_12_, lean_object* v_K_13_, lean_object* v_h_14_, lean_object* v_sz_15_, lean_object* v_c_16_, lean_object* v_I_17_, lean_object* v_k_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_6__overap_20_; lean_object* v___x_21_; 
v___x_6__overap_20_ = l_Fin_cases___redArg(v_c_16_, v_I_17_, v_k_18_);
v___x_21_ = lean_apply_1(v___x_6__overap_20_, v_a_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI___boxed(lean_object* v_r_22_, lean_object* v_K_23_, lean_object* v_h_24_, lean_object* v_sz_25_, lean_object* v_c_26_, lean_object* v_I_27_, lean_object* v_k_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_GradedWeylDivisibility_lcssyt__consI(v_r_22_, v_K_23_, v_h_24_, v_sz_25_, v_c_26_, v_I_27_, v_k_28_, v_a_29_);
lean_dec(v_k_28_);
lean_dec_ref(v_c_26_);
lean_dec_ref(v_sz_25_);
lean_dec(v_h_24_);
lean_dec(v_K_23_);
lean_dec(v_r_22_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
