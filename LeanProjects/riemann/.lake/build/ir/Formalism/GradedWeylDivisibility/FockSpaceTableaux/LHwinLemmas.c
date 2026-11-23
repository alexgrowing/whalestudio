// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementB
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
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwinHt___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwinHt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwinHt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwinHt___redArg(lean_object* v_v_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v___x_3_; 
v_fst_2_ = lean_ctor_get(v_v_1_, 0);
lean_inc(v_fst_2_);
lean_dec_ref(v_v_1_);
v___x_3_ = lean_nat_to_int(v_fst_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwinHt(lean_object* v_r_4_, lean_object* v_n_5_, lean_object* v_v_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_tree_Formalism_GradedWeylDivisibility_lhwinHt___redArg(v_v_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwinHt___boxed(lean_object* v_r_8_, lean_object* v_n_9_, lean_object* v_v_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_GradedWeylDivisibility_lhwinHt(v_r_8_, v_n_9_, v_v_10_);
lean_dec(v_n_9_);
lean_dec(v_r_8_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
