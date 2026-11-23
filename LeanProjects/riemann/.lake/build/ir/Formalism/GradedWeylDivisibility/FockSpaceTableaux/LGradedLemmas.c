// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementB public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___redArg(lean_object* v_a_1_, lean_object* v_v_2_){
_start:
{
lean_object* v_fst_3_; uint8_t v___x_4_; 
v_fst_3_ = lean_ctor_get(v_v_2_, 0);
v___x_4_ = lean_nat_dec_eq(v_fst_3_, v_a_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(0u);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(1u);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___redArg___boxed(lean_object* v_a_7_, lean_object* v_v_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___redArg(v_a_7_, v_v_8_);
lean_dec_ref(v_v_8_);
lean_dec(v_a_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa(lean_object* v_r_10_, lean_object* v_n_11_, lean_object* v_a_12_, lean_object* v_v_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___redArg(v_a_12_, v_v_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa___boxed(lean_object* v_r_15_, lean_object* v_n_16_, lean_object* v_a_17_, lean_object* v_v_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_GradedWeylDivisibility_lgraded__wa(v_r_15_, v_n_16_, v_a_17_, v_v_18_);
lean_dec_ref(v_v_18_);
lean_dec(v_a_17_);
lean_dec(v_n_16_);
lean_dec(v_r_15_);
return v_res_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementB(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
