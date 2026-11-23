// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementA public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW___redArg(lean_object* v_s_1_, lean_object* v_t_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_t_2_, v_s_1_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(0u);
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(1u);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW___redArg___boxed(lean_object* v_s_6_, lean_object* v_t_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_GradedWeylDivisibility_initW___redArg(v_s_6_, v_t_7_);
lean_dec(v_t_7_);
lean_dec(v_s_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW(lean_object* v_n_9_, lean_object* v_s_10_, lean_object* v_t_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_GradedWeylDivisibility_initW___redArg(v_s_10_, v_t_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_initW___boxed(lean_object* v_n_13_, lean_object* v_s_14_, lean_object* v_t_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_GradedWeylDivisibility_initW(v_n_13_, v_s_14_, v_t_15_);
lean_dec(v_t_15_);
lean_dec(v_s_14_);
lean_dec(v_n_13_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
