// Lean compiler output
// Module: Formalism.SizeWindowBrackets.JointCSlopeExists
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.CutFailsForRSubmodule public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
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
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LJC_posSum___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LJC_posSum___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LJC_posSum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LJC_posSum___lam__0(lean_object* v_e_1_, lean_object* v_t_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_apply_1(v_e_1_, v_i_3_);
v___x_5_ = lean_nat_to_int(v___x_4_);
v___x_6_ = lean_int_sub(v___x_5_, v_t_2_);
lean_dec(v___x_5_);
v___x_7_ = l_Int_toNat(v___x_6_);
lean_dec(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LJC_posSum___lam__0___boxed(lean_object* v_e_8_, lean_object* v_t_9_, lean_object* v_i_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_LFunctionChainParameters_LJC_posSum___lam__0(v_e_8_, v_t_9_, v_i_10_);
lean_dec(v_t_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LJC_posSum(lean_object* v_d_12_, lean_object* v_e_13_, lean_object* v_t_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_LJC_posSum___lam__0___boxed), 3, 2);
lean_closure_set(v___f_15_, 0, v_e_13_);
lean_closure_set(v___f_15_, 1, v_t_14_);
v___x_16_ = l_List_finRange(v_d_12_);
v___x_17_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_16_, v___f_15_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_CutFailsForRSubmodule(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_JointCSlopeExists(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_CutFailsForRSubmodule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
