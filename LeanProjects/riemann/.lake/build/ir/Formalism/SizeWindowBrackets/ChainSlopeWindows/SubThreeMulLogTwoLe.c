// Lean compiler output
// Module: Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LErr_modelC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_LErr_modelC(lean_object* v_cHH_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_3_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_2_);
lean_ctor_set(v___x_3_, 2, v___x_2_);
lean_ctor_set(v___x_3_, 3, v___x_2_);
lean_ctor_set(v___x_3_, 4, v___x_2_);
lean_ctor_set(v___x_3_, 5, v___x_2_);
lean_ctor_set(v___x_3_, 6, v___x_2_);
lean_ctor_set(v___x_3_, 7, v___x_2_);
lean_ctor_set(v___x_3_, 8, v___x_2_);
lean_ctor_set(v___x_3_, 9, v_cHH_1_);
return v___x_3_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
