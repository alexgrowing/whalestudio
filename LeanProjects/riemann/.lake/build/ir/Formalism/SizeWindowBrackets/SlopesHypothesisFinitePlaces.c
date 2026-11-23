// Lean compiler output
// Module: Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HarderNarasimhan.StatementPl public import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
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
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_slopeLatticeData_locScal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_slopeLatticeData_locScal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_slopeLatticeData_locScal(lean_object* v_K_1_, lean_object* v_V_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_w_8_, lean_object* v_inst_9_, lean_object* v_c_10_, lean_object* v_L_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_slopeLatticeData_locScal___boxed(lean_object* v_K_13_, lean_object* v_V_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_w_20_, lean_object* v_inst_21_, lean_object* v_c_22_, lean_object* v_L_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_LFunctionChainParameters_slopeLatticeData_locScal(v_K_13_, v_V_14_, v_inst_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_w_20_, v_inst_21_, v_c_22_, v_L_23_);
lean_dec(v_c_22_);
lean_dec(v_inst_21_);
lean_dec(v_inst_19_);
lean_dec(v_inst_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_15_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_StatementPl(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(uint8_t builtin) {
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
res = initialize_tree_Formalism_HarderNarasimhan_StatementPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
