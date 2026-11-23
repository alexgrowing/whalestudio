// Lean compiler output
// Module: Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.Statement public import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem public import Formalism.TameInertiaTowers.CentralOrderTwo.DecompositionSubgroupIndex
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
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___redArg(lean_object* v_b_1_){
_start:
{
lean_inc(v_b_1_);
return v_b_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___redArg___boxed(lean_object* v_b_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___redArg(v_b_2_);
lean_dec(v_b_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK(lean_object* v_L_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_b_7_){
_start:
{
lean_inc(v_b_7_);
return v_b_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_SplitK_bK___boxed(lean_object* v_L_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_b_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_FrobeniusOrbits_SplitK_bK(v_L_8_, v_inst_9_, v_inst_10_, v_b_11_);
lean_dec(v_b_11_);
lean_dec_ref(v_inst_9_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
