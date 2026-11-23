// Lean compiler output
// Module: Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
// Imports: public import Init public meta import Init public import Formalism.TorsionNormIteration.InvIntegralOfClass
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
LEAN_EXPORT lean_object* lp_tree_Formalism_LT_FrobP_liftO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LT_FrobP_liftO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LT_FrobP_liftO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LT_FrobP_liftO___redArg(lean_object* v_A_1_, lean_object* v_d_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_A_1_, v_d_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LT_FrobP_liftO(lean_object* v_K_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_00_u03b9_7_, lean_object* v_A_8_, lean_object* v_hA_9_, lean_object* v_d_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_apply_1(v_A_8_, v_d_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LT_FrobP_liftO___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03b9_15_, lean_object* v_A_16_, lean_object* v_hA_17_, lean_object* v_d_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_LT_FrobP_liftO(v_K_12_, v_inst_13_, v_inst_14_, v_00_u03b9_15_, v_A_16_, v_hA_17_, v_d_18_);
lean_dec_ref(v_inst_13_);
return v_res_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_TorsionNormIteration_InvIntegralOfClass(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TorsionNormIteration_InvIntegralOfClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
