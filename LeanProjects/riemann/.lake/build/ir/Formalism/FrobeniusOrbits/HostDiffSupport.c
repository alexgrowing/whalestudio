// Lean compiler output
// Module: Formalism.FrobeniusOrbits.HostDiffSupport
// Imports: public import Init public meta import Init public import Formalism.FrobeniusOrbits.Statement
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
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_KinE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_KinE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_KinE(lean_object* v_L_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_00_u03b6_4_, lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_KinE___boxed(lean_object* v_L_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_00_u03b6_11_, lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_FrobeniusOrbits_KinE(v_L_8_, v_inst_9_, v_inst_10_, v_00_u03b6_11_, v_a_12_, v_b_13_);
lean_dec(v_b_13_);
lean_dec(v_a_12_);
lean_dec(v_00_u03b6_11_);
lean_dec_ref(v_inst_10_);
lean_dec_ref(v_inst_9_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostDiffSupport(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
