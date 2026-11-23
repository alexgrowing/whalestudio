// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.TiedTwLv
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.TiedTw
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_PvG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_PvG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_PvG(lean_object* v_D_1_, lean_object* v_u_2_, lean_object* v_C_3_, lean_object* v_A_4_, lean_object* v_res_5_, lean_object* v_v_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_PvG___boxed(lean_object* v_D_8_, lean_object* v_u_9_, lean_object* v_C_10_, lean_object* v_A_11_, lean_object* v_res_12_, lean_object* v_v_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_L2_Forms_PvG(v_D_8_, v_u_9_, v_C_10_, v_A_11_, v_res_12_, v_v_13_);
lean_dec(v_v_13_);
lean_dec(v_res_12_);
lean_dec_ref(v_A_11_);
lean_dec_ref(v_C_10_);
lean_dec(v_u_9_);
lean_dec_ref(v_D_8_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedTw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedTwLv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_TiedTw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
