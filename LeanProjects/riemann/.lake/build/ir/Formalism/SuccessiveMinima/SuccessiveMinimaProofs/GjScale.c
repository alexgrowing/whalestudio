// Lean compiler output
// Module: Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale
// Imports: public import Init public meta import Init public import Formalism.SuccessiveMinima.DefsMink
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
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb___redArg(lean_object* v_j_1_, lean_object* v_u_2_, lean_object* v_y_3_, lean_object* v_i_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_i_4_, v_j_1_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
lean_dec(v_u_2_);
v___x_6_ = lean_apply_1(v_y_3_, v_i_4_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
lean_dec(v_y_3_);
v___x_7_ = lean_apply_1(v_u_2_, v_i_4_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb___redArg___boxed(lean_object* v_j_8_, lean_object* v_u_9_, lean_object* v_y_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_FN_GjScaling_emb___redArg(v_j_8_, v_u_9_, v_y_10_, v_i_11_);
lean_dec(v_j_8_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb(lean_object* v_n_13_, lean_object* v_j_14_, lean_object* v_u_15_, lean_object* v_y_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_FN_GjScaling_emb___redArg(v_j_14_, v_u_15_, v_y_16_, v_i_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_GjScaling_emb___boxed(lean_object* v_n_19_, lean_object* v_j_20_, lean_object* v_u_21_, lean_object* v_y_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_FN_GjScaling_emb(v_n_19_, v_j_20_, v_u_21_, v_y_22_, v_i_23_);
lean_dec(v_j_20_);
lean_dec(v_n_19_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_DefsMink(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_DefsMink(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
