// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.MemWmPerp
// Imports: public import Init public meta import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmPerp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmPerp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmZ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmZ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmPerp(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_V_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_B_7_, lean_object* v_A_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmPerp___boxed(lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_V_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_B_16_, lean_object* v_A_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Col_wmPerp(v_K_10_, v_inst_11_, v_inst_12_, v_V_13_, v_inst_14_, v_inst_15_, v_B_16_, v_A_17_);
lean_dec(v_B_16_);
lean_dec(v_inst_15_);
lean_dec_ref(v_inst_14_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmZ(lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_V_22_, lean_object* v_W_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_B_28_, lean_object* v_V_u2080_29_, lean_object* v_00_u03b8_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmZ___boxed(lean_object* v_K_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_V_35_, lean_object* v_W_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_B_41_, lean_object* v_V_u2080_42_, lean_object* v_00_u03b8_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_L2_Col_wmZ(v_K_32_, v_inst_33_, v_inst_34_, v_V_35_, v_W_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_B_41_, v_V_u2080_42_, v_00_u03b8_43_);
lean_dec(v_00_u03b8_43_);
lean_dec(v_B_41_);
lean_dec(v_inst_40_);
lean_dec_ref(v_inst_39_);
lean_dec(v_inst_38_);
lean_dec_ref(v_inst_37_);
lean_dec(v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_MemWmPerp(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
