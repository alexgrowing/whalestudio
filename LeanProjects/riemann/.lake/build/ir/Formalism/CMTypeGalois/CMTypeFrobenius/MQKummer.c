// Lean compiler output
// Module: Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.CMTypeGalois.StatementField
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
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_mqkField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_mqkField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_mqkField(lean_object* v_E_1_, lean_object* v_inst_2_, lean_object* v_F_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_k_6_, lean_object* v_00_u03b1_7_, lean_object* v_T_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_Q3_mqkField___boxed(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_F_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_k_15_, lean_object* v_00_u03b1_16_, lean_object* v_T_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_Q3_mqkField(v_E_10_, v_inst_11_, v_F_12_, v_inst_13_, v_inst_14_, v_k_15_, v_00_u03b1_16_, v_T_17_);
lean_dec(v_T_17_);
lean_dec(v_00_u03b1_16_);
lean_dec(v_k_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_CMTypeGalois_StatementField(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer(uint8_t builtin) {
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
res = initialize_tree_Formalism_CMTypeGalois_StatementField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
