// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.DivIntoDualShift
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.ProdFormula
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
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_smulLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_smulLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_smulLat(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_d_3_, lean_object* v_a_4_, lean_object* v_N_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_smulLat___boxed(lean_object* v_K_7_, lean_object* v_inst_8_, lean_object* v_d_9_, lean_object* v_a_10_, lean_object* v_N_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_DivisionValues_smulLat(v_K_7_, v_inst_8_, v_d_9_, v_a_10_, v_N_11_);
lean_dec(v_a_10_);
lean_dec(v_d_9_);
lean_dec_ref(v_inst_8_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_DivIntoDualShift(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
