// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SpecDet
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
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cv___redArg(lean_object* v_00_u03c3_1_, lean_object* v_x_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_x_2_, v_i_3_);
v___x_5_ = lean_apply_1(v_00_u03c3_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cv(lean_object* v_K_6_, lean_object* v_inst_7_, lean_object* v_d_8_, lean_object* v_00_u03c3_9_, lean_object* v_x_10_, lean_object* v_i_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_DivisionValues_cv___redArg(v_00_u03c3_9_, v_x_10_, v_i_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cv___boxed(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_d_15_, lean_object* v_00_u03c3_16_, lean_object* v_x_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_DivisionValues_cv(v_K_13_, v_inst_14_, v_d_15_, v_00_u03c3_16_, v_x_17_, v_i_18_);
lean_dec(v_d_15_);
lean_dec_ref(v_inst_14_);
return v_res_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet(uint8_t builtin) {
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
