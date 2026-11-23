// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.EigenRatHermLcv
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
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
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_extSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_extSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_simEig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_simEig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_extSpan(lean_object* v_K_1_, lean_object* v_00_u03a9_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_n_5_, lean_object* v_j_6_, lean_object* v_Z_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_extSpan___boxed(lean_object* v_K_9_, lean_object* v_00_u03a9_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_n_13_, lean_object* v_j_14_, lean_object* v_Z_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_DivisionValues_extSpan(v_K_9_, v_00_u03a9_10_, v_inst_11_, v_inst_12_, v_n_13_, v_j_14_, v_Z_15_);
lean_dec(v_j_14_);
lean_dec(v_n_13_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_simEig(lean_object* v_K_17_, lean_object* v_00_u03a9_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_n_21_, lean_object* v_j_22_, lean_object* v_00_U0001d4af_23_, lean_object* v_00_u03c7_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_simEig___boxed(lean_object* v_K_26_, lean_object* v_00_u03a9_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_n_30_, lean_object* v_j_31_, lean_object* v_00_U0001d4af_32_, lean_object* v_00_u03c7_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_DivisionValues_simEig(v_K_26_, v_00_u03a9_27_, v_inst_28_, v_inst_29_, v_n_30_, v_j_31_, v_00_U0001d4af_32_, v_00_u03c7_33_);
lean_dec(v_00_u03c7_33_);
lean_dec(v_j_31_);
lean_dec(v_n_30_);
lean_dec_ref(v_inst_29_);
lean_dec_ref(v_inst_28_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_EigenRatHermLcv(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
