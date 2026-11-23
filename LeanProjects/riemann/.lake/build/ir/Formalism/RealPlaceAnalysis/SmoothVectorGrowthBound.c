// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ public import Formalism.RealPlaceAnalysis.SmoothOnG public import Formalism.RealPlaceAnalysis.StatementA
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
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toM___redArg(lean_object* v_g_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_val_4_; lean_object* v___x_5_; 
v_val_4_ = lean_ctor_get(v_g_1_, 0);
lean_inc(v_val_4_);
lean_dec_ref(v_g_1_);
v___x_5_ = lean_apply_2(v_val_4_, v_a_2_, v_a_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toM(lean_object* v_n_6_, lean_object* v_00_u03b5_7_, lean_object* v_g_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_val_11_; lean_object* v___x_12_; 
v_val_11_ = lean_ctor_get(v_g_8_, 0);
lean_inc(v_val_11_);
lean_dec_ref(v_g_8_);
v___x_12_ = lean_apply_2(v_val_11_, v_a_9_, v_a_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toM___boxed(lean_object* v_n_13_, lean_object* v_00_u03b5_14_, lean_object* v_g_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_REAL_toM(v_n_13_, v_00_u03b5_14_, v_g_15_, v_a_16_, v_a_17_);
lean_dec_ref(v_00_u03b5_14_);
lean_dec(v_n_13_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_SmoothOnG(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_SmoothOnG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
