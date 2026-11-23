// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.UJLocCompact public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix
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
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coeMatrixAlt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coeMatrixAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coeMatrixAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coeMatrixAlt___redArg(lean_object* v_g_1_, lean_object* v_a_2_, lean_object* v_a_3_){
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
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coeMatrixAlt(lean_object* v_n_6_, lean_object* v_00_u03b5_7_, lean_object* v_g_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_tree_Formalism_REAL_coeMatrixAlt___redArg(v_g_8_, v_a_9_, v_a_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_coeMatrixAlt___boxed(lean_object* v_n_12_, lean_object* v_00_u03b5_13_, lean_object* v_g_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_REAL_coeMatrixAlt(v_n_12_, v_00_u03b5_13_, v_g_14_, v_a_15_, v_a_16_);
lean_dec_ref(v_00_u03b5_13_);
lean_dec(v_n_12_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_UJLocCompact(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_UJLocCompact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
