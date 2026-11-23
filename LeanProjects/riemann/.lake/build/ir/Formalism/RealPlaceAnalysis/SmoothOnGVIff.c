// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.SmoothOnGVIff
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower public import Formalism.RealPlaceAnalysis.StatementD
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
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_KG(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_KG___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toMK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toMK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toMK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_KG(lean_object* v_n_1_, lean_object* v_00_u03b5_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_KG___boxed(lean_object* v_n_4_, lean_object* v_00_u03b5_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_REAL_KG(v_n_4_, v_00_u03b5_5_);
lean_dec_ref(v_00_u03b5_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toMK___redArg(lean_object* v_k_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_val_10_; lean_object* v___x_11_; 
v_val_10_ = lean_ctor_get(v_k_7_, 0);
lean_inc(v_val_10_);
lean_dec_ref(v_k_7_);
v___x_11_ = lean_apply_2(v_val_10_, v_a_8_, v_a_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toMK(lean_object* v_n_12_, lean_object* v_00_u03b5_13_, lean_object* v_k_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_val_17_; lean_object* v___x_18_; 
v_val_17_ = lean_ctor_get(v_k_14_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v_k_14_);
v___x_18_ = lean_apply_2(v_val_17_, v_a_15_, v_a_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_toMK___boxed(lean_object* v_n_19_, lean_object* v_00_u03b5_20_, lean_object* v_k_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_REAL_toMK(v_n_19_, v_00_u03b5_20_, v_k_21_, v_a_22_, v_a_23_);
lean_dec_ref(v_00_u03b5_20_);
lean_dec(v_n_19_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementD(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_SmoothOnGVIff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
