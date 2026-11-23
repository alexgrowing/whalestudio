// Lean compiler output
// Module: Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.LatticeGeometry.CompNe public import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
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
lean_object* lp_tree_Formalism_L2_Geo_datW___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw___redArg(lean_object* v_D_1_, lean_object* v_F_2_, lean_object* v_j_3_){
_start:
{
lean_object* v_00_u03bag_4_; lean_object* v_U_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_00_u03bag_4_ = lean_ctor_get(v_F_2_, 1);
lean_inc(v_00_u03bag_4_);
v_U_5_ = lean_ctor_get(v_F_2_, 4);
lean_inc_ref(v_U_5_);
lean_dec_ref(v_F_2_);
v___x_6_ = lp_tree_Formalism_L2_Geo_datW___redArg(v_D_1_, v_00_u03bag_4_, v_j_3_);
v___x_7_ = lean_apply_1(v_U_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw___redArg___boxed(lean_object* v_D_8_, lean_object* v_F_9_, lean_object* v_j_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_L2_Geo_ShimFam_Uw___redArg(v_D_8_, v_F_9_, v_j_10_);
lean_dec(v_j_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw(lean_object* v_D_12_, lean_object* v_G_13_, lean_object* v_Lev_14_, lean_object* v_F_15_, lean_object* v_j_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_L2_Geo_ShimFam_Uw___redArg(v_D_12_, v_F_15_, v_j_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Geo_ShimFam_Uw___boxed(lean_object* v_D_18_, lean_object* v_G_19_, lean_object* v_Lev_20_, lean_object* v_F_21_, lean_object* v_j_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_Geo_ShimFam_Uw(v_D_18_, v_G_19_, v_Lev_20_, v_F_21_, v_j_22_);
lean_dec(v_j_22_);
lean_dec_ref(v_G_19_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_CompNe(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_InstAddCommSemigroupWt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_LevPrPrime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_CompNe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_LatticeGeometry_InstAddCommSemigroupWt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
