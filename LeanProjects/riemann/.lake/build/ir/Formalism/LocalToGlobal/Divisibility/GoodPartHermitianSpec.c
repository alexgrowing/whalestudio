// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.ClassSum
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_lvlPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_lvlPart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_lvlPart(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_S_5_, lean_object* v_G_6_, lean_object* v_inst_7_, lean_object* v_r_8_, lean_object* v_P_9_, lean_object* v_00_u03c8_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_lvlPart___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_S_16_, lean_object* v_G_17_, lean_object* v_inst_18_, lean_object* v_r_19_, lean_object* v_P_20_, lean_object* v_00_u03c8_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_DIV_CSD_lvlPart(v_K_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_S_16_, v_G_17_, v_inst_18_, v_r_19_, v_P_20_, v_00_u03c8_21_);
lean_dec_ref(v_00_u03c8_21_);
lean_dec(v_r_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_S_16_);
lean_dec(v_inst_15_);
lean_dec_ref(v_inst_13_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ClassSum(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_ClassSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
