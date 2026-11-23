// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.ClassSumBridge
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_toMul_2_, lean_object* v_x_3_, lean_object* v_y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_inst_1_, v_x_3_);
v___x_6_ = lean_apply_2(v_toMul_2_, v___x_5_, v_y_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg(lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toSemiring_11_; lean_object* v___x_12_; lean_object* v_toMul_13_; lean_object* v___f_14_; lean_object* v___f_15_; 
v___x_9_ = lp_mathlib_Field_toSemifield___redArg(v_inst_7_);
v___x_10_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_9_);
v_toSemiring_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_ref(v_toSemiring_11_);
lean_dec_ref(v___x_10_);
v___x_12_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_11_);
v_toMul_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_toMul_13_);
lean_dec_ref(v___x_12_);
v___f_14_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg___lam__0), 4, 2);
lean_closure_set(v___f_14_, 0, v_inst_8_);
lean_closure_set(v___f_14_, 1, v_toMul_13_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0), 3, 1);
lean_closure_set(v___f_15_, 0, v___f_14_);
return v___f_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg___boxed(lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg(v_inst_16_, v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne(lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_tree_Formalism_L2_DIV_CSD_pairOne___redArg(v_inst_20_, v_inst_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_pairOne___boxed(lean_object* v_K_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_L2_DIV_CSD_pairOne(v_K_23_, v_inst_24_, v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ClassSumBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
