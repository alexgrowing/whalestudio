// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.DetShiftShW
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
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
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___redArg___lam__0(lean_object* v_l_1_, lean_object* v_c_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_l_1_, v_i_3_);
v___x_5_ = lean_int_sub(v___x_4_, v_c_2_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed(lean_object* v_l_6_, lean_object* v_c_7_, lean_object* v_i_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_L2_Forms_shW___redArg___lam__0(v_l_6_, v_c_7_, v_i_8_);
lean_dec(v_c_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___redArg(lean_object* v_l_10_, lean_object* v_c_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_12_, 0, v_l_10_);
lean_closure_set(v___f_12_, 1, v_c_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW(lean_object* v_N_13_, lean_object* v_l_14_, lean_object* v_c_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_16_, 0, v_l_14_);
lean_closure_set(v___f_16_, 1, v_c_15_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_shW___boxed(lean_object* v_N_17_, lean_object* v_l_18_, lean_object* v_c_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_Forms_shW(v_N_17_, v_l_18_, v_c_19_);
lean_dec(v_N_17_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_IsLocBasis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_DetShiftShW(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_IsLocBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
