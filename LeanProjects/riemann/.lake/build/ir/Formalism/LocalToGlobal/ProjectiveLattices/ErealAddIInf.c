// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
// Imports: public import Init public meta import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG___redArg___lam__0(lean_object* v_m_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_toFun_3_);
lean_dec_ref(v_x_2_);
v___x_4_ = lean_apply_1(v_toFun_3_, v_m_1_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG___redArg(lean_object* v_m_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_cfG___redArg___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v_m_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG(lean_object* v_R_7_, lean_object* v_M_8_, lean_object* v_inst_9_, lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_m_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_cfG___redArg___lam__0), 2, 1);
lean_closure_set(v___f_14_, 0, v_m_13_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_cfG___boxed(lean_object* v_R_15_, lean_object* v_M_16_, lean_object* v_inst_17_, lean_object* v_K_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_m_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_L2_Pj_cfG(v_R_15_, v_M_16_, v_inst_17_, v_K_18_, v_inst_19_, v_inst_20_, v_m_21_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_17_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
