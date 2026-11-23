// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.CompData
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
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
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ___redArg___lam__0(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_apply_1(v_a_1_, v_x_2_);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ___redArg(lean_object* v_a_5_, lean_object* v_n_6_){
_start:
{
lean_object* v___f_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___f_7_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_wtZ___redArg___lam__0), 2, 1);
lean_closure_set(v___f_7_, 0, v_a_5_);
v___x_8_ = lean_nat_to_int(v_n_6_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v___f_7_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_a_12_, lean_object* v_n_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_L2_Pj_wtZ___redArg(v_a_12_, v_n_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wtZ___boxed(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_n_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_L2_Pj_wtZ(v_E_15_, v_inst_16_, v_a_17_, v_n_18_);
lean_dec_ref(v_inst_16_);
return v_res_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CompData(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
