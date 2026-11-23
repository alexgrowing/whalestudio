// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.RhoWApply
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
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
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_chiDet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_chiDet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_chiDet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_chiDet___redArg(lean_object* v_det_1_, lean_object* v_00_u03c7_2_){
_start:
{
lean_object* v___f_3_; 
v___f_3_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3_, 0, v_det_1_);
lean_closure_set(v___f_3_, 1, v_00_u03c7_2_);
return v___f_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_chiDet(lean_object* v_G_4_, lean_object* v_inst_5_, lean_object* v_D_6_, lean_object* v_L_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_det_10_, lean_object* v_00_u03c7_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_12_, 0, v_det_10_);
lean_closure_set(v___f_12_, 1, v_00_u03c7_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_chiDet___boxed(lean_object* v_G_13_, lean_object* v_inst_14_, lean_object* v_D_15_, lean_object* v_L_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_det_19_, lean_object* v_00_u03c7_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_Pj_chiDet(v_G_13_, v_inst_14_, v_D_15_, v_L_16_, v_inst_17_, v_inst_18_, v_det_19_, v_00_u03c7_20_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_14_);
return v_res_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
