// Lean compiler output
// Module: Lib.Adelic.AutomorphicForms.HeckeEigenforms
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.SchurNorm
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
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_domRestrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_evalClassReps___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_evalClassReps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_evalClassReps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_evalClassReps___redArg(lean_object* v_r_1_){
_start:
{
lean_object* v___f_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_funLeft___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2_, 0, v_r_1_);
v___x_3_ = lp_mathlib_LinearMap_domRestrict___redArg(v___f_2_);
v___x_4_ = lp_mathlib_LinearMap_domRestrict___redArg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_evalClassReps(lean_object* v_G_5_, lean_object* v_00_u0393_6_, lean_object* v_W_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_e_13_, lean_object* v_00_u03c1_14_, lean_object* v_00_u03c7_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_r_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_GRH_New_evalClassReps___redArg(v_r_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_evalClassReps___boxed(lean_object* v_G_20_, lean_object* v_00_u0393_21_, lean_object* v_W_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_K_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_e_28_, lean_object* v_00_u03c1_29_, lean_object* v_00_u03c7_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_r_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_evalClassReps(v_G_20_, v_00_u0393_21_, v_W_22_, v_inst_23_, v_inst_24_, v_K_25_, v_inst_26_, v_inst_27_, v_e_28_, v_00_u03c1_29_, v_00_u03c7_30_, v_inst_31_, v_inst_32_, v_r_33_);
lean_dec_ref(v_00_u03c7_30_);
lean_dec(v_00_u03c1_29_);
lean_dec(v_e_28_);
lean_dec(v_inst_27_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_SchurNorm(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_HeckeEigenforms(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_SchurModule_SchurNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
