// Lean compiler output
// Module: New.Derivatives.FormalGroup.Resolution
// Imports: public import Init public meta import Init public import Lib.CM.Integrality.LogTheta public import Lib.Weil.Construction.ThetaJets
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
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dagger___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dagger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dagger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dagger___redArg(lean_object* v_inst_1_, lean_object* v_y_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_fst_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_x_3_);
v___x_6_ = lean_apply_1(v_y_2_, v_snd_5_);
v___x_7_ = lean_apply_2(v_inst_1_, v_fst_4_, v___x_6_);
v___x_8_ = lp_mathlib_Complex_instStarRing___lam__0(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dagger(lean_object* v_E_9_, lean_object* v_n_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_y_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_GRH_New_dagger___redArg(v_inst_12_, v_y_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dagger___boxed(lean_object* v_E_16_, lean_object* v_n_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_y_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_dagger(v_E_16_, v_n_17_, v_inst_18_, v_inst_19_, v_y_20_, v_x_21_);
lean_dec_ref(v_inst_18_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_Integrality_LogTheta(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_ThetaJets(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_FormalGroup_Resolution(uint8_t builtin) {
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
res = initialize_GRH_Lib_CM_Integrality_LogTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Construction_ThetaJets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
