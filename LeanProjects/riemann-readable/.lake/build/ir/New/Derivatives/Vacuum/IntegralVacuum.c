// Lean compiler output
// Module: New.Derivatives.Vacuum.IntegralVacuum
// Imports: public import Init public meta import Init public import Lib.CM.FiniteLattices public import Lib.Weil.Construction.CanonicalTheta public import New.Derivatives.Vacuum.TightFrames
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
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Parameters_integralAfter___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter(lean_object* v_P_5_, lean_object* v_s_6_, lean_object* v_n_7_, lean_object* v_00_u03b4_8_, lean_object* v_S_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_integralAfter___boxed(lean_object* v_P_11_, lean_object* v_s_12_, lean_object* v_n_13_, lean_object* v_00_u03b4_14_, lean_object* v_S_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_Parameters_integralAfter(v_P_11_, v_s_12_, v_n_13_, v_00_u03b4_14_, v_S_15_);
lean_dec_ref(v_00_u03b4_14_);
lean_dec(v_s_12_);
lean_dec_ref(v_P_11_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_FiniteLattices(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_CanonicalTheta(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Vacuum_TightFrames(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_Vacuum_IntegralVacuum(uint8_t builtin) {
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
res = initialize_GRH_Lib_CM_FiniteLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Construction_CanonicalTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Derivatives_Vacuum_TightFrames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
