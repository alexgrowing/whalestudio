// Lean compiler output
// Module: Lib.Shimura.ComplexTheta.AppellHumbertData
// Imports: public import Init public meta import Init public import Lib.Adelic.Adeles.AdditiveCharacter public import Lib.General.Analysis.FourierTransforms public import Lib.General.Topology
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
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_RealComplexForm_thetaSpace___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace(lean_object* v_V_5_, lean_object* v_inst_6_, lean_object* v_L_7_, lean_object* v_00_u03c7_8_, lean_object* v_B_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealComplexForm_thetaSpace___boxed(lean_object* v_V_11_, lean_object* v_inst_12_, lean_object* v_L_13_, lean_object* v_00_u03c7_14_, lean_object* v_B_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_RealComplexForm_thetaSpace(v_V_11_, v_inst_12_, v_L_13_, v_00_u03c7_14_, v_B_15_);
lean_dec_ref(v_B_15_);
lean_dec_ref(v_00_u03c7_14_);
lean_dec_ref(v_inst_12_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Adeles_AdditiveCharacter(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_FourierTransforms(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Topology(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ComplexTheta_AppellHumbertData(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Adeles_AdditiveCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Analysis_FourierTransforms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Topology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
