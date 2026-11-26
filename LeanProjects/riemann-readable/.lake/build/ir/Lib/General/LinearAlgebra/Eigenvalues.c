// Lean compiler output
// Module: Lib.General.LinearAlgebra.Eigenvalues
// Imports: public import Init public meta import Init public import Lib.General.Groups.CongruenceSubgroups
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
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_traceIdentityMultipliers___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers(lean_object* v_W_5_, lean_object* v_W_x27_6_, lean_object* v_J_7_, lean_object* v_J_x27_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_A_13_, lean_object* v_A_x27_14_, lean_object* v_s_15_, lean_object* v_c_16_, lean_object* v_Q_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_traceIdentityMultipliers___boxed(lean_object* v_W_19_, lean_object* v_W_x27_20_, lean_object* v_J_21_, lean_object* v_J_x27_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_A_27_, lean_object* v_A_x27_28_, lean_object* v_s_29_, lean_object* v_c_30_, lean_object* v_Q_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_traceIdentityMultipliers(v_W_19_, v_W_x27_20_, v_J_21_, v_J_x27_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_A_27_, v_A_x27_28_, v_s_29_, v_c_30_, v_Q_31_);
lean_dec_ref(v_c_30_);
lean_dec(v_s_29_);
lean_dec(v_A_x27_28_);
lean_dec(v_A_27_);
lean_dec(v_inst_26_);
lean_dec_ref(v_inst_25_);
lean_dec(v_inst_24_);
lean_dec_ref(v_inst_23_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_CongruenceSubgroups(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Groups_CongruenceSubgroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
