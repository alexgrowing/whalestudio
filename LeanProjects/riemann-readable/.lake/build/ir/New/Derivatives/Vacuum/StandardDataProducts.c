// Lean compiler output
// Module: New.Derivatives.Vacuum.StandardDataProducts
// Imports: public import Init public meta import Init public import New.Derivatives.Vacuum.JetIntegrality public import New.Derivatives.Vacuum.ShortVectors
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
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Parameters_thetaMultiples___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples(lean_object* v_P_5_, lean_object* v_s_6_, lean_object* v_n_7_, lean_object* v_p_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_00_u03b5_12_, lean_object* v_V_13_, lean_object* v_inst_14_, lean_object* v_J_15_, lean_object* v_inst_16_, lean_object* v_00_u03bc_17_, lean_object* v_c_18_, lean_object* v_00_u0398_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_thetaMultiples___boxed(lean_object* v_P_21_, lean_object* v_s_22_, lean_object* v_n_23_, lean_object* v_p_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_00_u03b5_28_, lean_object* v_V_29_, lean_object* v_inst_30_, lean_object* v_J_31_, lean_object* v_inst_32_, lean_object* v_00_u03bc_33_, lean_object* v_c_34_, lean_object* v_00_u0398_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_Parameters_thetaMultiples(v_P_21_, v_s_22_, v_n_23_, v_p_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_00_u03b5_28_, v_V_29_, v_inst_30_, v_J_31_, v_inst_32_, v_00_u03bc_33_, v_c_34_, v_00_u0398_35_);
lean_dec(v_00_u0398_35_);
lean_dec_ref(v_c_34_);
lean_dec(v_00_u03bc_33_);
lean_dec(v_inst_32_);
lean_dec(v_inst_30_);
lean_dec_ref(v_V_29_);
lean_dec_ref(v_00_u03b5_28_);
lean_dec_ref(v_inst_27_);
lean_dec(v_inst_26_);
lean_dec(v_p_24_);
lean_dec(v_s_22_);
lean_dec_ref(v_P_21_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Vacuum_JetIntegrality(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Vacuum_ShortVectors(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_Vacuum_StandardDataProducts(uint8_t builtin) {
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
res = initialize_GRH_New_Derivatives_Vacuum_JetIntegrality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Derivatives_Vacuum_ShortVectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
