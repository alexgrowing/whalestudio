// Lean compiler output
// Module: Lib.SiegelWeil.Tower.ConstantTerm
// Imports: public import Init public meta import Init public import Lib.SiegelWeil.SingularForms.UnimodularCoefficients public import Lib.SiegelWeil.Tower.LineTerms public import Lib.SiegelWeil.Tower.PrincipalIdeles public import Lib.Weil.DualPair.ThetaIntegrals
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
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Exchange_splittingLine___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_r_8_, lean_object* v_r_x27_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_t_14_, lean_object* v_t_x27_15_, lean_object* v_V_16_, lean_object* v_V_x27_17_, lean_object* v_X_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_splittingLine___boxed(lean_object* v_E_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_r_23_, lean_object* v_r_x27_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_t_29_, lean_object* v_t_x27_30_, lean_object* v_V_31_, lean_object* v_V_x27_32_, lean_object* v_X_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_Exchange_splittingLine(v_E_20_, v_inst_21_, v_inst_22_, v_r_23_, v_r_x27_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_t_29_, v_t_x27_30_, v_V_31_, v_V_x27_32_, v_X_33_);
lean_dec_ref(v_X_33_);
lean_dec_ref(v_V_x27_32_);
lean_dec_ref(v_V_31_);
lean_dec_ref(v_t_x27_30_);
lean_dec_ref(v_t_29_);
lean_dec_ref(v_inst_28_);
lean_dec(v_inst_27_);
lean_dec_ref(v_inst_26_);
lean_dec(v_inst_25_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_SingularForms_UnimodularCoefficients(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_LineTerms(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_PrincipalIdeles(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_ThetaIntegrals(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_SiegelWeil_Tower_ConstantTerm(uint8_t builtin) {
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
res = initialize_GRH_Lib_SiegelWeil_SingularForms_UnimodularCoefficients(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_Tower_LineTerms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_Tower_PrincipalIdeles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_ThetaIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
