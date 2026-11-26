// Lean compiler output
// Module: New.OneLift.ComparisonOperator.OneExchange
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.PAdicGauge public import Lib.General.LinearAlgebra.BlockEmbeddings public import New.Determinant.Exchange.MatchingPartners
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
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Rows_rowStabilizer___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer(lean_object* v_R_5_, lean_object* v_S_6_, lean_object* v_r_7_, lean_object* v_c_8_, lean_object* v_N_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03c6_15_, lean_object* v_w_16_, lean_object* v_e_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_rowStabilizer___boxed(lean_object* v_R_19_, lean_object* v_S_20_, lean_object* v_r_21_, lean_object* v_c_22_, lean_object* v_N_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_00_u03c6_29_, lean_object* v_w_30_, lean_object* v_e_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_Rows_rowStabilizer(v_R_19_, v_S_20_, v_r_21_, v_c_22_, v_N_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_00_u03c6_29_, v_w_30_, v_e_31_);
lean_dec(v_e_31_);
lean_dec(v_w_30_);
lean_dec(v_00_u03c6_29_);
lean_dec_ref(v_inst_28_);
lean_dec(v_inst_27_);
lean_dec(v_inst_26_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_PAdicGauge(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Exchange_MatchingPartners(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_OneLift_ComparisonOperator_OneExchange(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_PAdicGauge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Exchange_MatchingPartners(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
