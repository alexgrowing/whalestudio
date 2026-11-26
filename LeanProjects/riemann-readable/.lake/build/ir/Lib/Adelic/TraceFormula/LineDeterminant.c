// Lean compiler output
// Module: Lib.Adelic.TraceFormula.LineDeterminant
// Imports: public import Init public meta import Init public import Lib.Base
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
lean_object* lp_mathlib_LinearMap_restrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_restrictGenEigenspace___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_restrictGenEigenspace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_restrictGenEigenspace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_restrictGenEigenspace___redArg(lean_object* v_T_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_LinearMap_restrict___redArg(v_T_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_restrictGenEigenspace(lean_object* v_B_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_A_6_, lean_object* v_T_7_, lean_object* v_h_8_, lean_object* v_00_u03bc_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lp_mathlib_LinearMap_restrict___redArg(v_T_7_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_restrictGenEigenspace___boxed(lean_object* v_B_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_A_14_, lean_object* v_T_15_, lean_object* v_h_16_, lean_object* v_00_u03bc_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_restrictGenEigenspace(v_B_11_, v_inst_12_, v_inst_13_, v_A_14_, v_T_15_, v_h_16_, v_00_u03bc_17_);
lean_dec_ref(v_00_u03bc_17_);
lean_dec(v_A_14_);
lean_dec(v_inst_13_);
lean_dec_ref(v_inst_12_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_TraceFormula_LineDeterminant(uint8_t builtin) {
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
res = initialize_GRH_Lib_Base(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
