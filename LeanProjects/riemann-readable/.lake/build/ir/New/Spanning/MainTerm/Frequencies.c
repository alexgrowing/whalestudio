// Lean compiler output
// Module: New.Spanning.MainTerm.Frequencies
// Imports: public import Init public meta import Init public import Lib.ClassField.HeckeL.EulerProduct public import Lib.General.Analysis.PackingAndSobolev
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
LEAN_EXPORT lean_object* lp_GRH_New_denominator___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_denominator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_denominator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_denominator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_denominator___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_denominator___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_denominator___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_denominator(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_00_u03bd_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_denominator___boxed(lean_object* v_E_9_, lean_object* v_inst_10_, lean_object* v_00_u03bd_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_denominator(v_E_9_, v_inst_10_, v_00_u03bd_11_);
lean_dec(v_00_u03bd_11_);
lean_dec_ref(v_inst_10_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeL_EulerProduct(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_PackingAndSobolev(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_MainTerm_Frequencies(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_HeckeL_EulerProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Analysis_PackingAndSobolev(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
