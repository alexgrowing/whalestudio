// Lean compiler output
// Module: New.UpperBound.Size.ShortColumns
// Imports: public import Init public meta import Init public import Lib.CM.FormalGroup.PrimeNotation public import Lib.GLn.Dual public import New.UpperBound.Kernels.JetConjugatesAndBounds public import New.UpperBound.Objects.Columns
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
lean_object* lp_mathlib_Nat_clog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts___redArg(lean_object* v_D_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_m_3_; lean_object* v___x_4_; 
v_m_3_ = lean_ctor_get(v_D_1_, 6);
v___x_4_ = lp_mathlib_Nat_clog(v_p_2_, v_m_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts___redArg___boxed(lean_object* v_D_5_, lean_object* v_p_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_GRH_New_Data_ceilLogLifts___redArg(v_D_5_, v_p_6_);
lean_dec(v_p_6_);
lean_dec_ref(v_D_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts(lean_object* v_P_8_, lean_object* v_D_9_, lean_object* v_p_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_GRH_New_Data_ceilLogLifts___redArg(v_D_9_, v_p_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_ceilLogLifts___boxed(lean_object* v_P_12_, lean_object* v_D_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_GRH_New_Data_ceilLogLifts(v_P_12_, v_D_13_, v_p_14_);
lean_dec(v_p_14_);
lean_dec_ref(v_D_13_);
lean_dec_ref(v_P_12_);
return v_res_15_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_FormalGroup_PrimeNotation(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_Dual(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Kernels_JetConjugatesAndBounds(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Columns(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Size_ShortColumns(uint8_t builtin) {
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
res = initialize_GRH_Lib_CM_FormalGroup_PrimeNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_Dual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Kernels_JetConjugatesAndBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Columns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
