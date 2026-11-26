// Lean compiler output
// Module: New.Derivatives.FormalGroup.Exponent
// Imports: public import Init public meta import Init public import Lib.General.Algebra.SeriesCongruences public import New.Derivatives.FormalGroup.FrobeniusCongruence
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leastFlatDegree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leastFlatDegree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leastFlatDegree(lean_object* v_d_1_, lean_object* v_p_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_eq(v_p_2_, v_d_1_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_p_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(2u);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leastFlatDegree___boxed(lean_object* v_d_7_, lean_object* v_p_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_GRH_New_leastFlatDegree(v_d_7_, v_p_8_);
lean_dec(v_p_8_);
lean_dec(v_d_7_);
return v_res_9_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_SeriesCongruences(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_FormalGroup_FrobeniusCongruence(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_FormalGroup_Exponent(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Algebra_SeriesCongruences(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Derivatives_FormalGroup_FrobeniusCongruence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
