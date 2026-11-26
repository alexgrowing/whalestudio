// Lean compiler output
// Module: New.Reduction.Data.FieldsAndPlaces
// Imports: public import Init public meta import Init public import Lib.ClassField.Places.DecompositionCyclotomic public import Lib.General.NumberTheory.ImaginaryQuadraticField
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_log(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_l_u2080(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_towerDeg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2081(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2081___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2082(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2082___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_l_u2080(lean_object* v_s_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_2_ = lean_unsigned_to_nat(3u);
v___x_3_ = lp_mathlib_Nat_log(v___x_2_, v_s_1_);
v___x_4_ = lean_unsigned_to_nat(4u);
v___x_5_ = lean_nat_add(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_nat_pow(v___x_2_, v___x_5_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_towerDeg(lean_object* v_s_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_8_ = lean_unsigned_to_nat(3u);
lean_inc(v_s_7_);
v___x_9_ = lp_mathlib_Nat_log(v___x_8_, v_s_7_);
v___x_10_ = lean_unsigned_to_nat(5u);
v___x_11_ = lean_nat_add(v___x_9_, v___x_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_nat_pow(v___x_8_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_unsigned_to_nat(2u);
v___x_14_ = lean_nat_pow(v___x_13_, v_s_7_);
lean_dec(v_s_7_);
v___x_15_ = lean_nat_mul(v___x_12_, v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2081(lean_object* v_P_16_, lean_object* v_s_17_){
_start:
{
lean_object* v_q_u2080_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_q_u2080_18_ = lean_ctor_get(v_P_16_, 0);
v___x_19_ = lp_GRH_New_towerDeg(v_s_17_);
v___x_20_ = lean_nat_mul(v_q_u2080_18_, v___x_19_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2081___boxed(lean_object* v_P_21_, lean_object* v_s_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_Parameters_q_u2081(v_P_21_, v_s_22_);
lean_dec_ref(v_P_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2082(lean_object* v_P_24_, lean_object* v_s_25_){
_start:
{
lean_object* v_q_u2080_26_; lean_object* v_d_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_q_u2080_26_ = lean_ctor_get(v_P_24_, 0);
v_d_27_ = lean_ctor_get(v_P_24_, 1);
v___x_28_ = lean_nat_mul(v_q_u2080_26_, v_d_27_);
v___x_29_ = lean_unsigned_to_nat(6u);
v___x_30_ = lean_nat_add(v_s_25_, v___x_29_);
v___x_31_ = lean_nat_pow(v___x_28_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_q_u2082___boxed(lean_object* v_P_32_, lean_object* v_s_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_Parameters_q_u2082(v_P_32_, v_s_33_);
lean_dec(v_s_33_);
lean_dec_ref(v_P_32_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_DecompositionCyclotomic(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Reduction_Data_FieldsAndPlaces(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Places_DecompositionCyclotomic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
