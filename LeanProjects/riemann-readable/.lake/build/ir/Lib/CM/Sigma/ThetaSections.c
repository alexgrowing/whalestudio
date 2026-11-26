// Lean compiler output
// Module: Lib.CM.Sigma.ThetaSections
// Imports: public import Init public meta import Init public import Lib.General.Analysis.MeanValueAndTaylor public import Lib.General.NumberTheory.SUnitsAndClassNumber
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
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_monomialDeg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_monomialDeg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_monomialDeg(lean_object* v_x_1_){
_start:
{
lean_object* v_snd_2_; lean_object* v_fst_3_; lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_snd_2_ = lean_ctor_get(v_x_1_, 1);
v_fst_3_ = lean_ctor_get(v_x_1_, 0);
v_fst_4_ = lean_ctor_get(v_snd_2_, 0);
v_snd_5_ = lean_ctor_get(v_snd_2_, 1);
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = lean_nat_mul(v_fst_4_, v___x_6_);
v___x_8_ = lean_nat_add(v_fst_3_, v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_unsigned_to_nat(3u);
v___x_10_ = lean_nat_mul(v_snd_5_, v___x_9_);
v___x_11_ = lean_nat_add(v___x_8_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v___x_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_monomialDeg___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH_New_CMLattice_monomialDeg(v_x_12_);
lean_dec_ref(v_x_12_);
return v_res_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_MeanValueAndTaylor(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_SUnitsAndClassNumber(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_CM_Sigma_ThetaSections(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Analysis_MeanValueAndTaylor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_SUnitsAndClassNumber(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
