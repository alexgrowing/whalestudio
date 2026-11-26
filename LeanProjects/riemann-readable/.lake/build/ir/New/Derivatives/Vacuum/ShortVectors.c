// Lean compiler output
// Module: New.Derivatives.Vacuum.ShortVectors
// Imports: public import Init public meta import Init public import New.Derivatives.Field.ChosenPlaces
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
lean_object* lp_GRH_New_towerDeg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_clog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_ceilLogQ_u2081(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_ceilLogQ_u2081___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_ceilLogQ_u2081(lean_object* v_P_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_q_u2080_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_q_u2080_3_ = lean_ctor_get(v_P_1_, 0);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lp_GRH_New_towerDeg(v_s_2_);
v___x_6_ = lean_nat_mul(v_q_u2080_3_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lp_mathlib_Nat_clog(v___x_4_, v___x_6_);
lean_dec(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Parameters_ceilLogQ_u2081___boxed(lean_object* v_P_8_, lean_object* v_s_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_GRH_New_Parameters_ceilLogQ_u2081(v_P_8_, v_s_9_);
lean_dec_ref(v_P_8_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Field_ChosenPlaces(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Derivatives_Vacuum_ShortVectors(uint8_t builtin) {
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
res = initialize_GRH_New_Derivatives_Field_ChosenPlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
