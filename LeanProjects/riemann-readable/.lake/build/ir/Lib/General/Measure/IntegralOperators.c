// Lean compiler output
// Module: Lib.General.Measure.IntegralOperators
// Imports: public import Init public meta import Init public import Lib.Adelic.QuotientMeasure.Basic
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_padTuple___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_padTuple___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_padTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_padTuple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_padTuple___redArg(lean_object* v_n_1_, lean_object* v_inst_2_, lean_object* v_c_3_, lean_object* v_t_4_, lean_object* v_a_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_a_5_, v_n_1_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
lean_dec(v_c_3_);
v___x_7_ = lean_nat_dec_eq(v_a_5_, v_n_1_);
lean_dec(v_a_5_);
if (v___x_7_ == 0)
{
lean_inc(v_inst_2_);
return v_inst_2_;
}
else
{
lean_inc(v_t_4_);
return v_t_4_;
}
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_c_3_, v_a_5_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_padTuple___redArg___boxed(lean_object* v_n_9_, lean_object* v_inst_10_, lean_object* v_c_11_, lean_object* v_t_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_padTuple___redArg(v_n_9_, v_inst_10_, v_c_11_, v_t_12_, v_a_13_);
lean_dec(v_t_12_);
lean_dec(v_inst_10_);
lean_dec(v_n_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_padTuple(lean_object* v_C_15_, lean_object* v_n_16_, lean_object* v_inst_17_, lean_object* v_c_18_, lean_object* v_t_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_GRH_New_padTuple___redArg(v_n_16_, v_inst_17_, v_c_18_, v_t_19_, v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_padTuple___boxed(lean_object* v_C_22_, lean_object* v_n_23_, lean_object* v_inst_24_, lean_object* v_c_25_, lean_object* v_t_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_padTuple(v_C_22_, v_n_23_, v_inst_24_, v_c_25_, v_t_26_, v_a_27_);
lean_dec(v_t_26_);
lean_dec(v_inst_24_);
lean_dec(v_n_23_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_QuotientMeasure_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Measure_IntegralOperators(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_QuotientMeasure_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
