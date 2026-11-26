// Lean compiler output
// Module: Lib.General.Algebra.AbsIntegrallyClosed
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_powMonoidHom___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_mk_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow___redArg(lean_object* v_p_1_, lean_object* v_inst_2_, lean_object* v_f_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___f_7_; 
v___x_4_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_2_);
v___x_5_ = lean_nat_pow(v_p_1_, v_f_3_);
v___x_6_ = lp_mathlib_powMonoidHom___redArg(v___x_4_, v___x_5_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_mk_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_7_, 0, v___x_6_);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow___redArg___boxed(lean_object* v_p_8_, lean_object* v_inst_9_, lean_object* v_f_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_New_Variety_frobPow___redArg(v_p_8_, v_inst_9_, v_f_10_);
lean_dec(v_f_10_);
lean_dec_ref(v_inst_9_);
lean_dec(v_p_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow(lean_object* v_p_12_, lean_object* v_B_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_h_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_GRH_New_Variety_frobPow___redArg(v_p_12_, v_inst_15_, v_f_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_frobPow___boxed(lean_object* v_p_19_, lean_object* v_B_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_h_23_, lean_object* v_f_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_Variety_frobPow(v_p_19_, v_B_20_, v_inst_21_, v_inst_22_, v_h_23_, v_f_24_);
lean_dec(v_f_24_);
lean_dec_ref(v_inst_22_);
lean_dec(v_p_19_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Algebra_AbsIntegrallyClosed(uint8_t builtin) {
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
