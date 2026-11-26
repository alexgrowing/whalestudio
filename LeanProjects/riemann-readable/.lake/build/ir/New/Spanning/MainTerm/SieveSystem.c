// Lean compiler output
// Module: New.Spanning.MainTerm.SieveSystem
// Imports: public import Init public meta import Init public import Lib.General.Groups.BesselGroups public import Lib.General.Measure.IntegralOperators
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
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_326038627____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dampedPower(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dampedPower___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_headAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_headAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dampedPower(lean_object* v_k_1_, lean_object* v_r_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___f_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___f_8_; 
lean_inc(v_r_2_);
v___x_3_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v_k_1_, v_r_2_);
v___x_4_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___f_5_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_326038627____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_5_, 0, v___x_4_);
lean_closure_set(v___f_5_, 1, v_r_2_);
v___x_6_ = lean_unsigned_to_nat(6u);
v___x_7_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_6_, v___f_5_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_8_, 0, v___x_3_);
lean_closure_set(v___f_8_, 1, v___x_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dampedPower___boxed(lean_object* v_k_9_, lean_object* v_r_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_New_dampedPower(v_k_9_, v_r_10_);
lean_dec(v_k_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_headAt___redArg(lean_object* v_v_12_, lean_object* v_p_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_fst_16_; lean_object* v___x_17_; 
v___x_15_ = lean_apply_1(v_p_13_, v_a_14_);
v_fst_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_fst_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_apply_1(v_fst_16_, v_v_12_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_headAt(lean_object* v_U_18_, lean_object* v_00_u03c4_19_, lean_object* v_v_20_, lean_object* v_p_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_GRH_New_headAt___redArg(v_v_20_, v_p_21_, v_a_22_);
return v___x_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_BesselGroups(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Measure_IntegralOperators(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_MainTerm_SieveSystem(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Groups_BesselGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Measure_IntegralOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
