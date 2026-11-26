// Lean compiler output
// Module: Lib.PadicHodge.Limit.TraceLimit
// Imports: public import Init public meta import Init public import Lib.GaloisRep.Main.LocalConditions public import Lib.General.LinearAlgebra.TensorChains public import Lib.PadicHodge.Limit.CrystallineLimit
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg___lam__0(lean_object* v_k_1_, lean_object* v_w_2_, lean_object* v_toZero_3_, lean_object* v_toOne_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_apply_1(v_k_1_, v_i_5_);
v___x_7_ = lean_int_dec_eq(v_w_2_, v___x_6_);
lean_dec(v___x_6_);
if (v___x_7_ == 0)
{
lean_inc(v_toZero_3_);
return v_toZero_3_;
}
else
{
lean_inc(v_toOne_4_);
return v_toOne_4_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg___lam__0___boxed(lean_object* v_k_8_, lean_object* v_w_9_, lean_object* v_toZero_10_, lean_object* v_toOne_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg___lam__0(v_k_8_, v_w_9_, v_toZero_10_, v_toOne_11_, v_i_12_);
lean_dec(v_toOne_11_);
lean_dec(v_toZero_10_);
lean_dec(v_w_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_w_16_, lean_object* v_k_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_toSemiring_20_; lean_object* v___x_21_; lean_object* v_toZero_22_; lean_object* v___x_23_; lean_object* v_toAddMonoidWithOne_24_; lean_object* v_toOne_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v_toSemiring_20_ = lean_ctor_get(v_inst_15_, 0);
lean_inc_ref(v_toSemiring_20_);
v___x_21_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_20_);
v_toZero_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc_n(v_toZero_22_, 2);
lean_dec_ref(v___x_21_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_15_);
v_toAddMonoidWithOne_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_toAddMonoidWithOne_24_);
lean_dec_ref(v___x_23_);
v_toOne_25_ = lean_ctor_get(v_toAddMonoidWithOne_24_, 2);
lean_inc(v_toOne_25_);
lean_dec_ref(v_toAddMonoidWithOne_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_26_, 0, v_k_17_);
lean_closure_set(v___f_26_, 1, v_w_16_);
lean_closure_set(v___f_26_, 2, v_toZero_22_);
lean_closure_set(v___f_26_, 3, v_toOne_25_);
v___x_27_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_14_, v_toZero_22_, v___f_26_, v_a_18_, v_a_19_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector(lean_object* v_00_u03b1_28_, lean_object* v_A_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_w_32_, lean_object* v_k_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_GRH___private_Lib_PadicHodge_Limit_TraceLimit_0__New_Period_jumpProjector___redArg(v_inst_30_, v_inst_31_, v_w_32_, v_k_33_, v_a_34_, v_a_35_);
return v___x_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Main_LocalConditions(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_TensorChains(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Limit_CrystallineLimit(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicHodge_Limit_TraceLimit(uint8_t builtin) {
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
res = initialize_GRH_Lib_GaloisRep_Main_LocalConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_TensorChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicHodge_Limit_CrystallineLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
