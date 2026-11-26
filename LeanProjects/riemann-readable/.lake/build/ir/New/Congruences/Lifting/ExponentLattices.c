// Lean compiler output
// Module: New.Congruences.Lifting.ExponentLattices
// Imports: public import Init public meta import Init public import Lib.PadicHodge.Kisin.FrameTheorem
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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_padicValInt(lean_object*, lean_object*);
lean_object* lp_GRH_New_Lift_KummerChart_differentBound___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost___redArg(lean_object* v_p_1_, lean_object* v_k_2_, lean_object* v_a_3_, lean_object* v_n_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_5_ = lp_mathlib_padicValInt(v_p_1_, v_n_4_);
v___x_6_ = lp_GRH_New_Lift_KummerChart_differentBound___redArg(v_p_1_, v_k_2_);
v___x_7_ = lean_unsigned_to_nat(3u);
v___x_8_ = lean_nat_mul(v___x_7_, v_a_3_);
v___x_9_ = lean_nat_add(v___x_6_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_6_);
v___x_10_ = lean_nat_add(v___x_5_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_5_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost___redArg___boxed(lean_object* v_p_11_, lean_object* v_k_12_, lean_object* v_a_13_, lean_object* v_n_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_GRH_New_Lift_KummerChart_cost___redArg(v_p_11_, v_k_12_, v_a_13_, v_n_14_);
lean_dec(v_n_14_);
lean_dec(v_a_13_);
lean_dec(v_p_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost(lean_object* v_p_16_, lean_object* v_P_17_, lean_object* v_00_u0393_18_, lean_object* v_k_19_, lean_object* v_a_20_, lean_object* v_n_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_GRH_New_Lift_KummerChart_cost___redArg(v_p_16_, v_k_19_, v_a_20_, v_n_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cost___boxed(lean_object* v_p_23_, lean_object* v_P_24_, lean_object* v_00_u0393_25_, lean_object* v_k_26_, lean_object* v_a_27_, lean_object* v_n_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_GRH_New_Lift_KummerChart_cost(v_p_23_, v_P_24_, v_00_u0393_25_, v_k_26_, v_a_27_, v_n_28_);
lean_dec(v_n_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_00_u0393_25_);
lean_dec(v_p_23_);
return v_res_29_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders(lean_object* v_lo_32_, lean_object* v_hi_33_, lean_object* v_a_34_, lean_object* v_u_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___y_38_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
lean_inc(v_u_35_);
lean_inc(v_a_34_);
v___x_36_ = lean_apply_2(v_hi_33_, v_a_34_, v_u_35_);
v___x_40_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders___closed__0, &lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_JumpLattice_improvedOrders___closed__0);
v___x_41_ = lean_apply_2(v_lo_32_, v_a_34_, v_u_35_);
v___x_42_ = lean_int_dec_lt(v___x_40_, v___x_41_);
lean_dec(v___x_41_);
if (v___x_42_ == 0)
{
v___y_38_ = v___x_40_;
goto v___jp_37_;
}
else
{
lean_inc(v___x_36_);
v___y_38_ = v___x_36_;
goto v___jp_37_;
}
v___jp_37_:
{
uint8_t v___x_39_; 
v___x_39_ = lean_int_dec_le(v___x_36_, v___y_38_);
if (v___x_39_ == 0)
{
lean_dec(v___x_36_);
return v___y_38_;
}
else
{
lean_dec(v___y_38_);
return v___x_36_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Kisin_FrameTheorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_ExponentLattices(uint8_t builtin) {
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
res = initialize_GRH_Lib_PadicHodge_Kisin_FrameTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
