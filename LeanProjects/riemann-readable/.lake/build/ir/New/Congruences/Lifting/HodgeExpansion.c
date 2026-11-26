// Lean compiler output
// Module: New.Congruences.Lifting.HodgeExpansion
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.MatrixNormBounds public import New.Congruences.Lifting.ExponentLattices
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedOrders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0;
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrdersAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrdersAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedOrders(lean_object* v_l_1_, lean_object* v_n_2_, lean_object* v_c_3_, lean_object* v_a_4_, lean_object* v_u_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_a_4_, v_l_1_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_nat_sub(v_a_4_, v_l_1_);
v___x_8_ = lean_apply_2(v_c_3_, v___x_7_, v_u_5_);
return v___x_8_;
}
else
{
lean_dec(v_u_5_);
lean_dec_ref(v_c_3_);
lean_inc(v_n_2_);
return v_n_2_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedOrders___boxed(lean_object* v_l_9_, lean_object* v_n_10_, lean_object* v_c_11_, lean_object* v_a_12_, lean_object* v_u_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedOrders(v_l_9_, v_n_10_, v_c_11_, v_a_12_, v_u_13_);
lean_dec(v_a_12_);
lean_dec(v_n_10_);
lean_dec(v_l_9_);
return v_res_14_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v___x_16_ = lean_nat_to_int(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_to_int(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder(lean_object* v_o_19_, lean_object* v_a_20_, lean_object* v_u_21_, lean_object* v_b_22_, lean_object* v_v_23_){
_start:
{
lean_object* v___x_24_; uint8_t v___x_28_; 
lean_inc(v_v_23_);
lean_inc(v_b_22_);
v___x_24_ = lean_apply_2(v_o_19_, v_b_22_, v_v_23_);
v___x_28_ = lean_nat_dec_eq(v_b_22_, v_a_20_);
lean_dec(v_b_22_);
if (v___x_28_ == 0)
{
lean_dec(v_v_23_);
goto v___jp_25_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = lean_int_dec_eq(v_v_23_, v_u_21_);
lean_dec(v_v_23_);
if (v___x_29_ == 0)
{
goto v___jp_25_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1, &lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1_once, _init_lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1);
v___x_31_ = lean_int_add(v___x_24_, v___x_30_);
lean_dec(v___x_24_);
return v___x_31_;
}
}
v___jp_25_:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0, &lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0);
v___x_27_ = lean_int_add(v___x_24_, v___x_26_);
lean_dec(v___x_24_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___boxed(lean_object* v_o_32_, lean_object* v_a_33_, lean_object* v_u_34_, lean_object* v_b_35_, lean_object* v_v_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder(v_o_32_, v_a_33_, v_u_34_, v_b_35_, v_v_36_);
lean_dec(v_u_34_);
lean_dec(v_a_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrdersAt(lean_object* v_o_38_, lean_object* v_a_39_, lean_object* v_b_40_, lean_object* v_v_41_){
_start:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
lean_inc(v_b_40_);
v___x_42_ = lean_apply_2(v_o_38_, v_b_40_, v_v_41_);
v___x_43_ = lean_nat_dec_eq(v_b_40_, v_a_39_);
lean_dec(v_b_40_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0, &lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__0);
v___x_45_ = lean_int_add(v___x_42_, v___x_44_);
lean_dec(v___x_42_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1, &lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1_once, _init_lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrder___closed__1);
v___x_47_ = lean_int_add(v___x_42_, v___x_46_);
lean_dec(v___x_42_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrdersAt___boxed(lean_object* v_o_48_, lean_object* v_a_49_, lean_object* v_b_50_, lean_object* v_v_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_GRH_New_Lift_KummerChart_JumpLattice_raiseOrdersAt(v_o_48_, v_a_49_, v_b_50_, v_v_51_);
lean_dec(v_a_49_);
return v_res_52_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_ExponentLattices(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_HodgeExpansion(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_MatrixNormBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Lifting_ExponentLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
