// Lean compiler output
// Module: New.Congruences.Lifting.LongGap
// Imports: public import Init public meta import Init public import New.Congruences.Lifting.SidePoints
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
lean_object* lp_GRH_New_Lift_KummerChart_stdOrders(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders(lean_object* v_l_3_, lean_object* v_o_4_, lean_object* v_a_5_, lean_object* v_u_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = lp_GRH_New_Lift_KummerChart_stdOrders(v_l_3_, v_a_5_, v_u_6_);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_nat_dec_eq(v___x_8_, v_a_5_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_u_6_);
lean_dec_ref(v_o_4_);
v___x_10_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___closed__0, &lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___closed__0);
v___x_11_ = lean_int_add(v___x_7_, v___x_10_);
lean_dec(v___x_7_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_apply_1(v_o_4_, v_u_6_);
v___x_13_ = lean_int_add(v___x_7_, v___x_12_);
lean_dec(v___x_12_);
lean_dec(v___x_7_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders___boxed(lean_object* v_l_14_, lean_object* v_o_15_, lean_object* v_a_16_, lean_object* v_u_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_Lift_KummerChart_JumpLattice_shiftedStdOrders(v_l_14_, v_o_15_, v_a_16_, v_u_17_);
lean_dec(v_a_16_);
lean_dec(v_l_14_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_SidePoints(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_LongGap(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_Lifting_SidePoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
