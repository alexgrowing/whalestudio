// Lean compiler output
// Module: New.Congruences.Lifting.CutExponentBounds
// Imports: public import Init public meta import Init public import New.Congruences.Lifting.LongGap public import New.Congruences.Lifting.SafeMoves
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
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lp_GRH_New_Lift_raisedOrdersAtZero(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_cutOrders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_cutOrders___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cutOrders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cutOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_longGapDepth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_longGapDepth___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_longGapDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_longGapDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Lift_KummerChart_cutOrders___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cutOrders(lean_object* v_s_3_, lean_object* v_00_u03b7_4_, lean_object* v_l_5_, lean_object* v_a_6_, lean_object* v_u_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___y_14_; lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
lean_inc(v_s_3_);
v___x_8_ = lean_nat_to_int(v_s_3_);
v___x_9_ = lean_int_neg(v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_l_5_, v___x_10_);
v___x_12_ = lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth(v_s_3_, v_00_u03b7_4_, v___x_11_, v_a_6_, v_u_7_);
lean_dec(v___x_11_);
v___x_16_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_cutOrders___closed__0, &lp_GRH_New_Lift_KummerChart_cutOrders___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_cutOrders___closed__0);
v___x_17_ = lp_GRH_New_Lift_raisedOrdersAtZero(v___x_9_, v_a_6_, v_u_7_);
lean_dec(v___x_9_);
v___x_18_ = lean_int_dec_lt(v___x_16_, v___x_17_);
lean_dec(v___x_17_);
if (v___x_18_ == 0)
{
v___y_14_ = v___x_16_;
goto v___jp_13_;
}
else
{
lean_inc(v___x_12_);
v___y_14_ = v___x_12_;
goto v___jp_13_;
}
v___jp_13_:
{
uint8_t v___x_15_; 
v___x_15_ = lean_int_dec_le(v___x_12_, v___y_14_);
if (v___x_15_ == 0)
{
lean_dec(v___x_12_);
return v___y_14_;
}
else
{
lean_dec(v___y_14_);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_cutOrders___boxed(lean_object* v_s_19_, lean_object* v_00_u03b7_20_, lean_object* v_l_21_, lean_object* v_a_22_, lean_object* v_u_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_Lift_KummerChart_cutOrders(v_s_19_, v_00_u03b7_20_, v_l_21_, v_a_22_, v_u_23_);
lean_dec(v_u_23_);
lean_dec(v_a_22_);
lean_dec(v_l_21_);
return v_res_24_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_longGapDepth___closed__0(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_longGapDepth(lean_object* v_l_27_, lean_object* v_t_28_, lean_object* v_r_29_, lean_object* v_a_30_, lean_object* v_u_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = lean_nat_dec_eq(v_a_30_, v_t_28_);
if (v___x_32_ == 0)
{
uint8_t v___x_33_; 
lean_dec(v_r_29_);
v___x_33_ = lean_nat_dec_lt(v_a_30_, v_l_27_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_int_neg(v_u_31_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_longGapDepth___closed__0, &lp_GRH_New_Lift_KummerChart_longGapDepth___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_longGapDepth___closed__0);
return v___x_35_;
}
}
else
{
lean_object* v___x_36_; 
v___x_36_ = lean_nat_to_int(v_r_29_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_longGapDepth___boxed(lean_object* v_l_37_, lean_object* v_t_38_, lean_object* v_r_39_, lean_object* v_a_40_, lean_object* v_u_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_GRH_New_Lift_KummerChart_longGapDepth(v_l_37_, v_t_38_, v_r_39_, v_a_40_, v_u_41_);
lean_dec(v_u_41_);
lean_dec(v_a_40_);
lean_dec(v_t_38_);
lean_dec(v_l_37_);
return v_res_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_LongGap(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_SafeMoves(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_CutExponentBounds(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_Lifting_LongGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Congruences_Lifting_SafeMoves(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
