// Lean compiler output
// Module: New.Congruences.Lifting.FewLowJumps
// Imports: public import Init public meta import Init public import New.Congruences.Lifting.DeepPoints
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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_GRH_New_Lift_raisedOrdersAtZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_abs___at___00New_Lift_KummerChart_PairingSide_negativeWindowDepth_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_abs___at___00New_Lift_KummerChart_PairingSide_negativeWindowDepth_spec__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_abs___at___00New_Lift_KummerChart_PairingSide_negativeWindowDepth_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; 
v___x_2_ = lean_int_neg(v_a_1_);
v___x_3_ = lean_int_dec_le(v_a_1_, v___x_2_);
if (v___x_3_ == 0)
{
lean_dec(v___x_2_);
lean_inc(v_a_1_);
return v_a_1_;
}
else
{
return v___x_2_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_abs___at___00New_Lift_KummerChart_PairingSide_negativeWindowDepth_spec__0___boxed(lean_object* v_a_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_GRH_abs___at___00New_Lift_KummerChart_PairingSide_negativeWindowDepth_spec__0(v_a_4_);
lean_dec(v_a_4_);
return v_res_5_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_to_int(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth(lean_object* v_a_8_, lean_object* v_00_u03b7_9_, lean_object* v_W_10_, lean_object* v_b_11_, lean_object* v_l_12_, lean_object* v_u_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_dec_eq(v_l_12_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; uint8_t v___x_17_; 
lean_dec(v_b_11_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_dec_eq(v_l_12_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
lean_dec(v_W_10_);
lean_dec(v_00_u03b7_9_);
lean_dec(v_a_8_);
v___x_18_ = lean_int_neg(v_u_13_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___y_24_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_19_ = lean_nat_to_int(v_W_10_);
v___x_20_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0);
v___x_21_ = lean_int_add(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_int_sub(v___x_21_, v_u_13_);
lean_dec(v___x_21_);
v___x_27_ = lp_GRH_abs___at___00New_Lift_KummerChart_PairingSide_negativeWindowDepth_spec__0(v_u_13_);
v___x_28_ = lean_nat_to_int(v_00_u03b7_9_);
v___x_29_ = lean_int_dec_le(v___x_27_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_27_);
if (v___x_29_ == 0)
{
lean_dec(v_a_8_);
v___y_24_ = v___x_14_;
goto v___jp_23_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(2u);
v___x_31_ = lean_nat_mul(v___x_30_, v_a_8_);
lean_dec(v_a_8_);
v___y_24_ = v___x_31_;
goto v___jp_23_;
}
v___jp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_nat_to_int(v___y_24_);
v___x_26_ = lean_int_add(v___x_22_, v___x_25_);
lean_dec(v___x_25_);
lean_dec(v___x_22_);
return v___x_26_;
}
}
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_32_ = lean_nat_to_int(v_b_11_);
v___x_33_ = lean_nat_to_int(v_W_10_);
v___x_34_ = lean_int_add(v___x_32_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_nat_to_int(v_a_8_);
v___x_36_ = lean_int_add(v___x_34_, v___x_35_);
lean_dec(v___x_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_nat_to_int(v_00_u03b7_9_);
v___x_38_ = lean_int_add(v___x_36_, v___x_37_);
lean_dec(v___x_37_);
lean_dec(v___x_36_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___boxed(lean_object* v_a_39_, lean_object* v_00_u03b7_40_, lean_object* v_W_41_, lean_object* v_b_42_, lean_object* v_l_43_, lean_object* v_u_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth(v_a_39_, v_00_u03b7_40_, v_W_41_, v_b_42_, v_l_43_, v_u_44_);
lean_dec(v_u_44_);
lean_dec(v_l_43_);
return v_res_45_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(2u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth(lean_object* v_a_48_, lean_object* v_00_u03b7_49_, lean_object* v_W_50_, lean_object* v_b_51_, lean_object* v_00_u03b5_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_val_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_val_55_ = lean_ctor_get(v_00_u03b5_52_, 0);
v___x_56_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth___closed__0);
v___x_57_ = lean_int_dec_eq(v_val_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lp_GRH_New_Lift_KummerChart_PairingSide_negativeWindowDepth(v_a_48_, v_00_u03b7_49_, v_W_50_, v_b_51_, v_a_53_, v_a_54_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_b_51_);
lean_dec(v_W_50_);
v___x_59_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___closed__0);
v___x_60_ = lean_nat_to_int(v_a_48_);
v___x_61_ = lean_int_mul(v___x_59_, v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = lean_nat_to_int(v_00_u03b7_49_);
v___x_63_ = lean_int_add(v___x_61_, v___x_62_);
lean_dec(v___x_62_);
lean_dec(v___x_61_);
v___x_64_ = lp_GRH_New_Lift_raisedOrdersAtZero(v___x_63_, v_a_53_, v_a_54_);
lean_dec(v___x_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth___boxed(lean_object* v_a_65_, lean_object* v_00_u03b7_66_, lean_object* v_W_67_, lean_object* v_b_68_, lean_object* v_00_u03b5_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_GRH_New_Lift_KummerChart_PairingSide_fewLowJumpsDepth(v_a_65_, v_00_u03b7_66_, v_W_67_, v_b_68_, v_00_u03b5_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_00_u03b5_69_);
return v_res_72_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_DeepPoints(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_FewLowJumps(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_Lifting_DeepPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
