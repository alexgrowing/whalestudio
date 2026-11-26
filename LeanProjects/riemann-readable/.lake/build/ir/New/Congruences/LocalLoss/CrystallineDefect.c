// Lean compiler output
// Module: New.Congruences.LocalLoss.CrystallineDefect
// Imports: public import Init public meta import Init public import New.Congruences.LocalLoss.CrystallineCocycles public import New.Reduction.Data.Magnitudes
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
lean_object* v_zero_5_; uint8_t v_isZero_6_; 
v_zero_5_ = lean_unsigned_to_nat(0u);
v_isZero_6_ = lean_nat_dec_eq(v_x_1_, v_zero_5_);
if (v_isZero_6_ == 1)
{
lean_object* v___x_7_; 
lean_dec(v_h__2_4_);
v___x_7_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_3_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_x_1_, v_one_8_);
v___x_10_ = lean_apply_2(v_h__2_4_, v_n_9_, v_x_2_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___redArg___boxed(lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___redArg(v_x_11_, v_x_12_, v_h__1_13_, v_h__2_14_);
lean_dec(v_x_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter(lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_x_17_, v_zero_21_);
if (v_isZero_22_ == 1)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v___x_23_ = lean_apply_1(v_h__1_19_, v_x_18_);
return v___x_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_19_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_x_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, v_x_18_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter___boxed(lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_range_loop_match__1_splitter(v_motive_27_, v_x_28_, v_x_29_, v_h__1_30_, v_h__2_31_);
lean_dec(v_x_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___redArg(uint8_t v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (v_x_33_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_34_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__2_35_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_35_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_34_, v___x_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
uint8_t v_x_24__boxed_43_; lean_object* v_res_44_; 
v_x_24__boxed_43_ = lean_unbox(v_x_40_);
v_res_44_ = lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_43_, v_h__1_41_, v_h__2_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter(lean_object* v_motive_45_, uint8_t v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (v_x_46_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_47_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__2_48_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_48_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__1_47_, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
uint8_t v_x_35__boxed_57_; lean_object* v_res_58_; 
v_x_35__boxed_57_ = lean_unbox(v_x_54_);
v_res_58_ = lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__List_filter_match__1_splitter(v_motive_53_, v_x_35__boxed_57_, v_h__1_55_, v_h__2_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___redArg(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_){
_start:
{
lean_object* v_zero_64_; uint8_t v_isZero_65_; 
v_zero_64_ = lean_unsigned_to_nat(0u);
v_isZero_65_ = lean_nat_dec_eq(v_x_59_, v_zero_64_);
if (v_isZero_65_ == 1)
{
lean_object* v___x_66_; 
lean_dec(v_h__3_63_);
lean_dec(v_h__2_62_);
v___x_66_ = lean_apply_1(v_h__1_61_, v_x_60_);
return v___x_66_;
}
else
{
lean_object* v_one_67_; lean_object* v_n_68_; uint8_t v_isZero_69_; 
lean_dec(v_h__1_61_);
v_one_67_ = lean_unsigned_to_nat(1u);
v_n_68_ = lean_nat_sub(v_x_59_, v_one_67_);
v_isZero_69_ = lean_nat_dec_eq(v_x_60_, v_zero_64_);
if (v_isZero_69_ == 1)
{
lean_object* v___x_70_; 
lean_dec(v_h__3_63_);
lean_dec(v_x_60_);
v___x_70_ = lean_apply_1(v_h__2_62_, v_n_68_);
return v___x_70_;
}
else
{
lean_object* v_n_71_; lean_object* v___x_72_; 
lean_dec(v_h__2_62_);
v_n_71_ = lean_nat_sub(v_x_60_, v_one_67_);
lean_dec(v_x_60_);
v___x_72_ = lean_apply_2(v_h__3_63_, v_n_68_, v_n_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___redArg___boxed(lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___redArg(v_x_73_, v_x_74_, v_h__1_75_, v_h__2_76_, v_h__3_77_);
lean_dec(v_x_73_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter(lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
lean_object* v_zero_85_; uint8_t v_isZero_86_; 
v_zero_85_ = lean_unsigned_to_nat(0u);
v_isZero_86_ = lean_nat_dec_eq(v_x_80_, v_zero_85_);
if (v_isZero_86_ == 1)
{
lean_object* v___x_87_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__2_83_);
v___x_87_ = lean_apply_1(v_h__1_82_, v_x_81_);
return v___x_87_;
}
else
{
lean_object* v_one_88_; lean_object* v_n_89_; uint8_t v_isZero_90_; 
lean_dec(v_h__1_82_);
v_one_88_ = lean_unsigned_to_nat(1u);
v_n_89_ = lean_nat_sub(v_x_80_, v_one_88_);
v_isZero_90_ = lean_nat_dec_eq(v_x_81_, v_zero_85_);
if (v_isZero_90_ == 1)
{
lean_object* v___x_91_; 
lean_dec(v_h__3_84_);
lean_dec(v_x_81_);
v___x_91_ = lean_apply_1(v_h__2_83_, v_n_89_);
return v___x_91_;
}
else
{
lean_object* v_n_92_; lean_object* v___x_93_; 
lean_dec(v_h__2_83_);
v_n_92_ = lean_nat_sub(v_x_81_, v_one_88_);
lean_dec(v_x_81_);
v___x_93_ = lean_apply_2(v_h__3_84_, v_n_89_, v_n_92_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter___boxed(lean_object* v_motive_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_GRH___private_New_Congruences_LocalLoss_CrystallineDefect_0__Nat_ble_match__1_splitter(v_motive_94_, v_x_95_, v_x_96_, v_h__1_97_, v_h__2_98_, v_h__3_99_);
lean_dec(v_x_95_);
return v_res_100_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_LocalLoss_CrystallineCocycles(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Data_Magnitudes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_LocalLoss_CrystallineDefect(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_LocalLoss_CrystallineCocycles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Data_Magnitudes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
