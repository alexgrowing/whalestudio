// Lean compiler output
// Module: Lib.PadicComparison.Completion
// Imports: public import Init public meta import Init public import Lib.General.Algebra.CohomologyBaseChange
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
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_00_u03c0_4_, lean_object* v_y_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; lean_object* v_toAddMonoid_8_; lean_object* v_toSemiring_9_; lean_object* v_toMonoid_10_; lean_object* v_toZero_11_; lean_object* v_toAdd_12_; lean_object* v_toNPow_13_; lean_object* v_zero_14_; uint8_t v_isZero_15_; 
v___x_7_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_inst_2_);
v_toAddMonoid_8_ = lean_ctor_get(v_inst_2_, 0);
v_toSemiring_9_ = lean_ctor_get(v_inst_1_, 0);
v_toMonoid_10_ = lean_ctor_get(v_toSemiring_9_, 1);
v_toZero_11_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_toZero_11_);
lean_dec_ref(v___x_7_);
v_toAdd_12_ = lean_ctor_get(v_toAddMonoid_8_, 1);
lean_inc(v_toAdd_12_);
v_toNPow_13_ = lean_ctor_get(v_toMonoid_10_, 2);
lean_inc(v_toNPow_13_);
v_zero_14_ = lean_unsigned_to_nat(0u);
v_isZero_15_ = lean_nat_dec_eq(v_x_6_, v_zero_14_);
if (v_isZero_15_ == 1)
{
lean_dec(v_toNPow_13_);
lean_dec(v_toAdd_12_);
lean_dec(v_y_5_);
lean_dec(v_00_u03c0_4_);
lean_dec(v_inst_3_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
return v_toZero_11_;
}
else
{
lean_object* v_one_16_; lean_object* v_n_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_toZero_11_);
v_one_16_ = lean_unsigned_to_nat(1u);
v_n_17_ = lean_nat_sub(v_x_6_, v_one_16_);
lean_inc(v_y_5_);
lean_inc(v_00_u03c0_4_);
lean_inc(v_inst_3_);
v___x_18_ = lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg(v_inst_1_, v_inst_2_, v_inst_3_, v_00_u03c0_4_, v_y_5_, v_n_17_);
lean_inc(v_n_17_);
v___x_19_ = lean_apply_2(v_toNPow_13_, v_n_17_, v_00_u03c0_4_);
lean_inc(v___x_18_);
v___x_20_ = lean_apply_2(v_y_5_, v_n_17_, v___x_18_);
v___x_21_ = lean_apply_2(v_inst_3_, v___x_19_, v___x_20_);
v___x_22_ = lean_apply_2(v_toAdd_12_, v___x_18_, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg___boxed(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_00_u03c0_26_, lean_object* v_y_27_, lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg(v_inst_23_, v_inst_24_, v_inst_25_, v_00_u03c0_26_, v_y_27_, v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums(lean_object* v_W_30_, lean_object* v_inst_31_, lean_object* v_X_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_00_u03c0_35_, lean_object* v_y_36_, lean_object* v_x_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___redArg(v_inst_31_, v_inst_33_, v_inst_34_, v_00_u03c0_35_, v_y_36_, v_x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums___boxed(lean_object* v_W_39_, lean_object* v_inst_40_, lean_object* v_X_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_00_u03c0_44_, lean_object* v_y_45_, lean_object* v_x_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums(v_W_39_, v_inst_40_, v_X_41_, v_inst_42_, v_inst_43_, v_00_u03c0_44_, v_y_45_, v_x_46_);
lean_dec(v_x_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___redArg(lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
lean_object* v_zero_51_; uint8_t v_isZero_52_; 
v_zero_51_ = lean_unsigned_to_nat(0u);
v_isZero_52_ = lean_nat_dec_eq(v_x_48_, v_zero_51_);
if (v_isZero_52_ == 1)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_50_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__1_49_, v___x_53_);
return v___x_54_;
}
else
{
lean_object* v_one_55_; lean_object* v_n_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_49_);
v_one_55_ = lean_unsigned_to_nat(1u);
v_n_56_ = lean_nat_sub(v_x_48_, v_one_55_);
v___x_57_ = lean_apply_1(v_h__2_50_, v_n_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___redArg___boxed(lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___redArg(v_x_58_, v_h__1_59_, v_h__2_60_);
lean_dec(v_x_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter(lean_object* v_motive_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
lean_object* v_zero_66_; uint8_t v_isZero_67_; 
v_zero_66_ = lean_unsigned_to_nat(0u);
v_isZero_67_ = lean_nat_dec_eq(v_x_63_, v_zero_66_);
if (v_isZero_67_ == 1)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_h__2_65_);
v___x_68_ = lean_box(0);
v___x_69_ = lean_apply_1(v_h__1_64_, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_one_70_; lean_object* v_n_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_64_);
v_one_70_ = lean_unsigned_to_nat(1u);
v_n_71_ = lean_nat_sub(v_x_63_, v_one_70_);
v___x_72_ = lean_apply_1(v_h__2_65_, v_n_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter___boxed(lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_GRH___private_Lib_PadicComparison_Completion_0__New_Variety_partialSums_match__1_splitter(v_motive_73_, v_x_74_, v_h__1_75_, v_h__2_76_);
lean_dec(v_x_74_);
return v_res_77_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_CohomologyBaseChange(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicComparison_Completion(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Algebra_CohomologyBaseChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
