// Lean compiler output
// Module: New.UpperBound.Seesaw.Cut
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.LatticeBounds public import New.UpperBound.Seesaw.IntegralAsCosetSum public import New.UpperBound.Seesaw.UnfoldingStages
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
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_apply_1(v_h__1_2_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_x_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__2_3_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___redArg___boxed(lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_x_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter(lean_object* v_P_14_, lean_object* v_D_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v_zero_21_; uint8_t v_isZero_22_; 
v_zero_21_ = lean_unsigned_to_nat(0u);
v_isZero_22_ = lean_nat_dec_eq(v_x_17_, v_zero_21_);
if (v_isZero_22_ == 1)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_20_);
v___x_23_ = lean_apply_1(v_h__1_19_, lean_box(0));
return v___x_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; 
lean_dec(v_h__1_19_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_x_17_, v_one_24_);
v___x_26_ = lean_apply_2(v_h__2_20_, v_n_25_, lean_box(0));
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter___boxed(lean_object* v_P_27_, lean_object* v_D_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutPoints_match__1_splitter(v_P_27_, v_D_28_, v_motive_29_, v_x_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_30_);
lean_dec_ref(v_D_28_);
lean_dec_ref(v_P_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
lean_object* v_zero_39_; uint8_t v_isZero_40_; 
v_zero_39_ = lean_unsigned_to_nat(0u);
v_isZero_40_ = lean_nat_dec_eq(v_x_35_, v_zero_39_);
if (v_isZero_40_ == 1)
{
lean_object* v___x_41_; 
lean_dec(v_h__2_38_);
v___x_41_ = lean_apply_2(v_h__1_37_, lean_box(0), v_x_36_);
return v___x_41_;
}
else
{
lean_object* v_one_42_; lean_object* v_n_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_37_);
v_one_42_ = lean_unsigned_to_nat(1u);
v_n_43_ = lean_nat_sub(v_x_35_, v_one_42_);
v___x_44_ = lean_apply_3(v_h__2_38_, v_n_43_, lean_box(0), v_x_36_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___redArg___boxed(lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___redArg(v_x_45_, v_x_46_, v_h__1_47_, v_h__2_48_);
lean_dec(v_x_45_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter(lean_object* v_P_50_, lean_object* v_D_51_, lean_object* v_00_u03d1_52_, lean_object* v_M_53_, lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
lean_object* v_zero_60_; uint8_t v_isZero_61_; 
v_zero_60_ = lean_unsigned_to_nat(0u);
v_isZero_61_ = lean_nat_dec_eq(v_x_55_, v_zero_60_);
if (v_isZero_61_ == 1)
{
lean_object* v___x_62_; 
lean_dec(v_h__2_59_);
v___x_62_ = lean_apply_2(v_h__1_58_, lean_box(0), v_x_57_);
return v___x_62_;
}
else
{
lean_object* v_one_63_; lean_object* v_n_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_58_);
v_one_63_ = lean_unsigned_to_nat(1u);
v_n_64_ = lean_nat_sub(v_x_55_, v_one_63_);
v___x_65_ = lean_apply_3(v_h__2_59_, v_n_64_, lean_box(0), v_x_57_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter___boxed(lean_object* v_P_66_, lean_object* v_D_67_, lean_object* v_00_u03d1_68_, lean_object* v_M_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH___private_New_UpperBound_Seesaw_Cut_0__New_Data_cutSum_match__1_splitter(v_P_66_, v_D_67_, v_00_u03d1_68_, v_M_69_, v_motive_70_, v_x_71_, v_x_72_, v_x_73_, v_h__1_74_, v_h__2_75_);
lean_dec(v_x_71_);
lean_dec_ref(v_00_u03d1_68_);
lean_dec_ref(v_D_67_);
lean_dec_ref(v_P_66_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_LatticeBounds(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_IntegralAsCosetSum(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_UnfoldingStages(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Seesaw_Cut(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_LatticeBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_IntegralAsCosetSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_UnfoldingStages(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
