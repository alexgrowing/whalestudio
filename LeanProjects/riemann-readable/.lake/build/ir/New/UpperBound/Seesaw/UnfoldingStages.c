// Lean compiler output
// Module: New.UpperBound.Seesaw.UnfoldingStages
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.Unfolding public import New.UpperBound.Objects.CharactersAtLevel public import New.UpperBound.Objects.RowChain public import New.UpperBound.Seesaw.Frequency public import New.UpperBound.Seesaw.GluedLevel public import New.UpperBound.Seesaw.LevelIdeles public import New.UpperBound.Seesaw.Sandwich
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
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___redArg___boxed(lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_x_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter(lean_object* v_P_14_, lean_object* v_D_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
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
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter___boxed(lean_object* v_P_27_, lean_object* v_D_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH___private_New_UpperBound_Seesaw_UnfoldingStages_0__New_Data_unfoldStageOn_match__1_splitter(v_P_27_, v_D_28_, v_motive_29_, v_x_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_30_);
lean_dec_ref(v_D_28_);
lean_dec_ref(v_P_27_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_Unfolding(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_CharactersAtLevel(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_RowChain(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_Frequency(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_GluedLevel(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_LevelIdeles(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Seesaw_Sandwich(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Seesaw_UnfoldingStages(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_Unfolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_CharactersAtLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_RowChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_Frequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_GluedLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_LevelIdeles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Seesaw_Sandwich(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
