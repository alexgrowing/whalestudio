// Lean compiler output
// Module: New.OneLift.ComparisonOperator.ExchangeData
// Imports: public import Init public meta import Init public import Lib.Weil.DualPair.HolomorphicData public import New.OneLift.HeckeValues.CharacterLift public import New.UpperBound.Objects.Rows
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
lean_object* lp_GRH_New_Data_t___redArg(lean_object*);
lean_object* lp_GRH_New_Data_k___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Rows_unitModulus___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Rows_unitModulus___boxed(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Rows_unitModulus(v_E_10_, v_inst_11_, v_inst_12_, v_inst_13_);
lean_dec_ref(v_inst_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp___redArg(lean_object* v_D_15_, lean_object* v_j_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_17_ = lp_GRH_New_Data_t___redArg(v_D_15_);
v___x_18_ = lp_GRH_New_Data_k___redArg(v_D_15_);
v___x_19_ = lean_nat_add(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_nat_sub(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_nat_shiftr(v___x_21_, v___x_20_);
lean_dec(v___x_21_);
v___x_23_ = lean_nat_add(v_j_16_, v___x_22_);
lean_dec(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp___redArg___boxed(lean_object* v_D_24_, lean_object* v_j_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Data_firstFactorCharExp___redArg(v_D_24_, v_j_25_);
lean_dec(v_j_25_);
lean_dec_ref(v_D_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp(lean_object* v_P_27_, lean_object* v_D_28_, lean_object* v_j_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_30_ = lp_GRH_New_Data_t___redArg(v_D_28_);
v___x_31_ = lp_GRH_New_Data_k___redArg(v_D_28_);
v___x_32_ = lean_nat_add(v___x_30_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_sub(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_nat_shiftr(v___x_34_, v___x_33_);
lean_dec(v___x_34_);
v___x_36_ = lean_nat_add(v_j_29_, v___x_35_);
lean_dec(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_firstFactorCharExp___boxed(lean_object* v_P_37_, lean_object* v_D_38_, lean_object* v_j_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_GRH_New_Data_firstFactorCharExp(v_P_37_, v_D_38_, v_j_39_);
lean_dec(v_j_39_);
lean_dec_ref(v_D_38_);
lean_dec_ref(v_P_37_);
return v_res_40_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_HolomorphicData(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_HeckeValues_CharacterLift(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ExchangeData(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_DualPair_HolomorphicData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_HeckeValues_CharacterLift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_Rows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
