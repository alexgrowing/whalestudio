// Lean compiler output
// Module: New.OneLift.ComparisonOperator.ThreeExchanges
// Imports: public import Init public meta import Init public import Lib.SiegelWeil.Reproduction public import New.Determinant.Exchange.ExplicitMatching public import New.OneLift.ComparisonOperator.FirstFactors
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_k___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Data_signPoint___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_signPoint___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_OneLift_ComparisonOperator_ThreeExchanges_0__New_Data_exchangePair_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_OneLift_ComparisonOperator_ThreeExchanges_0__New_Data_exchangePair_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Data_signPoint___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint___redArg(lean_object* v_D_3_, lean_object* v_s_4_){
_start:
{
lean_object* v_val_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_val_5_ = lean_ctor_get(v_s_4_, 0);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_obj_once(&lp_GRH_New_Data_signPoint___redArg___closed__0, &lp_GRH_New_Data_signPoint___redArg___closed__0_once, _init_lp_GRH_New_Data_signPoint___redArg___closed__0);
v___x_8_ = lean_int_dec_eq(v_val_5_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v_m_9_; lean_object* v___x_10_; 
v_m_9_ = lean_ctor_get(v_D_3_, 6);
v___x_10_ = lean_nat_shiftr(v_m_9_, v___x_6_);
return v___x_10_;
}
else
{
lean_object* v_m_11_; 
v_m_11_ = lean_ctor_get(v_D_3_, 6);
lean_inc(v_m_11_);
return v_m_11_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint___redArg___boxed(lean_object* v_D_12_, lean_object* v_s_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Data_signPoint___redArg(v_D_12_, v_s_13_);
lean_dec_ref(v_s_13_);
lean_dec_ref(v_D_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint(lean_object* v_P_15_, lean_object* v_D_16_, lean_object* v_s_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_GRH_New_Data_signPoint___redArg(v_D_16_, v_s_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_signPoint___boxed(lean_object* v_P_19_, lean_object* v_D_20_, lean_object* v_s_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_Data_signPoint(v_P_19_, v_D_20_, v_s_21_);
lean_dec_ref(v_s_21_);
lean_dec_ref(v_D_20_);
lean_dec_ref(v_P_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint___redArg(lean_object* v_D_23_){
_start:
{
lean_object* v_m_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_m_24_ = lean_ctor_get(v_D_23_, 6);
v___x_25_ = lean_unsigned_to_nat(7u);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_shiftr(v_m_24_, v___x_26_);
v___x_28_ = lean_nat_mul(v___x_25_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lp_GRH_New_Data_k___redArg(v_D_23_);
v___x_30_ = lean_nat_shiftr(v___x_29_, v___x_26_);
lean_dec(v___x_29_);
v___x_31_ = lean_nat_add(v___x_28_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint___redArg___boxed(lean_object* v_D_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_Data_mainPairPoint___redArg(v_D_32_);
lean_dec_ref(v_D_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint(lean_object* v_P_34_, lean_object* v_D_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_GRH_New_Data_mainPairPoint___redArg(v_D_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_mainPairPoint___boxed(lean_object* v_P_37_, lean_object* v_D_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_GRH_New_Data_mainPairPoint(v_P_37_, v_D_38_);
lean_dec_ref(v_D_38_);
lean_dec_ref(v_P_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_OneLift_ComparisonOperator_ThreeExchanges_0__New_Data_exchangePair_match__1_splitter___redArg(lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__2_42_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_1(v_h__1_41_, v___x_43_);
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_41_);
v_val_45_ = lean_ctor_get(v_x_40_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v_x_40_, 1);
v___x_46_ = lean_apply_1(v_h__2_42_, v_val_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_OneLift_ComparisonOperator_ThreeExchanges_0__New_Data_exchangePair_match__1_splitter(lean_object* v_motive_47_, lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_50_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__1_49_, v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_49_);
v_val_53_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v_x_48_, 1);
v___x_54_ = lean_apply_1(v_h__2_50_, v_val_53_);
return v___x_54_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Reproduction(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Exchange_ExplicitMatching(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_FirstFactors(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ThreeExchanges(uint8_t builtin) {
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
res = initialize_GRH_Lib_SiegelWeil_Reproduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Exchange_ExplicitMatching(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_FirstFactors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
