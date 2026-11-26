// Lean compiler output
// Module: New.Reduction.Data.LevelAndTwists
// Imports: public import Init public meta import Init public import Lib.ClassField.HeckeCharacter.SplitTameCharacters public import New.Derivatives.Field.ChosenPlaces
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_k___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_shiftedWeight___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Data_targetParameter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_targetParameter___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Data_targetParameter___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_targetParameter___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Data_targetParameter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_targetParameter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_targetParameter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Data_instCoeTwistTameChar___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Data_targetParameter___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Data_targetParameter___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_targetParameter___redArg(lean_object* v_D_5_, lean_object* v_v_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v_i_7_, v___x_8_);
v___x_10_ = lp_GRH_New_Data_k___redArg(v_D_5_);
v___x_11_ = lean_nat_dec_lt(v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_i_7_);
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lean_nat_sub(v___x_9_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v___x_9_);
v___x_14_ = lean_nat_mul(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_nat_add(v___x_14_, v___x_8_);
lean_dec(v___x_14_);
v___x_16_ = lp_GRH_New_Data_shiftedWeight___redArg(v_D_5_, v___x_15_, v_v_6_);
lean_dec(v___x_15_);
v___x_17_ = lean_nat_to_int(v___x_16_);
v___x_18_ = lean_int_neg(v___x_17_);
lean_dec(v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_9_);
lean_dec(v_v_6_);
lean_dec_ref(v_D_5_);
v___x_19_ = lean_nat_to_int(v___x_10_);
v___x_20_ = lean_obj_once(&lp_GRH_New_Data_targetParameter___redArg___closed__0, &lp_GRH_New_Data_targetParameter___redArg___closed__0_once, _init_lp_GRH_New_Data_targetParameter___redArg___closed__0);
v___x_21_ = lean_int_ediv(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_obj_once(&lp_GRH_New_Data_targetParameter___redArg___closed__1, &lp_GRH_New_Data_targetParameter___redArg___closed__1_once, _init_lp_GRH_New_Data_targetParameter___redArg___closed__1);
v___x_23_ = lean_int_sub(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_nat_to_int(v_i_7_);
v___x_25_ = lean_int_sub(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_targetParameter(lean_object* v_P_26_, lean_object* v_D_27_, lean_object* v_v_28_, lean_object* v_i_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_GRH_New_Data_targetParameter___redArg(v_D_27_, v_v_28_, v_i_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_targetParameter___boxed(lean_object* v_P_31_, lean_object* v_D_32_, lean_object* v_v_33_, lean_object* v_i_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_GRH_New_Data_targetParameter(v_P_31_, v_D_32_, v_v_33_, v_i_34_);
lean_dec_ref(v_P_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___lam__0(lean_object* v_self_36_){
_start:
{
lean_inc_ref(v_self_36_);
return v_self_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___lam__0___boxed(lean_object* v_self_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_Data_instCoeTwistTameChar___redArg___lam__0(v_self_37_);
lean_dec_ref(v_self_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg(){
_start:
{
lean_object* v___f_41_; 
v___f_41_ = ((lean_object*)(lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0));
return v___f_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___redArg___boxed(lean_object* v___dummy_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_GRH_New_Data_instCoeTwistTameChar___redArg();
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar(lean_object* v_P_44_, lean_object* v_D_45_){
_start:
{
lean_object* v___f_46_; 
v___f_46_ = ((lean_object*)(lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0));
return v___f_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeTwistTameChar___boxed(lean_object* v_P_47_, lean_object* v_D_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH_New_Data_instCoeTwistTameChar(v_P_47_, v_D_48_);
lean_dec_ref(v_D_48_);
lean_dec_ref(v_P_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist___redArg(){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = ((lean_object*)(lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0));
return v___f_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist___redArg___boxed(lean_object* v___dummy_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_GRH_New_Data_instCoeMFoldTwistTwist___redArg();
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist(lean_object* v_P_54_, lean_object* v_D_55_){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = ((lean_object*)(lp_GRH_New_Data_instCoeTwistTameChar___redArg___closed__0));
return v___f_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_instCoeMFoldTwistTwist___boxed(lean_object* v_P_57_, lean_object* v_D_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_GRH_New_Data_instCoeMFoldTwistTwist(v_P_57_, v_D_58_);
lean_dec_ref(v_D_58_);
lean_dec_ref(v_P_57_);
return v_res_59_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_SplitTameCharacters(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Field_ChosenPlaces(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Reduction_Data_LevelAndTwists(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_HeckeCharacter_SplitTameCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Derivatives_Field_ChosenPlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
