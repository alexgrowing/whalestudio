// Lean compiler output
// Module: New.UpperBound.Objects.RowChain
// Imports: public import Init public meta import Init public import New.UpperBound.Objects.Rows
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_blockNumber___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_blockNumber___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__1(lean_object* v___x_1_, lean_object* v_x_2_){
_start:
{
lean_inc(v___x_1_);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__1___boxed(lean_object* v___x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_GRH_New_blockNumber___redArg___lam__1(v___x_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v___x_3_);
return v_res_5_;
}
}
static lean_object* _init_lp_GRH_New_blockNumber___redArg___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v_zero_7_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v_zero_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_mod(v_zero_7_, v___x_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__0___boxed(lean_object* v_n_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_New_blockNumber___redArg___lam__0(v_n_9_, v___y_10_);
lean_dec(v_n_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg(lean_object* v_x_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_zero_14_; uint8_t v_isZero_15_; 
v_zero_14_ = lean_unsigned_to_nat(0u);
v_isZero_15_ = lean_nat_dec_eq(v_x_12_, v_zero_14_);
if (v_isZero_15_ == 1)
{
lean_object* v___x_16_; 
lean_dec(v_a_13_);
v___x_16_ = lean_obj_once(&lp_GRH_New_blockNumber___redArg___closed__0, &lp_GRH_New_blockNumber___redArg___closed__0_once, _init_lp_GRH_New_blockNumber___redArg___closed__0);
return v___x_16_;
}
else
{
lean_object* v_one_17_; lean_object* v_n_18_; lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v_one_17_ = lean_unsigned_to_nat(1u);
v_n_18_ = lean_nat_sub(v_x_12_, v_one_17_);
lean_inc(v_n_18_);
v___f_19_ = lean_alloc_closure((void*)(lp_GRH_New_blockNumber___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_19_, 0, v_n_18_);
v___x_20_ = lean_nat_add(v_n_18_, v_one_17_);
lean_dec(v_n_18_);
v___f_21_ = lean_alloc_closure((void*)(lp_GRH_New_blockNumber___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_21_, 0, v___x_20_);
v___x_22_ = l_Sum_elim___redArg(v___f_19_, v___f_21_, v_a_13_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___lam__0(lean_object* v_n_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_GRH_New_blockNumber___redArg(v_n_23_, v___y_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___redArg___boxed(lean_object* v_x_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_blockNumber___redArg(v_x_26_, v_a_27_);
lean_dec(v_x_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber(lean_object* v_R_29_, lean_object* v_T_30_, lean_object* v_x_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_GRH_New_blockNumber___redArg(v_x_31_, v_a_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockNumber___boxed(lean_object* v_R_34_, lean_object* v_T_35_, lean_object* v_x_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_blockNumber(v_R_34_, v_T_35_, v_x_36_, v_a_37_);
lean_dec(v_x_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter___redArg(lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_41_);
v_val_42_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_val_42_);
lean_dec_ref_known(v_x_39_, 1);
v___x_43_ = lean_apply_1(v_h__1_40_, v_val_42_);
return v___x_43_;
}
else
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_h__1_40_);
v_val_44_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v_x_39_, 1);
v___x_45_ = lean_apply_1(v_h__2_41_, v_val_44_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter(lean_object* v_P_46_, lean_object* v_D_47_, lean_object* v_00_u03d1_48_, lean_object* v_motive_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_val_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_52_);
v_val_53_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v_x_50_, 1);
v___x_54_ = lean_apply_1(v_h__1_51_, v_val_53_);
return v___x_54_;
}
else
{
lean_object* v_val_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_51_);
v_val_55_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_val_55_);
lean_dec_ref_known(v_x_50_, 1);
v___x_56_ = lean_apply_1(v_h__2_52_, v_val_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter___boxed(lean_object* v_P_57_, lean_object* v_D_58_, lean_object* v_00_u03d1_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH___private_New_UpperBound_Objects_RowChain_0__New_Data_lastResidueLevel_match__1_splitter(v_P_57_, v_D_58_, v_00_u03d1_59_, v_motive_60_, v_x_61_, v_h__1_62_, v_h__2_63_);
lean_dec_ref(v_00_u03d1_59_);
lean_dec_ref(v_D_58_);
lean_dec_ref(v_P_57_);
return v_res_64_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_Rows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_RowChain(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_Objects_Rows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
