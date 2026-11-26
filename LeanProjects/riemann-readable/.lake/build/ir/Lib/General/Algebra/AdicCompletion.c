// Lean compiler output
// Module: Lib.General.Algebra.AdicCompletion
// Imports: public import Init public meta import Init public import Lib.Base
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendAction___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftDiff___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_00_u03c0_3_, lean_object* v_x_4_, lean_object* v_j_5_){
_start:
{
lean_object* v_toSub_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_toSub_6_ = lean_ctor_get(v_inst_1_, 2);
lean_inc(v_toSub_6_);
lean_dec_ref(v_inst_1_);
lean_inc(v_x_4_);
lean_inc(v_j_5_);
v___x_7_ = lean_apply_1(v_x_4_, v_j_5_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v_j_5_, v___x_8_);
lean_dec(v_j_5_);
v___x_10_ = lean_apply_1(v_x_4_, v___x_9_);
v___x_11_ = lean_apply_2(v_inst_2_, v_00_u03c0_3_, v___x_10_);
v___x_12_ = lean_apply_2(v_toSub_6_, v___x_7_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_shiftDiff(lean_object* v_R_13_, lean_object* v_N_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_00_u03c0_18_, lean_object* v_x_19_, lean_object* v_j_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_GRH_New_shiftDiff___redArg(v_inst_16_, v_inst_17_, v_00_u03c0_18_, v_x_19_, v_j_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_shiftDiff___boxed(lean_object* v_R_22_, lean_object* v_N_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_00_u03c0_27_, lean_object* v_x_28_, lean_object* v_j_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_shiftDiff(v_R_22_, v_N_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_00_u03c0_27_, v_x_28_, v_j_29_);
lean_dec_ref(v_inst_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms___redArg___lam__0(lean_object* v_f_31_, lean_object* v_m_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_apply_2(v_f_31_, v_m_32_, v___y_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms___redArg(lean_object* v_f_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = lean_alloc_closure((void*)(lp_GRH_New_actionOfHoms___redArg___lam__0), 3, 1);
lean_closure_set(v___f_36_, 0, v_f_35_);
return v___f_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms(lean_object* v_M_37_, lean_object* v_inst_38_, lean_object* v_B_39_, lean_object* v_inst_40_, lean_object* v_f_41_, lean_object* v_h__one_42_, lean_object* v_h__mul_43_){
_start:
{
lean_object* v___f_44_; 
v___f_44_ = lean_alloc_closure((void*)(lp_GRH_New_actionOfHoms___redArg___lam__0), 3, 1);
lean_closure_set(v___f_44_, 0, v_f_41_);
return v___f_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_actionOfHoms___boxed(lean_object* v_M_45_, lean_object* v_inst_46_, lean_object* v_B_47_, lean_object* v_inst_48_, lean_object* v_f_49_, lean_object* v_h__one_50_, lean_object* v_h__mul_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_GRH_New_actionOfHoms(v_M_45_, v_inst_46_, v_B_47_, v_inst_48_, v_f_49_, v_h__one_50_, v_h__mul_51_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendAction___redArg(lean_object* v_f_53_){
_start:
{
lean_object* v___f_54_; 
v___f_54_ = lean_alloc_closure((void*)(lp_GRH_New_actionOfHoms___redArg___lam__0), 3, 1);
lean_closure_set(v___f_54_, 0, v_f_53_);
return v___f_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendAction(lean_object* v_M_55_, lean_object* v_R_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_B_60_, lean_object* v_inst_61_, lean_object* v_i_62_, lean_object* v_f_63_, lean_object* v_hf_64_, lean_object* v_h__ext_65_){
_start:
{
lean_object* v___f_66_; 
v___f_66_ = lean_alloc_closure((void*)(lp_GRH_New_actionOfHoms___redArg___lam__0), 3, 1);
lean_closure_set(v___f_66_, 0, v_f_63_);
return v___f_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendAction___boxed(lean_object* v_M_67_, lean_object* v_R_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_B_72_, lean_object* v_inst_73_, lean_object* v_i_74_, lean_object* v_f_75_, lean_object* v_hf_76_, lean_object* v_h__ext_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_GRH_New_extendAction(v_M_67_, v_R_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_B_72_, v_inst_73_, v_i_74_, v_f_75_, v_hf_76_, v_h__ext_77_);
lean_dec(v_i_74_);
lean_dec_ref(v_inst_73_);
lean_dec(v_inst_71_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_69_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange___redArg(){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange___redArg___boxed(lean_object* v___dummy_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_GRH_New_Period_nsmulRange___redArg();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange(lean_object* v_n_83_, lean_object* v_X_84_, lean_object* v_inst_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_nsmulRange___boxed(lean_object* v_n_87_, lean_object* v_X_88_, lean_object* v_inst_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_GRH_New_Period_nsmulRange(v_n_87_, v_X_88_, v_inst_89_);
lean_dec_ref(v_inst_89_);
lean_dec(v_n_87_);
return v_res_90_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Algebra_AdicCompletion(uint8_t builtin) {
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
res = initialize_GRH_Lib_Base(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
