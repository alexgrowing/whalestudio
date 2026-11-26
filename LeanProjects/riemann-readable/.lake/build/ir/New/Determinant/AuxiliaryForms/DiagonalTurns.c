// Lean compiler output
// Module: New.Determinant.AuxiliaryForms.DiagonalTurns
// Imports: public import Init public meta import Init public import New.Determinant.AuxiliaryForms.Turns
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
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___redArg___lam__0(lean_object* v_q_1_, lean_object* v_j_2_, uint8_t v_b_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(v_b_3_);
v___x_5_ = lean_apply_1(v_q_1_, v___x_4_);
lean_inc(v_j_2_);
v___x_6_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6_, 0, v_j_2_);
lean_ctor_set(v___x_6_, 1, v_j_2_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___redArg___lam__0___boxed(lean_object* v_q_7_, lean_object* v_j_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_b_boxed_10_; lean_object* v_res_11_; 
v_b_boxed_10_ = lean_unbox(v_b_9_);
v_res_11_ = lp_GRH_New_Data_downPath___redArg___lam__0(v_q_7_, v_j_8_, v_b_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___redArg(lean_object* v_j_12_, lean_object* v_q_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; 
lean_inc(v_j_12_);
v___f_14_ = lean_alloc_closure((void*)(lp_GRH_New_Data_downPath___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_14_, 0, v_q_13_);
lean_closure_set(v___f_14_, 1, v_j_12_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_j_12_);
lean_ctor_set(v___x_15_, 1, v___f_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath(lean_object* v_P_16_, lean_object* v_D_17_, lean_object* v_j_18_, lean_object* v_q_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; 
lean_inc(v_j_18_);
v___f_20_ = lean_alloc_closure((void*)(lp_GRH_New_Data_downPath___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_20_, 0, v_q_19_);
lean_closure_set(v___f_20_, 1, v_j_18_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_j_18_);
lean_ctor_set(v___x_21_, 1, v___f_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_downPath___boxed(lean_object* v_P_22_, lean_object* v_D_23_, lean_object* v_j_24_, lean_object* v_q_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Data_downPath(v_P_22_, v_D_23_, v_j_24_, v_q_25_);
lean_dec_ref(v_D_23_);
lean_dec_ref(v_P_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___redArg___lam__0(lean_object* v_q_27_, lean_object* v_j_28_, lean_object* v___x_29_, uint8_t v_b_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(v_b_30_);
v___x_32_ = lean_apply_1(v_q_27_, v___x_31_);
v___x_33_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_33_, 0, v_j_28_);
lean_ctor_set(v___x_33_, 1, v___x_29_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___redArg___lam__0___boxed(lean_object* v_q_34_, lean_object* v_j_35_, lean_object* v___x_36_, lean_object* v_b_37_){
_start:
{
uint8_t v_b_boxed_38_; lean_object* v_res_39_; 
v_b_boxed_38_ = lean_unbox(v_b_37_);
v_res_39_ = lp_GRH_New_Data_rightPath___redArg___lam__0(v_q_34_, v_j_35_, v___x_36_, v_b_boxed_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___redArg(lean_object* v_j_40_, lean_object* v_q_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___f_44_; lean_object* v___x_45_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_j_40_, v___x_42_);
lean_inc(v___x_43_);
v___f_44_ = lean_alloc_closure((void*)(lp_GRH_New_Data_rightPath___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_44_, 0, v_q_41_);
lean_closure_set(v___f_44_, 1, v_j_40_);
lean_closure_set(v___f_44_, 2, v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___f_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath(lean_object* v_P_46_, lean_object* v_D_47_, lean_object* v_j_48_, lean_object* v_q_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_add(v_j_48_, v___x_50_);
lean_inc(v___x_51_);
v___f_52_ = lean_alloc_closure((void*)(lp_GRH_New_Data_rightPath___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_52_, 0, v_q_49_);
lean_closure_set(v___f_52_, 1, v_j_48_);
lean_closure_set(v___f_52_, 2, v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___f_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rightPath___boxed(lean_object* v_P_54_, lean_object* v_D_55_, lean_object* v_j_56_, lean_object* v_q_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_GRH_New_Data_rightPath(v_P_54_, v_D_55_, v_j_56_, v_q_57_);
lean_dec_ref(v_D_55_);
lean_dec_ref(v_P_54_);
return v_res_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_Turns(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_DiagonalTurns(uint8_t builtin) {
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
res = initialize_GRH_New_Determinant_AuxiliaryForms_Turns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
