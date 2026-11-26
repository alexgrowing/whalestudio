// Lean compiler output
// Module: New.OneLift.ComparisonOperator.ProductsSpan
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bruhat.ComplexPlace public import New.OneLift.ComparisonOperator.ThetaKernelEstimates public import New.OneLift.ComparisonOperator.ThreeExchanges
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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_reducedHalfGap___redArg(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(6u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__0(lean_object* v_D_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_m_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_m_7_ = lean_ctor_get(v_D_5_, 6);
lean_inc(v_m_7_);
lean_dec_ref(v_D_5_);
v___x_8_ = lean_obj_once(&lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__0, &lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__0);
v___x_9_ = lean_nat_to_int(v_m_7_);
v___x_10_ = lean_int_mul(v___x_8_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = lean_obj_once(&lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__1, &lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___closed__1);
v___x_12_ = lean_int_add(v___x_10_, v___x_11_);
lean_dec(v___x_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___boxed(lean_object* v_D_13_, lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_GRH_New_Data_flatKernelWeight___redArg___lam__0(v_D_13_, v_x_14_);
lean_dec(v_x_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__1(lean_object* v_D_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lp_GRH_New_Data_reducedHalfGap___redArg(v_D_16_);
v___x_19_ = lean_nat_to_int(v___x_18_);
v___x_20_ = lean_int_neg(v___x_19_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg___lam__1___boxed(lean_object* v_D_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_Data_flatKernelWeight___redArg___lam__1(v_D_21_, v_x_22_);
lean_dec(v_x_22_);
lean_dec_ref(v_D_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___redArg(lean_object* v_D_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; 
lean_inc_ref(v_D_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_GRH_New_Data_flatKernelWeight___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_26_, 0, v_D_24_);
v___f_27_ = lean_alloc_closure((void*)(lp_GRH_New_Data_flatKernelWeight___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_27_, 0, v_D_24_);
v___x_28_ = l_Sum_elim___redArg(v___f_27_, v___f_26_, v_a_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight(lean_object* v_P_29_, lean_object* v_D_30_, lean_object* v_x_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_GRH_New_Data_flatKernelWeight___redArg(v_D_30_, v_a_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_flatKernelWeight___boxed(lean_object* v_P_34_, lean_object* v_D_35_, lean_object* v_x_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_Data_flatKernelWeight(v_P_34_, v_D_35_, v_x_36_, v_a_37_);
lean_dec(v_x_36_);
lean_dec_ref(v_P_34_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_ComplexPlace(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ThetaKernelEstimates(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ThreeExchanges(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ProductsSpan(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_ComplexPlace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_ThetaKernelEstimates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_ThreeExchanges(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
