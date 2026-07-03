// Lean compiler output
// Module: MyProject.Basic
// Imports: public import Init public meta import Init
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_double(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_double___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_factorial(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_factorial___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_fibonacci(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_fibonacci___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_myProject_MyProject_isEven(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_isEven___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_myMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_myMax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_myProject_MyProject_double(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(2u);
v___x_3_ = lean_nat_mul(v_n_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_double___boxed(lean_object* v_n_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_myProject_MyProject_double(v_n_4_);
lean_dec(v_n_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_factorial(lean_object* v_x_6_){
_start:
{
lean_object* v_zero_7_; uint8_t v_isZero_8_; 
v_zero_7_ = lean_unsigned_to_nat(0u);
v_isZero_8_ = lean_nat_dec_eq(v_x_6_, v_zero_7_);
if (v_isZero_8_ == 1)
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(1u);
return v___x_9_;
}
else
{
lean_object* v_one_10_; lean_object* v_n_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_one_10_ = lean_unsigned_to_nat(1u);
v_n_11_ = lean_nat_sub(v_x_6_, v_one_10_);
v___x_12_ = lean_nat_add(v_n_11_, v_one_10_);
v___x_13_ = lp_myProject_MyProject_factorial(v_n_11_);
lean_dec(v_n_11_);
v___x_14_ = lean_nat_mul(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_12_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_factorial___boxed(lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_myProject_MyProject_factorial(v_x_15_);
lean_dec(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_fibonacci(lean_object* v_x_17_){
_start:
{
lean_object* v_zero_18_; uint8_t v_isZero_19_; 
v_zero_18_ = lean_unsigned_to_nat(0u);
v_isZero_19_ = lean_nat_dec_eq(v_x_17_, v_zero_18_);
if (v_isZero_19_ == 1)
{
return v_zero_18_;
}
else
{
lean_object* v_one_20_; lean_object* v_n_21_; uint8_t v_isZero_22_; 
v_one_20_ = lean_unsigned_to_nat(1u);
v_n_21_ = lean_nat_sub(v_x_17_, v_one_20_);
v_isZero_22_ = lean_nat_dec_eq(v_n_21_, v_zero_18_);
if (v_isZero_22_ == 1)
{
lean_dec(v_n_21_);
return v_one_20_;
}
else
{
lean_object* v_n_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_n_23_ = lean_nat_sub(v_n_21_, v_one_20_);
lean_dec(v_n_21_);
v___x_24_ = lp_myProject_MyProject_fibonacci(v_n_23_);
v___x_25_ = lean_nat_add(v_n_23_, v_one_20_);
lean_dec(v_n_23_);
v___x_26_ = lp_myProject_MyProject_fibonacci(v___x_25_);
lean_dec(v___x_25_);
v___x_27_ = lean_nat_add(v___x_24_, v___x_26_);
lean_dec(v___x_26_);
lean_dec(v___x_24_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_fibonacci___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_myProject_MyProject_fibonacci(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t lp_myProject_MyProject_isEven(lean_object* v_n_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_31_ = lean_unsigned_to_nat(2u);
v___x_32_ = lean_nat_mod(v_n_30_, v___x_31_);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_nat_dec_eq(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_isEven___boxed(lean_object* v_n_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = lp_myProject_MyProject_isEven(v_n_35_);
lean_dec(v_n_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_myMax(lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = lean_nat_dec_le(v_a_38_, v_b_39_);
if (v___x_40_ == 0)
{
lean_inc(v_a_38_);
return v_a_38_;
}
else
{
lean_inc(v_b_39_);
return v_b_39_;
}
}
}
LEAN_EXPORT lean_object* lp_myProject_MyProject_myMax___boxed(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_myProject_MyProject_myMax(v_a_41_, v_b_42_);
lean_dec(v_b_42_);
lean_dec(v_a_41_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_myProject_MyProject_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
