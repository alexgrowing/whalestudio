// Lean compiler output
// Module: Lib.General.NumberTheory.ImaginaryQuadraticField
// Imports: public import Init public meta import Init public import Lib.General.NumberTheory.EmbeddingsAndDifferent
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
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_quadraticChar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_chiK___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_chiK(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_primeNorm___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_primeNorm___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_primeNorm___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_primeNorm___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_primeNorm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_primeNorm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_chiK___redArg(lean_object* v_d_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
lean_inc(v_d_1_);
v___x_2_ = lp_mathlib_ZMod_instField___redArg(v_d_1_);
v___x_3_ = lp_mathlib_ZMod_fintype___redArg(v_d_1_);
v___x_4_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_4_, 0, v_d_1_);
v___x_5_ = lp_mathlib_quadraticChar___redArg(v___x_2_, v___x_3_, v___x_4_);
lean_dec_ref(v___x_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_chiK(lean_object* v_d_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_GRH_New_chiK___redArg(v_d_6_);
return v___x_8_;
}
}
static lean_object* _init_lp_GRH_New_primeNorm___redArg___closed__0(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_to_int(v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_lp_GRH_New_primeNorm___redArg___closed__1(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&lp_GRH_New_primeNorm___redArg___closed__0, &lp_GRH_New_primeNorm___redArg___closed__0_once, _init_lp_GRH_New_primeNorm___redArg___closed__0);
v___x_12_ = lean_int_neg(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_primeNorm___redArg(lean_object* v_d_13_, lean_object* v_p_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toRing_17_; lean_object* v___x_18_; lean_object* v_toAddMonoidWithOne_19_; lean_object* v_toNatCast_20_; lean_object* v___x_21_; lean_object* v___x_72__overap_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
lean_inc(v_d_13_);
v___x_15_ = lp_mathlib_ZMod_instField___redArg(v_d_13_);
v___x_16_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_15_);
v_toRing_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_toRing_17_);
lean_dec_ref(v___x_16_);
v___x_18_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_17_);
v_toAddMonoidWithOne_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc_ref(v_toAddMonoidWithOne_19_);
lean_dec_ref(v___x_18_);
v_toNatCast_20_ = lean_ctor_get(v_toAddMonoidWithOne_19_, 0);
lean_inc(v_toNatCast_20_);
lean_dec_ref(v_toAddMonoidWithOne_19_);
lean_inc(v_p_14_);
v___x_21_ = lean_apply_1(v_toNatCast_20_, v_p_14_);
v___x_72__overap_22_ = lp_GRH_New_chiK___redArg(v_d_13_);
v___x_23_ = lean_apply_1(v___x_72__overap_22_, v___x_21_);
v___x_24_ = lean_obj_once(&lp_GRH_New_primeNorm___redArg___closed__1, &lp_GRH_New_primeNorm___redArg___closed__1_once, _init_lp_GRH_New_primeNorm___redArg___closed__1);
v___x_25_ = lean_int_dec_eq(v___x_23_, v___x_24_);
lean_dec(v___x_23_);
if (v___x_25_ == 0)
{
return v_p_14_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(2u);
v___x_27_ = lean_nat_pow(v_p_14_, v___x_26_);
lean_dec(v_p_14_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_primeNorm(lean_object* v_d_28_, lean_object* v_p_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v_toRing_33_; lean_object* v___x_34_; lean_object* v_toAddMonoidWithOne_35_; lean_object* v_toNatCast_36_; lean_object* v___x_37_; lean_object* v___x_95__overap_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
lean_inc(v_d_28_);
v___x_31_ = lp_mathlib_ZMod_instField___redArg(v_d_28_);
v___x_32_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_31_);
v_toRing_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc_ref(v_toRing_33_);
lean_dec_ref(v___x_32_);
v___x_34_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_33_);
v_toAddMonoidWithOne_35_ = lean_ctor_get(v___x_34_, 1);
lean_inc_ref(v_toAddMonoidWithOne_35_);
lean_dec_ref(v___x_34_);
v_toNatCast_36_ = lean_ctor_get(v_toAddMonoidWithOne_35_, 0);
lean_inc(v_toNatCast_36_);
lean_dec_ref(v_toAddMonoidWithOne_35_);
lean_inc(v_p_29_);
v___x_37_ = lean_apply_1(v_toNatCast_36_, v_p_29_);
v___x_95__overap_38_ = lp_GRH_New_chiK___redArg(v_d_28_);
v___x_39_ = lean_apply_1(v___x_95__overap_38_, v___x_37_);
v___x_40_ = lean_obj_once(&lp_GRH_New_primeNorm___redArg___closed__1, &lp_GRH_New_primeNorm___redArg___closed__1_once, _init_lp_GRH_New_primeNorm___redArg___closed__1);
v___x_41_ = lean_int_dec_eq(v___x_39_, v___x_40_);
lean_dec(v___x_39_);
if (v___x_41_ == 0)
{
return v_p_29_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lean_nat_pow(v_p_29_, v___x_42_);
lean_dec(v_p_29_);
return v___x_43_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_EmbeddingsAndDifferent(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_NumberTheory_EmbeddingsAndDifferent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
