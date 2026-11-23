// Lean compiler output
// Module: Development.AutomorphicArithmetic.CharacterBoxes.PairGood
// Imports: public import Init public meta import Init public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00UpperTheory_Top_tw_spec__0(lean_object*);
static lean_once_cell_t lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UpperTheory_Top_tw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_UpperTheory_Top_tw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00UpperTheory_Top_tw_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v_a_1_);
v___x_3_ = lp_mathlib_Complex_ofReal(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_5_ = lp_mathlib_Complex_ofReal(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1(lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_zero_8_; uint8_t v_isZero_9_; 
v_zero_8_ = lean_unsigned_to_nat(0u);
v_isZero_9_ = lean_nat_dec_eq(v_x_6_, v_zero_8_);
if (v_isZero_9_ == 1)
{
lean_object* v___x_10_; 
lean_dec_ref(v_x_7_);
v___x_10_ = lean_obj_once(&lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___closed__0, &lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___closed__0_once, _init_lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___closed__0);
return v___x_10_;
}
else
{
lean_object* v_one_11_; lean_object* v_n_12_; lean_object* v___x_13_; lean_object* v_re_14_; lean_object* v_im_15_; lean_object* v___x_16_; 
v_one_11_ = lean_unsigned_to_nat(1u);
v_n_12_ = lean_nat_sub(v_x_6_, v_one_11_);
lean_inc_ref(v_x_7_);
v___x_13_ = lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1(v_n_12_, v_x_7_);
lean_dec(v_n_12_);
v_re_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_re_14_);
v_im_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_im_15_);
lean_dec_ref(v___x_13_);
v___x_16_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_14_, v_im_15_, v_x_7_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1(v_x_17_, v_x_18_);
lean_dec(v_x_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_UpperTheory_Top_tw(lean_object* v_00_u03be_20_, lean_object* v_q_21_, lean_object* v_d_22_, lean_object* v_i_23_, lean_object* v_j_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; lean_object* v_re_27_; lean_object* v_im_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_re_34_; lean_object* v_im_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc(v_a_25_);
v___x_26_ = lean_apply_1(v_00_u03be_20_, v_a_25_);
v_re_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_re_27_);
v_im_28_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_im_28_);
lean_dec_ref(v___x_26_);
v___x_29_ = lean_nat_to_int(v_a_25_);
v___x_30_ = lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(v___x_29_, v_q_21_);
v___x_31_ = lp_tree_Int_cast___at___00UpperTheory_Top_tw_spec__0(v___x_30_);
v___x_32_ = lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1(v_i_23_, v___x_31_);
v___x_33_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_27_, v_im_28_, v___x_32_);
v_re_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_re_34_);
v_im_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_im_35_);
lean_dec_ref(v___x_33_);
v___x_36_ = lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(v___x_29_, v_d_22_);
lean_dec(v___x_29_);
v___x_37_ = lp_tree_Int_cast___at___00UpperTheory_Top_tw_spec__0(v___x_36_);
v___x_38_ = lp_tree_npowRec___at___00UpperTheory_Top_tw_spec__1(v_j_24_, v___x_37_);
v___x_39_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_34_, v_im_35_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_UpperTheory_Top_tw___boxed(lean_object* v_00_u03be_40_, lean_object* v_q_41_, lean_object* v_d_42_, lean_object* v_i_43_, lean_object* v_j_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_UpperTheory_Top_tw(v_00_u03be_40_, v_q_41_, v_d_42_, v_i_43_, v_j_44_, v_a_45_);
lean_dec(v_j_44_);
lean_dec(v_i_43_);
return v_res_46_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AutomorphicArithmetic_CharacterBoxes_PairGood(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
