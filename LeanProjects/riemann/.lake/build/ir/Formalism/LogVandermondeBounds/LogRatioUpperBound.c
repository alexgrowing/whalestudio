// Lean compiler output
// Module: Formalism.LogVandermondeBounds.LogRatioUpperBound
// Imports: public import Init public meta import Init public import Formalism.LogVandermondeBounds.LogRatioLowerBound
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_Ioo___at___00Formalism_LogVandermondeBounds_StandardLattice_nBetween_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_Ioo___at___00Formalism_LogVandermondeBounds_StandardLattice_nBetween_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign(lean_object* v_k_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_sub(v_k_1_, v___x_3_);
v___x_5_ = lean_nat_dec_lt(v_i_2_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_6_ = lean_nat_sub(v_i_2_, v___x_4_);
lean_dec(v___x_4_);
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lean_nat_mod(v___x_6_, v___x_7_);
lean_dec(v___x_6_);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_dec_eq(v___x_8_, v___x_9_);
lean_dec(v___x_8_);
return v___x_10_;
}
else
{
lean_dec(v___x_4_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign___boxed(lean_object* v_k_11_, lean_object* v_i_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign(v_k_11_, v_i_12_);
lean_dec(v_i_12_);
lean_dec(v_k_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_Ioo___at___00Formalism_LogVandermondeBounds_StandardLattice_nBetween_spec__0(lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_add(v_a_15_, v___x_17_);
v___x_19_ = lean_nat_sub(v_b_16_, v_a_15_);
v___x_20_ = lean_nat_sub(v___x_19_, v___x_17_);
lean_dec(v___x_19_);
v___x_21_ = lean_nat_add(v___x_18_, v___x_20_);
lean_dec(v___x_18_);
v___x_22_ = lean_box(0);
v___x_23_ = l_List_range_x27TR_go(v___x_17_, v___x_20_, v___x_21_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_Ioo___at___00Formalism_LogVandermondeBounds_StandardLattice_nBetween_spec__0___boxed(lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Finset_Ioo___at___00Formalism_LogVandermondeBounds_StandardLattice_nBetween_spec__0(v_a_24_, v_b_25_);
lean_dec(v_b_25_);
lean_dec(v_a_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___lam__0(lean_object* v_k_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign(v_k_27_, v_a_29_);
v___x_31_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_plusSign(v_k_27_, v_a_28_);
if (v___x_30_ == 0)
{
if (v___x_31_ == 0)
{
return v___x_31_;
}
else
{
if (v___x_30_ == 0)
{
return v___x_31_;
}
else
{
return v___x_30_;
}
}
}
else
{
if (v___x_31_ == 0)
{
if (v___x_31_ == 0)
{
return v___x_30_;
}
else
{
return v___x_31_;
}
}
else
{
if (v___x_31_ == 0)
{
return v___x_31_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 0;
return v___x_32_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___lam__0___boxed(lean_object* v_k_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___lam__0(v_k_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec(v_a_34_);
lean_dec(v_k_33_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween(lean_object* v_k_38_, lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc(v_a_39_);
v___f_41_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___lam__0___boxed), 3, 2);
lean_closure_set(v___f_41_, 0, v_k_38_);
lean_closure_set(v___f_41_, 1, v_a_39_);
v___x_42_ = lp_tree_Finset_Ioo___at___00Formalism_LogVandermondeBounds_StandardLattice_nBetween_spec__0(v_a_39_, v_b_40_);
lean_dec(v_a_39_);
v___x_43_ = lp_mathlib_Multiset_filter___redArg(v___f_41_, v___x_42_);
v___x_44_ = l_List_lengthTR___redArg(v___x_43_);
lean_dec(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween___boxed(lean_object* v_k_45_, lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_nBetween(v_k_45_, v_a_46_, v_b_47_);
lean_dec(v_b_47_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogVandermondeBounds_LogRatioLowerBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LogVandermondeBounds_LogRatioUpperBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogVandermondeBounds_LogRatioLowerBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
