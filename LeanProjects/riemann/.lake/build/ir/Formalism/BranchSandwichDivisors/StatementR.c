// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.StatementR
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* l_Fin_succ___redArg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d0___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d0___lam__0(lean_object* v_sg_1_, lean_object* v_lam_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_i_3_);
v___x_4_ = lean_apply_1(v_sg_1_, v_i_3_);
v___x_5_ = l_Fin_succ___redArg(v_i_3_);
lean_dec(v_i_3_);
v___x_6_ = lean_apply_1(v_lam_2_, v___x_5_);
v___x_7_ = lean_int_sub(v___x_4_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_nat_to_int(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0(lean_object* v_s_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_12_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__0));
v___x_13_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0___closed__1);
v___x_14_ = l_List_foldrTR___redArg(v___f_12_, v___x_13_, v_s_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(lean_object* v_s_15_, lean_object* v_f_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lp_mathlib_Multiset_map___redArg(v_f_16_, v_s_15_);
v___x_18_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0_spec__0(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d0(lean_object* v_n_19_, lean_object* v_lam_20_, lean_object* v_sg_21_){
_start:
{
lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_d0___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_sg_21_);
lean_closure_set(v___f_22_, 1, v_lam_20_);
v___x_23_ = l_List_finRange(v_n_19_);
v___x_24_ = lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(v___x_23_, v___f_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0(lean_object* v_00_u03b9_25_, lean_object* v_s_26_, lean_object* v_f_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(v_s_26_, v_f_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d1___lam__0(lean_object* v_lam_29_, lean_object* v_n_30_, lean_object* v_sg_31_, lean_object* v_i_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
lean_inc_ref_n(v_lam_29_, 2);
lean_inc(v_i_32_);
v___x_33_ = lean_apply_1(v_lam_29_, v_i_32_);
v___x_34_ = l_Fin_succ___redArg(v_i_32_);
lean_dec(v_i_32_);
v___x_35_ = lean_apply_1(v_lam_29_, v___x_34_);
v___x_36_ = lean_int_sub(v___x_33_, v___x_35_);
lean_dec(v___x_35_);
lean_dec(v___x_33_);
v___x_37_ = lp_tree_Formalism_BranchingDeterminantCap_d0(v_n_30_, v_lam_29_, v_sg_31_);
v___x_38_ = lean_int_dec_le(v___x_36_, v___x_37_);
if (v___x_38_ == 0)
{
lean_dec(v___x_36_);
return v___x_37_;
}
else
{
lean_dec(v___x_37_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_d1(lean_object* v_n_39_, lean_object* v_lam_40_, lean_object* v_sg_41_){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc(v_n_39_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_d1___lam__0), 4, 3);
lean_closure_set(v___f_42_, 0, v_lam_40_);
lean_closure_set(v___f_42_, 1, v_n_39_);
lean_closure_set(v___f_42_, 2, v_sg_41_);
v___x_43_ = l_List_finRange(v_n_39_);
v___x_44_ = lp_tree_Finset_sum___at___00Formalism_BranchingDeterminantCap_d0_spec__0___redArg(v___x_43_, v___f_42_);
return v___x_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
