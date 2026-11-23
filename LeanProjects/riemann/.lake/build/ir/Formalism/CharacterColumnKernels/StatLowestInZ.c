// Lean compiler output
// Module: Formalism.CharacterColumnKernels.StatLowestInZ
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Finsupp_toMultiset_spec__1_spec__1_spec__2___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__0;
static lean_once_cell_t lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum___redArg___lam__0(lean_object* v___x_5_, lean_object* v_tw_6_, lean_object* v_rp_7_, lean_object* v_i_8_, lean_object* v_k_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_10_ = lean_nat_to_int(v___x_5_);
v___x_11_ = lean_obj_once(&lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__0, &lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__0);
v___x_12_ = lean_int_sub(v___x_10_, v___x_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_obj_once(&lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__1, &lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__1_once, _init_lp_tree_Formalism_NG_blockSum___redArg___lam__0___closed__1);
v___x_14_ = lean_nat_to_int(v_k_9_);
v___x_15_ = lean_int_mul(v___x_13_, v___x_14_);
lean_dec(v___x_14_);
v___x_16_ = lean_int_sub(v___x_12_, v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_12_);
v___x_17_ = lean_apply_1(v_tw_6_, v___x_16_);
v___x_18_ = lean_apply_1(v_rp_7_, v_i_8_);
v___x_19_ = lp_mathlib_Multiset_map___redArg(v___x_17_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__0___redArg(lean_object* v_s_20_, lean_object* v_f_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lp_mathlib_Multiset_map___redArg(v_f_21_, v_s_20_);
v___x_23_ = lp_mathlib_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Finsupp_toMultiset_spec__1_spec__1_spec__2___redArg(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum___redArg___lam__1(lean_object* v_dd_24_, lean_object* v_tw_25_, lean_object* v_rp_26_, lean_object* v_i_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
lean_inc(v_i_27_);
v___x_28_ = lean_apply_1(v_dd_24_, v_i_27_);
lean_inc(v___x_28_);
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_blockSum___redArg___lam__0), 5, 4);
lean_closure_set(v___f_29_, 0, v___x_28_);
lean_closure_set(v___f_29_, 1, v_tw_25_);
lean_closure_set(v___f_29_, 2, v_rp_26_);
lean_closure_set(v___f_29_, 3, v_i_27_);
v___x_30_ = l_List_range(v___x_28_);
v___x_31_ = lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__0___redArg(v___x_30_, v___f_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__1___redArg(lean_object* v_s_32_, lean_object* v_f_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lp_mathlib_Multiset_map___redArg(v_f_33_, v_s_32_);
v___x_35_ = lp_mathlib_Multiset_sum___at___00Finset_sum___at___00Finsupp_sum___at___00Finsupp_toMultiset_spec__1_spec__1_spec__2___redArg(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum___redArg(lean_object* v_tw_36_, lean_object* v_I_37_, lean_object* v_rp_38_, lean_object* v_dd_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; 
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_blockSum___redArg___lam__1), 4, 3);
lean_closure_set(v___f_40_, 0, v_dd_39_);
lean_closure_set(v___f_40_, 1, v_tw_36_);
lean_closure_set(v___f_40_, 2, v_rp_38_);
v___x_41_ = lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__1___redArg(v_I_37_, v___f_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_blockSum(lean_object* v_Ir_42_, lean_object* v_00_u03b9_43_, lean_object* v_tw_44_, lean_object* v_I_45_, lean_object* v_rp_46_, lean_object* v_dd_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_NG_blockSum___redArg(v_tw_44_, v_I_45_, v_rp_46_, v_dd_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__0(lean_object* v_Ir_49_, lean_object* v_00_u03b9_50_, lean_object* v_s_51_, lean_object* v_f_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__0___redArg(v_s_51_, v_f_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__1(lean_object* v_Ir_54_, lean_object* v_00_u03b9_55_, lean_object* v_s_56_, lean_object* v_f_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_tree_Finset_sum___at___00Formalism_NG_blockSum_spec__1___redArg(v_s_56_, v_f_57_);
return v___x_58_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CharacterColumnKernels_StatLowestInZ(uint8_t builtin) {
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
