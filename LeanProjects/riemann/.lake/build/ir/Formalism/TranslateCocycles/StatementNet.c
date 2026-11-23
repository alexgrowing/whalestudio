// Lean compiler output
// Module: Formalism.TranslateCocycles.StatementNet
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CG_netFull___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netFull___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_CG_netFull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_CG_netFull___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_CG_netFull___closed__0 = (const lean_object*)&lp_tree_Formalism_CG_netFull___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netFull(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CG_netPattern___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netPattern___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CG_netX___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netX___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netX(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netX___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CG_netFull___lam__0(lean_object* v_a_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; uint8_t v___x_4_; 
v_fst_2_ = lean_ctor_get(v_a_1_, 0);
v_snd_3_ = lean_ctor_get(v_a_1_, 1);
v___x_4_ = lean_nat_dec_lt(v_fst_2_, v_snd_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netFull___lam__0___boxed(lean_object* v_a_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = lp_tree_Formalism_CG_netFull___lam__0(v_a_5_);
lean_dec_ref(v_a_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netFull(lean_object* v_n_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_10_ = ((lean_object*)(lp_tree_Formalism_CG_netFull___closed__0));
v___x_11_ = l_List_finRange(v_n_9_);
lean_inc(v___x_11_);
v___x_12_ = lp_mathlib_Multiset_product___redArg(v___x_11_, v___x_11_);
v___x_13_ = lp_mathlib_Multiset_filter___redArg(v___f_10_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_CG_netPattern___lam__0(lean_object* v_p0_14_, lean_object* v_k_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_fst_17_; lean_object* v_snd_18_; uint8_t v___x_19_; uint8_t v___y_21_; 
v_fst_17_ = lean_ctor_get(v_a_16_, 0);
v_snd_18_ = lean_ctor_get(v_a_16_, 1);
v___x_19_ = lean_nat_dec_lt(v_fst_17_, v_snd_18_);
if (v___x_19_ == 0)
{
return v___x_19_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_le(v_p0_14_, v_fst_17_);
if (v___x_23_ == 0)
{
v___y_21_ = v___x_23_;
goto v___jp_20_;
}
else
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_nat_add(v_p0_14_, v_k_15_);
v___x_25_ = lean_nat_dec_eq(v_snd_18_, v___x_24_);
lean_dec(v___x_24_);
v___y_21_ = v___x_25_;
goto v___jp_20_;
}
}
v___jp_20_:
{
if (v___y_21_ == 0)
{
return v___x_19_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netPattern___lam__0___boxed(lean_object* v_p0_26_, lean_object* v_k_27_, lean_object* v_a_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lp_tree_Formalism_CG_netPattern___lam__0(v_p0_26_, v_k_27_, v_a_28_);
lean_dec_ref(v_a_28_);
lean_dec(v_k_27_);
lean_dec(v_p0_26_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netPattern(lean_object* v_k_31_, lean_object* v_c_32_, lean_object* v_p0_33_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc(v_k_31_);
v___f_34_ = lean_alloc_closure((void*)(lp_tree_Formalism_CG_netPattern___lam__0___boxed), 3, 2);
lean_closure_set(v___f_34_, 0, v_p0_33_);
lean_closure_set(v___f_34_, 1, v_k_31_);
v___x_35_ = lean_nat_add(v_k_31_, v_c_32_);
lean_dec(v_k_31_);
v___x_36_ = l_List_finRange(v___x_35_);
lean_inc(v___x_36_);
v___x_37_ = lp_mathlib_Multiset_product___redArg(v___x_36_, v___x_36_);
v___x_38_ = lp_mathlib_Multiset_filter___redArg(v___f_34_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netPattern___boxed(lean_object* v_k_39_, lean_object* v_c_40_, lean_object* v_p0_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_CG_netPattern(v_k_39_, v_c_40_, v_p0_41_);
lean_dec(v_c_40_);
return v_res_42_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_CG_netX___lam__0(lean_object* v_p0_43_, lean_object* v_k_44_, lean_object* v_a_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_le(v_p0_43_, v_a_45_);
if (v___x_46_ == 0)
{
return v___x_46_;
}
else
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_nat_add(v_p0_43_, v_k_44_);
v___x_48_ = lean_nat_dec_lt(v_a_45_, v___x_47_);
lean_dec(v___x_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netX___lam__0___boxed(lean_object* v_p0_49_, lean_object* v_k_50_, lean_object* v_a_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = lp_tree_Formalism_CG_netX___lam__0(v_p0_49_, v_k_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec(v_k_50_);
lean_dec(v_p0_49_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netX(lean_object* v_k_54_, lean_object* v_c_55_, lean_object* v_p0_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_inc(v_k_54_);
v___f_57_ = lean_alloc_closure((void*)(lp_tree_Formalism_CG_netX___lam__0___boxed), 3, 2);
lean_closure_set(v___f_57_, 0, v_p0_56_);
lean_closure_set(v___f_57_, 1, v_k_54_);
v___x_58_ = lean_nat_add(v_k_54_, v_c_55_);
lean_dec(v_k_54_);
v___x_59_ = l_List_finRange(v___x_58_);
v___x_60_ = lp_mathlib_Multiset_filter___redArg(v___f_57_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_netX___boxed(lean_object* v_k_61_, lean_object* v_c_62_, lean_object* v_p0_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_Formalism_CG_netX(v_k_61_, v_c_62_, v_p0_63_);
lean_dec(v_c_62_);
return v_res_64_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_TranslateCocycles_StatementNet(uint8_t builtin) {
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
