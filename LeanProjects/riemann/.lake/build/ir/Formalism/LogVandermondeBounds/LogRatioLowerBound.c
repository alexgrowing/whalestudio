// Lean compiler output
// Module: Formalism.LogVandermondeBounds.LogRatioLowerBound
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__0(lean_object* v_x_1_, lean_object* v_i_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; lean_object* v___f_7_; 
lean_inc(v_x_1_);
v___x_4_ = lean_apply_1(v_x_1_, v_i_2_);
v___x_5_ = lean_apply_1(v_x_1_, v_j_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_7_, 0, v___x_4_);
lean_closure_set(v___f_7_, 1, v___f_6_);
return v___f_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0(lean_object* v_s_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___f_10_ = ((lean_object*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0___closed__0));
v___x_11_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_12_ = l_List_foldrTR___redArg(v___f_10_, v___x_11_, v_s_9_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0___redArg(lean_object* v_s_13_, lean_object* v_f_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lp_mathlib_Multiset_map___redArg(v_f_14_, v_s_13_);
v___x_16_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0_spec__0(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__1(lean_object* v_x_17_, lean_object* v_N_18_, lean_object* v_i_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc(v_i_19_);
v___f_20_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__0), 3, 2);
lean_closure_set(v___f_20_, 0, v_x_17_);
lean_closure_set(v___f_20_, 1, v_i_19_);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_i_19_, v___x_21_);
lean_dec(v_i_19_);
v___x_23_ = lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(v___x_22_, v_N_18_);
lean_dec(v___x_22_);
v___x_24_ = lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0___redArg(v___x_23_, v___f_20_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__1___boxed(lean_object* v_x_25_, lean_object* v_N_26_, lean_object* v_i_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__1(v_x_25_, v_N_26_, v_i_27_);
lean_dec(v_N_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN(lean_object* v_x_29_, lean_object* v_N_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
lean_inc(v_N_30_);
v___f_31_ = lean_alloc_closure((void*)(lp_tree_Formalism_LogVandermondeBounds_StandardLattice_vandN___lam__1___boxed), 3, 2);
lean_closure_set(v___f_31_, 0, v_x_29_);
lean_closure_set(v___f_31_, 1, v_N_30_);
v___x_32_ = l_List_range(v_N_30_);
v___x_33_ = lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0___redArg(v___x_32_, v___f_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0(lean_object* v_00_u03b9_34_, lean_object* v_s_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_Finset_prod___at___00Formalism_LogVandermondeBounds_StandardLattice_vandN_spec__0___redArg(v_s_35_, v_f_36_);
return v___x_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LogVandermondeBounds_LogRatioLowerBound(uint8_t builtin) {
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
