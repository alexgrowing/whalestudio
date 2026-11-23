// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.KernelArgumentHypothesisScalar
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.AtTLemmas public import Formalism.LocalRingCardinality.DataArith public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sumShiftW___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sumShiftW___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sumShiftW(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piO(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_V_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_00_u03b9_6_, lean_object* v_w_7_, lean_object* v_A_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piO___boxed(lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_V_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03b9_15_, lean_object* v_w_16_, lean_object* v_A_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Col_piO(v_K_10_, v_inst_11_, v_V_12_, v_inst_13_, v_inst_14_, v_00_u03b9_15_, v_w_16_, v_A_17_);
lean_dec_ref(v_A_17_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sumShiftW___lam__0(lean_object* v_lam_19_, lean_object* v_b_20_, lean_object* v_i_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_apply_1(v_lam_19_, v_i_21_);
v___x_23_ = lean_int_add(v___x_22_, v_b_20_);
lean_dec(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sumShiftW___lam__0___boxed(lean_object* v_lam_24_, lean_object* v_b_25_, lean_object* v_i_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_L2_Col_sumShiftW___lam__0(v_lam_24_, v_b_25_, v_i_26_);
lean_dec(v_b_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sumShiftW(lean_object* v_n_28_, lean_object* v_lam_29_, lean_object* v_b_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___f_31_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_sumShiftW___lam__0___boxed), 3, 2);
lean_closure_set(v___f_31_, 0, v_lam_29_);
lean_closure_set(v___f_31_, 1, v_b_30_);
v___x_32_ = l_List_finRange(v_n_28_);
v___x_33_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_32_, v___f_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC___lam__0(lean_object* v_m_34_, lean_object* v_ga_35_, lean_object* v_j_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_nat_sub(v_m_34_, v_j_36_);
v___x_38_ = lean_apply_1(v_ga_35_, v_j_36_);
v___x_39_ = lean_nat_mul(v___x_37_, v___x_38_);
lean_dec(v___x_38_);
lean_dec(v___x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC___lam__0___boxed(lean_object* v_m_40_, lean_object* v_ga_41_, lean_object* v_j_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_L2_Col_eColC___lam__0(v_m_40_, v_ga_41_, v_j_42_);
lean_dec(v_m_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC(lean_object* v_R_44_, lean_object* v_e1_45_, lean_object* v_ga_46_){
_start:
{
lean_object* v_m_47_; lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_m_47_ = lean_ctor_get(v_R_44_, 2);
lean_inc_n(v_m_47_, 2);
lean_dec_ref(v_R_44_);
v___f_48_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_eColC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_48_, 0, v_m_47_);
lean_closure_set(v___f_48_, 1, v_ga_46_);
v___x_49_ = lean_nat_mul(v_m_47_, v_e1_45_);
v___x_50_ = l_List_range(v_m_47_);
v___x_51_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_50_, v___f_48_);
v___x_52_ = lean_nat_add(v___x_49_, v___x_51_);
lean_dec(v___x_51_);
lean_dec(v___x_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eColC___boxed(lean_object* v_R_53_, lean_object* v_e1_54_, lean_object* v_ga_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_Formalism_L2_Col_eColC(v_R_53_, v_e1_54_, v_ga_55_);
lean_dec(v_e1_54_);
return v_res_56_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AtTLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_KernelArgumentHypothesisScalar(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_AtTLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
