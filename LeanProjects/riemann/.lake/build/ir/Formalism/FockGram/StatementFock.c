// Lean compiler output
// Module: Formalism.FockGram.StatementFock
// Imports: public import Init public meta import Init public import Formalism.SmithDeterminants.StatementGram
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_A_mfact___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fockGram___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_E_fockGram___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_E_fockGram___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fockGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fockGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fock___redArg___lam__0(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_inst_3_, lean_object* v_toMul_4_, lean_object* v_toNatCast_5_, lean_object* v_m_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc_ref_n(v_m_6_, 2);
v___x_7_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_6_, v_f_1_);
v___x_8_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_6_, v_g_2_);
v___x_9_ = lean_apply_1(v_inst_3_, v___x_8_);
lean_inc(v_toMul_4_);
v___x_10_ = lean_apply_2(v_toMul_4_, v___x_7_, v___x_9_);
v___x_11_ = lp_tree_Formalism_A_mfact___redArg(v_m_6_);
v___x_12_ = lean_apply_1(v_toNatCast_5_, v___x_11_);
v___x_13_ = lean_apply_2(v_toMul_4_, v___x_10_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fock___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_f_16_, lean_object* v_g_17_){
_start:
{
lean_object* v_toSemiring_18_; lean_object* v_toAddCommMonoid_19_; lean_object* v_support_20_; lean_object* v___x_21_; lean_object* v_toMul_22_; lean_object* v___x_23_; lean_object* v_toAddMonoidWithOne_24_; lean_object* v_toNatCast_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v_toSemiring_18_ = lean_ctor_get(v_inst_14_, 0);
v_toAddCommMonoid_19_ = lean_ctor_get(v_toSemiring_18_, 0);
lean_inc_ref(v_toAddCommMonoid_19_);
v_support_20_ = lean_ctor_get(v_f_16_, 0);
lean_inc(v_support_20_);
lean_inc_ref(v_toSemiring_18_);
v___x_21_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_18_);
v_toMul_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_toMul_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_14_);
v_toAddMonoidWithOne_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_toAddMonoidWithOne_24_);
lean_dec_ref(v___x_23_);
v_toNatCast_25_ = lean_ctor_get(v_toAddMonoidWithOne_24_, 0);
lean_inc(v_toNatCast_25_);
lean_dec_ref(v_toAddMonoidWithOne_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_E_fock___redArg___lam__0), 6, 5);
lean_closure_set(v___f_26_, 0, v_f_16_);
lean_closure_set(v___f_26_, 1, v_g_17_);
lean_closure_set(v___f_26_, 2, v_inst_15_);
lean_closure_set(v___f_26_, 3, v_toMul_22_);
lean_closure_set(v___f_26_, 4, v_toNatCast_25_);
v___x_27_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_19_, v_support_20_, v___f_26_);
lean_dec_ref(v_toAddCommMonoid_19_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fock(lean_object* v_R_28_, lean_object* v_00_u03c4_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_f_32_, lean_object* v_g_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_E_fock___redArg(v_inst_30_, v_inst_31_, v_f_32_, v_g_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fockGram___redArg___lam__0(lean_object* v_v_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_i_38_, lean_object* v_j_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc_ref(v_v_35_);
v___x_40_ = lean_apply_1(v_v_35_, v_i_38_);
v___x_41_ = lean_apply_1(v_v_35_, v_j_39_);
v___x_42_ = lp_tree_Formalism_E_fock___redArg(v_inst_36_, v_inst_37_, v___x_40_, v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_tree_Formalism_E_fockGram___redArg___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fockGram___redArg(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_v_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_49_; lean_object* v_toFun_50_; lean_object* v___f_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&lp_tree_Formalism_E_fockGram___redArg___closed__0, &lp_tree_Formalism_E_fockGram___redArg___closed__0_once, _init_lp_tree_Formalism_E_fockGram___redArg___closed__0);
v_toFun_50_ = lean_ctor_get(v___x_49_, 0);
v___f_51_ = lean_alloc_closure((void*)(lp_tree_Formalism_E_fockGram___redArg___lam__0), 5, 3);
lean_closure_set(v___f_51_, 0, v_v_46_);
lean_closure_set(v___f_51_, 1, v_inst_44_);
lean_closure_set(v___f_51_, 2, v_inst_45_);
lean_inc(v_toFun_50_);
v___x_52_ = lean_apply_3(v_toFun_50_, v___f_51_, v_a_47_, v_a_48_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_fockGram(lean_object* v_R_53_, lean_object* v_00_u03c4_54_, lean_object* v_00_u03b9_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_v_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_tree_Formalism_E_fockGram___redArg(v_inst_56_, v_inst_57_, v_v_58_, v_a_59_, v_a_60_);
return v___x_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SmithDeterminants_StatementGram(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FockGram_StatementFock(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SmithDeterminants_StatementGram(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
