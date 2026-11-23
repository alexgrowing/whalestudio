// Lean compiler output
// Module: Formalism.MoebiusJetDuality.Statement
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.RealPlaceAnalysis.FockPairGl
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
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_Finsupp_prod___at___00Finsupp_multinomial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_kroneckerMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MJ_mfac___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MJ_mfac___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MJ_mfac___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MJ_mfac___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_evOp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_evOp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_evOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac___redArg___lam__0(lean_object* v_x_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lp_mathlib_Nat_factorialBinarySplitting(v_k_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac___redArg___lam__0___boxed(lean_object* v_x_4_, lean_object* v_k_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_MJ_mfac___redArg___lam__0(v_x_4_, v_k_5_);
lean_dec(v_k_5_);
lean_dec(v_x_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac___redArg(lean_object* v_00_u03b1_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; 
v___f_9_ = ((lean_object*)(lp_tree_Formalism_MJ_mfac___redArg___closed__0));
v___x_10_ = lp_mathlib_Finsupp_prod___at___00Finsupp_multinomial_spec__1___redArg(v_00_u03b1_8_, v___f_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_mfac(lean_object* v_00_u03c3_11_, lean_object* v_00_u03b1_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_tree_Formalism_MJ_mfac___redArg(v_00_u03b1_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_evOp___redArg___lam__0(lean_object* v_toNatCast_14_, lean_object* v_P_15_, lean_object* v_toMul_16_, lean_object* v_F_17_, lean_object* v_00_u03b1_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc_ref_n(v_00_u03b1_18_, 2);
v___x_19_ = lp_tree_Formalism_MJ_mfac___redArg(v_00_u03b1_18_);
v___x_20_ = lean_apply_1(v_toNatCast_14_, v___x_19_);
v___x_21_ = lp_mathlib_MvPolynomial_coeff___redArg(v_00_u03b1_18_, v_P_15_);
lean_inc(v_toMul_16_);
v___x_22_ = lean_apply_2(v_toMul_16_, v___x_20_, v___x_21_);
v___x_23_ = lp_mathlib_MvPolynomial_coeff___redArg(v_00_u03b1_18_, v_F_17_);
v___x_24_ = lean_apply_2(v_toMul_16_, v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_evOp___redArg(lean_object* v_inst_25_, lean_object* v_P_26_, lean_object* v_F_27_){
_start:
{
lean_object* v_toSemiring_28_; lean_object* v_toAddCommMonoid_29_; lean_object* v_support_30_; lean_object* v___x_31_; lean_object* v_toMul_32_; lean_object* v___x_33_; lean_object* v_toAddMonoidWithOne_34_; lean_object* v_toNatCast_35_; lean_object* v___f_36_; lean_object* v___x_37_; 
v_toSemiring_28_ = lean_ctor_get(v_inst_25_, 0);
v_toAddCommMonoid_29_ = lean_ctor_get(v_toSemiring_28_, 0);
lean_inc_ref(v_toAddCommMonoid_29_);
v_support_30_ = lean_ctor_get(v_P_26_, 0);
lean_inc(v_support_30_);
lean_inc_ref(v_toSemiring_28_);
v___x_31_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_28_);
v_toMul_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_toMul_32_);
lean_dec_ref(v___x_31_);
v___x_33_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_25_);
v_toAddMonoidWithOne_34_ = lean_ctor_get(v___x_33_, 1);
lean_inc_ref(v_toAddMonoidWithOne_34_);
lean_dec_ref(v___x_33_);
v_toNatCast_35_ = lean_ctor_get(v_toAddMonoidWithOne_34_, 0);
lean_inc(v_toNatCast_35_);
lean_dec_ref(v_toAddMonoidWithOne_34_);
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_MJ_evOp___redArg___lam__0), 5, 4);
lean_closure_set(v___f_36_, 0, v_toNatCast_35_);
lean_closure_set(v___f_36_, 1, v_P_26_);
lean_closure_set(v___f_36_, 2, v_toMul_32_);
lean_closure_set(v___f_36_, 3, v_F_27_);
v___x_37_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_29_, v_support_30_, v___f_36_);
lean_dec_ref(v_toAddCommMonoid_29_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_evOp(lean_object* v_00_u03c3_38_, lean_object* v_R_39_, lean_object* v_inst_40_, lean_object* v_P_41_, lean_object* v_F_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_tree_Formalism_MJ_evOp___redArg(v_inst_40_, v_P_41_, v_F_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat___redArg___lam__0(lean_object* v_toMul_44_, lean_object* v_x1_45_, lean_object* v_x2_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_2(v_toMul_44_, v_x1_45_, v_x2_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat___redArg(lean_object* v_inst_48_, lean_object* v_A_49_, lean_object* v_D_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_toSemiring_53_; lean_object* v___x_54_; lean_object* v_toMul_55_; lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_toSemiring_53_ = lean_ctor_get(v_inst_48_, 0);
lean_inc_ref(v_toSemiring_53_);
lean_dec_ref(v_inst_48_);
v___x_54_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_53_);
v_toMul_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_toMul_55_);
lean_dec_ref(v___x_54_);
v___f_56_ = lean_alloc_closure((void*)(lp_tree_Formalism_MJ_hcMat___redArg___lam__0), 3, 1);
lean_closure_set(v___f_56_, 0, v_toMul_55_);
v___x_57_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_57_, 0, lean_box(0));
lean_closure_set(v___x_57_, 1, lean_box(0));
lean_closure_set(v___x_57_, 2, lean_box(0));
lean_closure_set(v___x_57_, 3, v_D_50_);
v___x_58_ = lp_mathlib_Matrix_kroneckerMap___redArg(v___f_56_, v_A_49_, v___x_57_, v_a_51_, v_a_52_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat(lean_object* v_R_59_, lean_object* v_inst_60_, lean_object* v_p_61_, lean_object* v_q_62_, lean_object* v_A_63_, lean_object* v_D_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_tree_Formalism_MJ_hcMat___redArg(v_inst_60_, v_A_63_, v_D_64_, v_a_65_, v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MJ_hcMat___boxed(lean_object* v_R_68_, lean_object* v_inst_69_, lean_object* v_p_70_, lean_object* v_q_71_, lean_object* v_A_72_, lean_object* v_D_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_MJ_hcMat(v_R_68_, v_inst_69_, v_p_70_, v_q_71_, v_A_72_, v_D_73_, v_a_74_, v_a_75_);
lean_dec(v_q_71_);
lean_dec(v_p_70_);
return v_res_76_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_FockPairGl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_MoebiusJetDuality_Statement(uint8_t builtin) {
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
res = initialize_tree_Formalism_RealPlaceAnalysis_FockPairGl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
