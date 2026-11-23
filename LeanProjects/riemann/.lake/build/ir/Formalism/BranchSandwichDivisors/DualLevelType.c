// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.DualLevelType
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.StatementK public import Formalism.BranchSandwichDivisors.StatementR public import Formalism.BranchSandwichDivisors.StatementL
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
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_typeSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_typeSpace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg(lean_object* v_K_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___f_6_; 
lean_dec(v_K_2_);
v___f_6_ = ((lean_object*)(lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg___closed__0));
return v___f_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; 
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_x_3_, v_one_7_);
lean_inc(v_K_2_);
lean_inc(v_n_8_);
v___x_9_ = lean_apply_1(v_K_2_, v_n_8_);
v___x_10_ = lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg(v_K_2_, v_n_8_);
lean_dec(v_n_8_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v___x_10_);
lean_closure_set(v___f_11_, 1, v___x_9_);
return v___f_11_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg___boxed(lean_object* v_K_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg(v_K_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd(lean_object* v_F_15_, lean_object* v_inst_16_, lean_object* v_V_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_K_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_tree_Formalism_BranchingDeterminantCap_chainProd___redArg(v_K_20_, v_x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_chainProd___boxed(lean_object* v_F_23_, lean_object* v_inst_24_, lean_object* v_V_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_K_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_BranchingDeterminantCap_chainProd(v_F_23_, v_inst_24_, v_V_25_, v_inst_26_, v_inst_27_, v_K_28_, v_x_29_);
lean_dec(v_x_29_);
lean_dec(v_inst_27_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg___lam__0(lean_object* v_E_31_, lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_inc(v_00_u03b2_33_);
v___x_35_ = lean_apply_2(v_E_31_, v_00_u03b1_32_, v_00_u03b2_33_);
v___x_36_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, v_00_u03b2_33_);
v___x_37_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___x_36_, v___x_35_, v___y_34_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg___lam__1(lean_object* v_E_38_, lean_object* v_toAddMonoid_39_, lean_object* v_inst_40_, lean_object* v_00_u03b1_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_63__overap_45_; lean_object* v___x_46_; 
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg___lam__0), 4, 2);
lean_closure_set(v___f_43_, 0, v_E_38_);
lean_closure_set(v___f_43_, 1, v_00_u03b1_41_);
v___x_44_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_39_);
v___x_63__overap_45_ = lp_mathlib_Finset_sum___redArg(v___x_44_, v_inst_40_, v___f_43_);
lean_dec_ref(v___x_44_);
v___x_46_ = lean_apply_1(v___x_63__overap_45_, v___y_42_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg(lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_E_49_){
_start:
{
lean_object* v_toAddMonoid_50_; lean_object* v___f_51_; lean_object* v___f_52_; 
v_toAddMonoid_50_ = lean_ctor_get(v_inst_48_, 0);
lean_inc_ref(v_toAddMonoid_50_);
lean_dec_ref(v_inst_48_);
v___f_51_ = lean_alloc_closure((void*)(lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg___lam__1), 5, 3);
lean_closure_set(v___f_51_, 0, v_E_49_);
lean_closure_set(v___f_51_, 1, v_toAddMonoid_50_);
lean_closure_set(v___f_51_, 2, v_inst_47_);
v___f_52_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_52_, 0, v___f_51_);
return v___f_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp(lean_object* v_F_53_, lean_object* v_inst_54_, lean_object* v_A_55_, lean_object* v_A_x27_56_, lean_object* v_W_57_, lean_object* v_W_x27_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_E_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_tree_Formalism_BranchingDeterminantCap_matOp___redArg(v_inst_59_, v_inst_62_, v_E_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_matOp___boxed(lean_object* v_F_66_, lean_object* v_inst_67_, lean_object* v_A_68_, lean_object* v_A_x27_69_, lean_object* v_W_70_, lean_object* v_W_x27_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_E_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_tree_Formalism_BranchingDeterminantCap_matOp(v_F_66_, v_inst_67_, v_A_68_, v_A_x27_69_, v_W_70_, v_W_x27_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_E_77_);
lean_dec(v_inst_76_);
lean_dec(v_inst_74_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_inst_67_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_typeSpace(lean_object* v_K_79_, lean_object* v_V_80_, lean_object* v_00_u0393_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_00_u03c1_86_, lean_object* v_chi_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_typeSpace___boxed(lean_object* v_K_89_, lean_object* v_V_90_, lean_object* v_00_u0393_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_00_u03c1_96_, lean_object* v_chi_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_BranchingDeterminantCap_typeSpace(v_K_89_, v_V_90_, v_00_u0393_91_, v_inst_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_00_u03c1_96_, v_chi_97_);
lean_dec(v_chi_97_);
lean_dec(v_00_u03c1_96_);
lean_dec_ref(v_inst_95_);
lean_dec(v_inst_94_);
lean_dec_ref(v_inst_93_);
lean_dec_ref(v_inst_92_);
return v_res_98_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_StatementK(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementR(uint8_t builtin);
lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementL(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_DualLevelType(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_StatementK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_BranchSandwichDivisors_StatementL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
