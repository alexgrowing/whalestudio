// Lean compiler output
// Module: Formalism.BranchSandwichDivisors.StatementL
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HarderNarasimhan.QuotRealize public import Formalism.HarderNarasimhan.StatementMod public import Formalism.QuotientMetricDivisors.Statement
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
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__0_value)} };
static const lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg(lean_object* v_c_4_, lean_object* v_X_5_, lean_object* v_v_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; lean_object* v_re_10_; lean_object* v_im_11_; lean_object* v___x_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
v___x_9_ = lp_mathlib_Complex_ofReal(v_c_4_);
v_re_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_re_10_);
v_im_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_im_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_apply_3(v_X_5_, v_v_6_, v_a_7_, v_a_8_);
v___f_13_ = ((lean_object*)(lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg___closed__1));
v___x_14_ = lp_mathlib_Complex_mulAux___redArg(v___f_13_, v_re_10_, v_im_11_, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame(lean_object* v_K_15_, lean_object* v_inst_16_, lean_object* v_00_u03b9_17_, lean_object* v_c_18_, lean_object* v_X_19_, lean_object* v_v_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___redArg(v_c_18_, v_X_19_, v_v_20_, v_a_21_, v_a_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BranchingDeterminantCap_scaleFrame___boxed(lean_object* v_K_24_, lean_object* v_inst_25_, lean_object* v_00_u03b9_26_, lean_object* v_c_27_, lean_object* v_X_28_, lean_object* v_v_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_BranchingDeterminantCap_scaleFrame(v_K_24_, v_inst_25_, v_00_u03b9_26_, v_c_27_, v_X_28_, v_v_29_, v_a_30_, v_a_31_);
lean_dec_ref(v_inst_25_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_QuotRealize(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_StatementMod(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_BranchSandwichDivisors_StatementL(uint8_t builtin) {
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
res = initialize_tree_Formalism_HarderNarasimhan_QuotRealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_StatementMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
