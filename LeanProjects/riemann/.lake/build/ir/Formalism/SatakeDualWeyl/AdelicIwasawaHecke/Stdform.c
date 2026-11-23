// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementC public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
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
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
static const lean_closure_object lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__0_value)} };
static const lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__1 = (const lean_object*)&lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0(lean_object* v_y_4_, lean_object* v_i_5_, lean_object* v_M_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_re_10_; lean_object* v_im_11_; lean_object* v___x_12_; lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v_re_15_; lean_object* v_im_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc_ref(v_y_4_);
lean_inc(v_i_5_);
v___x_8_ = lean_apply_1(v_y_4_, v_i_5_);
v___x_9_ = lp_mathlib_Complex_instStarRing___lam__0(v___x_8_);
v_re_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_re_10_);
v_im_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_im_11_);
lean_dec_ref(v___x_9_);
lean_inc(v_j_7_);
v___x_12_ = lean_apply_2(v_M_6_, v_i_5_, v_j_7_);
v___f_13_ = ((lean_object*)(lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0___closed__1));
v___x_14_ = lp_mathlib_Complex_mulAux___redArg(v___f_13_, v_re_10_, v_im_11_, v___x_12_);
v_re_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_re_15_);
v_im_16_ = lean_ctor_get(v___x_14_, 1);
lean_inc(v_im_16_);
lean_dec_ref(v___x_14_);
v___x_17_ = lean_apply_1(v_y_4_, v_j_7_);
v___x_18_ = lp_mathlib_Complex_mulAux___redArg(v___f_13_, v_re_15_, v_im_16_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__1(lean_object* v_y_19_, lean_object* v_M_20_, lean_object* v___x_21_, lean_object* v_inst_22_, lean_object* v_i_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___x_25_; 
v___f_24_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_stdformQ___redArg___lam__0), 4, 3);
lean_closure_set(v___f_24_, 0, v_y_19_);
lean_closure_set(v___f_24_, 1, v_i_23_);
lean_closure_set(v___f_24_, 2, v_M_20_);
v___x_25_ = lp_mathlib_Finset_sum___redArg(v___x_21_, v_inst_22_, v___f_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg___lam__1___boxed(lean_object* v_y_26_, lean_object* v_M_27_, lean_object* v___x_28_, lean_object* v_inst_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_UG_P_stdformQ___redArg___lam__1(v_y_26_, v_M_27_, v___x_28_, v_inst_29_, v_i_30_);
lean_dec_ref(v___x_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ___redArg(lean_object* v_inst_32_, lean_object* v_M_33_, lean_object* v_y_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v_re_38_; 
v___x_35_ = lp_mathlib_Complex_instAddCommMonoid;
lean_inc(v_inst_32_);
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_stdformQ___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_36_, 0, v_y_34_);
lean_closure_set(v___f_36_, 1, v_M_33_);
lean_closure_set(v___f_36_, 2, v___x_35_);
lean_closure_set(v___f_36_, 3, v_inst_32_);
v___x_37_ = lp_mathlib_Finset_sum___redArg(v___x_35_, v_inst_32_, v___f_36_);
v_re_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_re_38_);
lean_dec(v___x_37_);
return v_re_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_stdformQ(lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_M_41_, lean_object* v_y_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_tree_Formalism_UG_P_stdformQ___redArg(v_inst_40_, v_M_41_, v_y_42_);
return v___x_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementC(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
