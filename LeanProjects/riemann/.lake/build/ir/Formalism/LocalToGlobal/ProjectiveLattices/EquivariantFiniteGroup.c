// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
// Imports: public import Init public meta import Init public import Mathlib public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity public import Formalism.LocalToGlobal.ProjectiveLattices.IsProbabilityMeasureAutQuotientNormalized
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
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_holSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_holSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_holSub(lean_object* v_E_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_r_5_, lean_object* v_Comp_6_, lean_object* v_X_7_, lean_object* v_la_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_holSub___boxed(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_r_14_, lean_object* v_Comp_15_, lean_object* v_X_16_, lean_object* v_la_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Pj_holSub(v_E_10_, v_inst_11_, v_inst_12_, v_inst_13_, v_r_14_, v_Comp_15_, v_X_16_, v_la_17_);
lean_dec_ref(v_la_17_);
lean_dec_ref(v_X_16_);
lean_dec(v_r_14_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel___redArg___lam__0(lean_object* v_mu_22_, lean_object* v_dict_23_, lean_object* v_P_24_, lean_object* v_g_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_fst_28_; lean_object* v_snd_29_; lean_object* v_re_30_; lean_object* v_im_31_; lean_object* v___x_32_; lean_object* v___f_33_; lean_object* v___x_34_; 
lean_inc_ref(v_g_25_);
v___x_26_ = lean_apply_1(v_mu_22_, v_g_25_);
v___x_27_ = lean_apply_1(v_dict_23_, v_g_25_);
v_fst_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_fst_28_);
v_snd_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_snd_29_);
lean_dec_ref(v___x_27_);
v_re_30_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_re_30_);
v_im_31_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_im_31_);
lean_dec_ref(v___x_26_);
v___x_32_ = lean_apply_2(v_P_24_, v_fst_28_, v_snd_29_);
v___f_33_ = ((lean_object*)(lp_tree_Formalism_L2_Pj_adel___redArg___lam__0___closed__1));
v___x_34_ = lp_mathlib_Complex_mulAux___redArg(v___f_33_, v_re_30_, v_im_31_, v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel___redArg(lean_object* v_dict_35_, lean_object* v_mu_36_){
_start:
{
lean_object* v___f_37_; 
v___f_37_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_adel___redArg___lam__0), 4, 2);
lean_closure_set(v___f_37_, 0, v_mu_36_);
lean_closure_set(v___f_37_, 1, v_dict_35_);
return v___f_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel(lean_object* v_D_38_, lean_object* v_E_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_r_43_, lean_object* v_Comp_44_, lean_object* v_V_45_, lean_object* v_X_46_, lean_object* v_dict_47_, lean_object* v_mu_48_){
_start:
{
lean_object* v___f_49_; 
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_adel___redArg___lam__0), 4, 2);
lean_closure_set(v___f_49_, 0, v_mu_48_);
lean_closure_set(v___f_49_, 1, v_dict_47_);
return v___f_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_adel___boxed(lean_object* v_D_50_, lean_object* v_E_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_r_55_, lean_object* v_Comp_56_, lean_object* v_V_57_, lean_object* v_X_58_, lean_object* v_dict_59_, lean_object* v_mu_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_Pj_adel(v_D_50_, v_E_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_r_55_, v_Comp_56_, v_V_57_, v_X_58_, v_dict_59_, v_mu_60_);
lean_dec_ref(v_X_58_);
lean_dec_ref(v_V_57_);
lean_dec(v_r_55_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_D_50_);
return v_res_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsProbabilityMeasureAutQuotientNormalized(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_EquivariantFiniteGroup(uint8_t builtin) {
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
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsProbabilityMeasureAutQuotientNormalized(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
