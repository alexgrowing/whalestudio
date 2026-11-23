// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil public import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
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
static const lean_closure_object lp_tree_Formalism_L2_Pj_muPin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Pj_muPin___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Pj_muPin___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Pj_muPin___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Pj_muPin___redArg___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_Pj_muPin___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Pj_muPin___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_muPin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_muPin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_muPin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latG_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latG_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_muPin___redArg(lean_object* v_dict_4_, lean_object* v_mu_5_, lean_object* v_c_6_, lean_object* v_g_7_){
_start:
{
lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v___x_10_; lean_object* v_re_11_; lean_object* v_im_12_; lean_object* v___x_13_; lean_object* v___f_14_; lean_object* v___x_15_; 
lean_inc_ref(v_g_7_);
v___x_8_ = lean_apply_1(v_dict_4_, v_g_7_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lean_apply_1(v_c_6_, v_fst_9_);
v_re_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_re_11_);
v_im_12_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_im_12_);
lean_dec_ref(v___x_10_);
v___x_13_ = lean_apply_1(v_mu_5_, v_g_7_);
v___f_14_ = ((lean_object*)(lp_tree_Formalism_L2_Pj_muPin___redArg___closed__1));
v___x_15_ = lp_mathlib_Complex_mulAux___redArg(v___f_14_, v_re_11_, v_im_12_, v___x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_muPin(lean_object* v_D_16_, lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_r_21_, lean_object* v_Comp_22_, lean_object* v_V_23_, lean_object* v_X_24_, lean_object* v_dict_25_, lean_object* v_mu_26_, lean_object* v_c_27_, lean_object* v_g_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Formalism_L2_Pj_muPin___redArg(v_dict_25_, v_mu_26_, v_c_27_, v_g_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_muPin___boxed(lean_object* v_D_30_, lean_object* v_E_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_r_35_, lean_object* v_Comp_36_, lean_object* v_V_37_, lean_object* v_X_38_, lean_object* v_dict_39_, lean_object* v_mu_40_, lean_object* v_c_41_, lean_object* v_g_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_L2_Pj_muPin(v_D_30_, v_E_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_r_35_, v_Comp_36_, v_V_37_, v_X_38_, v_dict_39_, v_mu_40_, v_c_41_, v_g_42_);
lean_dec_ref(v_X_38_);
lean_dec_ref(v_V_37_);
lean_dec(v_r_35_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_D_30_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latG_spec__0(lean_object* v___x_44_, lean_object* v_s_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latG_spec__0___boxed(lean_object* v___x_47_, lean_object* v_s_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Submodule_span___at___00Formalism_L2_Pj_latG_spec__0(v___x_47_, v_s_48_);
lean_dec_ref(v___x_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG___redArg(lean_object* v_D_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG___redArg___boxed(lean_object* v_D_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_L2_Pj_latG___redArg(v_D_52_);
lean_dec_ref(v_D_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG(lean_object* v_D_54_, lean_object* v_V_55_, lean_object* v_g_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latG___boxed(lean_object* v_D_58_, lean_object* v_V_59_, lean_object* v_g_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_Pj_latG(v_D_58_, v_V_59_, v_g_60_);
lean_dec_ref(v_g_60_);
lean_dec_ref(v_V_59_);
lean_dec_ref(v_D_58_);
return v_res_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CuspidalL2Subspace(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_TiedWeil(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntAll(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CuspidalL2Subspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_TiedWeil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
