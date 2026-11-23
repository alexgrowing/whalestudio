// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace public import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest public import Formalism.LocalToGlobal.ProjectiveLattices.DatIndep public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
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
lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_g0(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_badN___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_badN___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Pj_badN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Pj_badN___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Pj_badN___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Pj_badN___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_badN(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_badN___lam__0(lean_object* v_p_1_){
_start:
{
lean_inc(v_p_1_);
return v_p_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_badN___lam__0___boxed(lean_object* v_p_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_L2_Pj_badN___lam__0(v_p_2_);
lean_dec(v_p_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_badN(lean_object* v_D_5_){
_start:
{
lean_object* v_host_6_; lean_object* v_toHostAx_7_; lean_object* v_levelPrimes_8_; lean_object* v_q_9_; lean_object* v_d_10_; lean_object* v_QS_11_; lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_host_6_ = lean_ctor_get(v_D_5_, 1);
lean_inc_ref(v_host_6_);
lean_dec_ref(v_D_5_);
v_toHostAx_7_ = lean_ctor_get(v_host_6_, 0);
lean_inc_ref(v_toHostAx_7_);
v_levelPrimes_8_ = lean_ctor_get(v_host_6_, 5);
lean_inc(v_levelPrimes_8_);
lean_dec_ref(v_host_6_);
v_q_9_ = lean_ctor_get(v_toHostAx_7_, 0);
lean_inc(v_q_9_);
v_d_10_ = lean_ctor_get(v_toHostAx_7_, 1);
lean_inc(v_d_10_);
v_QS_11_ = lean_ctor_get(v_toHostAx_7_, 2);
lean_inc(v_QS_11_);
lean_dec_ref(v_toHostAx_7_);
v___f_12_ = ((lean_object*)(lp_tree_Formalism_L2_Pj_badN___closed__0));
v___x_13_ = lean_nat_mul(v_QS_11_, v_q_9_);
lean_dec(v_q_9_);
lean_dec(v_QS_11_);
v___x_14_ = lean_nat_mul(v___x_13_, v_d_10_);
lean_dec(v_d_10_);
lean_dec(v___x_13_);
v___x_15_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v_levelPrimes_8_, v___f_12_);
v___x_16_ = lean_nat_mul(v___x_14_, v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt___redArg(lean_object* v_D_17_, lean_object* v_i_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lp_tree_Formalism_MainNotions_WeightAlgebra_g0(v_D_17_);
v___x_20_ = lean_nat_mul(v___x_19_, v_i_18_);
lean_dec(v___x_19_);
v___x_21_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt___redArg___boxed(lean_object* v_D_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_L2_Pj_wEt___redArg(v_D_22_, v_i_23_);
lean_dec(v_i_23_);
lean_dec_ref(v_D_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt(lean_object* v_D_25_, lean_object* v_j_26_, lean_object* v_i_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_L2_Pj_wEt___redArg(v_D_25_, v_i_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_wEt___boxed(lean_object* v_D_29_, lean_object* v_j_30_, lean_object* v_i_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_L2_Pj_wEt(v_D_29_, v_j_30_, v_i_31_);
lean_dec(v_i_31_);
lean_dec(v_j_30_);
lean_dec_ref(v_D_29_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ResChPrime(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CuspidalL2Subspace(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ValSetAlgSubset(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_AllTest(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_DatIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThShort(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_HasDataCondition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ResChPrime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_CuspidalL2Subspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ValSetAlgSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_AllTest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_DatIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThShort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
