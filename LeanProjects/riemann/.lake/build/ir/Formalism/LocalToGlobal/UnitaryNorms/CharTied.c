// Lean compiler output
// Module: Formalism.LocalToGlobal.UnitaryNorms.CharTied
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataTheta public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_eExp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_embLL0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_CharFrame_delAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_CharFrame_delAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_eExp(lean_object* v_D_1_, lean_object* v_j_2_, lean_object* v_g_3_){
_start:
{
lean_object* v_eTau_4_; lean_object* v_hc_5_; lean_object* v___x_6_; lean_object* v_toFun_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_e_10_; lean_object* v___x_11_; 
v_eTau_4_ = lean_ctor_get(v_D_1_, 5);
lean_inc_ref(v_eTau_4_);
v_hc_5_ = lean_ctor_get(v_D_1_, 6);
lean_inc_ref(v_hc_5_);
lean_dec_ref(v_D_1_);
v___x_6_ = lp_mathlib_Equiv_symm___redArg(v_eTau_4_);
v_toFun_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_toFun_7_);
lean_dec_ref(v___x_6_);
v___x_8_ = lean_apply_1(v_toFun_7_, v_g_3_);
v___x_9_ = lean_apply_1(v_hc_5_, v___x_8_);
v_e_10_ = lean_ctor_get(v___x_9_, 3);
lean_inc_ref(v_e_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lean_apply_1(v_e_10_, v_j_2_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___lam__0(lean_object* v_self_12_){
_start:
{
lean_inc(v_self_12_);
return v_self_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___lam__0___boxed(lean_object* v_self_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___lam__0(v_self_13_);
lean_dec(v_self_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0(lean_object* v___x_16_, lean_object* v_S_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = ((lean_object*)(lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___closed__0));
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___boxed(lean_object* v___x_19_, lean_object* v_S_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0(v___x_19_, v_S_20_);
lean_dec_ref(v___x_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0(lean_object* v___x_22_, lean_object* v_S_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = ((lean_object*)(lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___closed__0));
return v___f_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0___boxed(lean_object* v___x_25_, lean_object* v_S_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0(v___x_25_, v_S_26_);
lean_dec_ref(v___x_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_embLL0(lean_object* v_D_28_){
_start:
{
lean_object* v_what_u2082_29_; lean_object* v_embLL_30_; lean_object* v___f_31_; lean_object* v___f_32_; 
v_what_u2082_29_ = lean_ctor_get(v_D_28_, 4);
lean_inc_ref(v_what_u2082_29_);
lean_dec_ref(v_D_28_);
v_embLL_30_ = lean_ctor_get(v_what_u2082_29_, 1);
lean_inc_ref(v_embLL_30_);
lean_dec_ref(v_what_u2082_29_);
v___f_31_ = ((lean_object*)(lp_tree_Subalgebra_val___at___00IntermediateField_val___at___00Formalism_L2_Host_embLL0_spec__0_spec__0___closed__0));
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_32_, 0, v___f_31_);
lean_closure_set(v___f_32_, 1, v_embLL_30_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_CharFrame_delAt(lean_object* v_D_33_, lean_object* v_C_34_, lean_object* v_l_35_){
_start:
{
lean_object* v_host_36_; lean_object* v_pde_37_; uint8_t v___x_38_; 
v_host_36_ = lean_ctor_get(v_D_33_, 1);
v_pde_37_ = lean_ctor_get(v_host_36_, 7);
v___x_38_ = lean_nat_dec_eq(v_l_35_, v_pde_37_);
if (v___x_38_ == 0)
{
lean_object* v_del_39_; 
v_del_39_ = lean_ctor_get(v_C_34_, 5);
lean_inc_ref(v_del_39_);
return v_del_39_;
}
else
{
lean_object* v_del_x27_40_; 
v_del_x27_40_ = lean_ctor_get(v_C_34_, 6);
lean_inc_ref(v_del_x27_40_);
return v_del_x27_40_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_CharFrame_delAt___boxed(lean_object* v_D_41_, lean_object* v_C_42_, lean_object* v_l_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_L2_Host_CharFrame_delAt(v_D_41_, v_C_42_, v_l_43_);
lean_dec(v_l_43_);
lean_dec_ref(v_C_42_);
lean_dec_ref(v_D_41_);
return v_res_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataTheta(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharUniq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharTied(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharUniq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
