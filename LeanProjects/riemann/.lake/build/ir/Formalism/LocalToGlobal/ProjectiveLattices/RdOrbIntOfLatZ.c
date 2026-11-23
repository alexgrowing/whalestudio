// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Pj_FJ_cM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Pj_FJ_cM___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Pj_FJ_cM___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_cM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_cM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_cM___redArg(lean_object* v_A_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___f_5_; lean_object* v___x_6_; 
v___f_5_ = ((lean_object*)(lp_tree_Formalism_L2_Pj_FJ_cM___redArg___closed__0));
v___x_6_ = lp_mathlib_Matrix_map___redArg(v_A_2_, v___f_5_, v_a_3_, v_a_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_cM(lean_object* v_m_7_, lean_object* v_n_8_, lean_object* v_A_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_L2_Pj_FJ_cM___redArg(v_A_9_, v_a_10_, v_a_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___lam__0(lean_object* v_e_13_, lean_object* v_00_u03c4_14_, lean_object* v_k_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_apply_2(v_e_13_, v_a_16_, v_k_15_);
v___x_18_ = lean_apply_1(v_00_u03c4_14_, v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___redArg(lean_object* v_00_u03c4_20_, lean_object* v_e_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_24_; lean_object* v_toFun_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v___x_24_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___closed__0, &lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___closed__0);
v_toFun_25_ = lean_ctor_get(v___x_24_, 0);
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_FJ_Fm___redArg___lam__0), 4, 2);
lean_closure_set(v___f_26_, 0, v_e_21_);
lean_closure_set(v___f_26_, 1, v_00_u03c4_20_);
lean_inc(v_toFun_25_);
v___x_27_ = lean_apply_3(v_toFun_25_, v___f_26_, v_a_22_, v_a_23_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm(lean_object* v_E_28_, lean_object* v_inst_29_, lean_object* v_r_30_, lean_object* v_00_u03c1_31_, lean_object* v_00_u03c4_32_, lean_object* v_e_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_L2_Pj_FJ_Fm___redArg(v_00_u03c4_32_, v_e_33_, v_a_34_, v_a_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FJ_Fm___boxed(lean_object* v_E_37_, lean_object* v_inst_38_, lean_object* v_r_39_, lean_object* v_00_u03c1_40_, lean_object* v_00_u03c4_41_, lean_object* v_e_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_L2_Pj_FJ_Fm(v_E_37_, v_inst_38_, v_r_39_, v_00_u03c1_40_, v_00_u03c4_41_, v_e_42_, v_a_43_, v_a_44_);
lean_dec(v_00_u03c1_40_);
lean_dec(v_r_39_);
lean_dec_ref(v_inst_38_);
return v_res_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
