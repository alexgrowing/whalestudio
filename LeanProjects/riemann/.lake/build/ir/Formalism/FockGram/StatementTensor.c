// Lean compiler output
// Module: Formalism.FockGram.StatementTensor
// Imports: public import Init public meta import Init public import Formalism.FockGram.StatementLat
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
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_instSMul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_addMonoid___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_leftHasSMul___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_mapBilinear___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_lid___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_llcomp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_compr_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_compl_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_TensorProduct_liftAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_E_tensorFunctional___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_E_tensorFunctional___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_E_tensorFunctional___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_E_tensorFunctional___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_tensorFunctional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_htmul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_htmul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_E_tensorFunctional___redArg(lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v_toSemiring_7_; lean_object* v_toAddMonoid_8_; lean_object* v_toAddCommMonoid_9_; lean_object* v_toAddMonoid_10_; lean_object* v___x_11_; lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toLinearMap_19_; lean_object* v___x_51__overap_20_; lean_object* v___x_21_; lean_object* v___f_22_; 
v_toSemiring_7_ = lean_ctor_get(v_inst_2_, 0);
lean_inc_ref_n(v_toSemiring_7_, 10);
lean_dec_ref(v_inst_2_);
v_toAddMonoid_8_ = lean_ctor_get(v_inst_3_, 0);
lean_inc_ref_n(v_toAddMonoid_8_, 3);
lean_dec_ref(v_inst_3_);
v_toAddCommMonoid_9_ = lean_ctor_get(v_toSemiring_7_, 0);
lean_inc_ref_n(v_toAddCommMonoid_9_, 8);
v_toAddMonoid_10_ = lean_ctor_get(v_inst_5_, 0);
lean_inc_ref_n(v_toAddMonoid_10_, 3);
lean_dec_ref(v_inst_5_);
v___x_11_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_7_);
v___f_12_ = ((lean_object*)(lp_tree_Formalism_E_tensorFunctional___redArg___closed__0));
lean_inc_n(v_inst_6_, 2);
lean_inc_n(v_inst_4_, 3);
v___x_13_ = lp_mathlib_TensorProduct_addMonoid___redArg(v_toSemiring_7_, v_toAddMonoid_8_, v_toAddMonoid_10_, v_inst_4_, v_inst_6_);
lean_inc_n(v___x_11_, 8);
v___x_14_ = lp_mathlib_TensorProduct_addMonoid___redArg(v_toSemiring_7_, v_toAddCommMonoid_9_, v_toAddCommMonoid_9_, v___x_11_, v___x_11_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_TensorProduct_leftHasSMul___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_15_, 0, v_toSemiring_7_);
lean_closure_set(v___f_15_, 1, v_toAddMonoid_8_);
lean_closure_set(v___f_15_, 2, v_toAddMonoid_10_);
lean_closure_set(v___f_15_, 3, v_inst_4_);
lean_closure_set(v___f_15_, 4, v_inst_6_);
lean_closure_set(v___f_15_, 5, v_inst_4_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_TensorProduct_leftHasSMul___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_16_, 0, v_toSemiring_7_);
lean_closure_set(v___f_16_, 1, v_toAddCommMonoid_9_);
lean_closure_set(v___f_16_, 2, v_toAddCommMonoid_9_);
lean_closure_set(v___f_16_, 3, v___x_11_);
lean_closure_set(v___f_16_, 4, v___x_11_);
lean_closure_set(v___f_16_, 5, v___x_11_);
v___x_17_ = lp_mathlib_TensorProduct_mapBilinear___redArg(v_toSemiring_7_, v_toSemiring_7_, v___f_12_, v_toAddMonoid_8_, v_toAddMonoid_10_, v_toAddCommMonoid_9_, v_toAddCommMonoid_9_, v_inst_4_, v_inst_6_, v___x_11_, v___x_11_);
v___x_18_ = lp_mathlib_TensorProduct_lid___redArg(v_toSemiring_7_, v_toAddCommMonoid_9_, v___x_11_);
v_toLinearMap_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_toLinearMap_19_);
lean_dec_ref(v___x_18_);
v___x_51__overap_20_ = lp_mathlib_LinearMap_llcomp___redArg(v_toSemiring_7_, v_toSemiring_7_, v_toSemiring_7_, v___x_13_, v___x_14_, v_toAddCommMonoid_9_, v___f_15_, v___f_16_, v___x_11_, v___f_12_, v___f_12_, v___f_12_);
v___x_21_ = lean_apply_1(v___x_51__overap_20_, v_toLinearMap_19_);
v___f_22_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_compr_u2082___redArg___lam__0), 4, 2);
lean_closure_set(v___f_22_, 0, v___x_21_);
lean_closure_set(v___f_22_, 1, v___x_17_);
return v___f_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_tensorFunctional(lean_object* v_R_23_, lean_object* v_M_u2081_24_, lean_object* v_M_u2082_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_tree_Formalism_E_tensorFunctional___redArg(v_inst_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_inst_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_htmul___redArg(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_B_u2081_38_, lean_object* v_B_u2082_39_){
_start:
{
lean_object* v_toSemiring_40_; lean_object* v_toAddMonoid_41_; lean_object* v_toAddCommMonoid_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v_toSemiring_40_ = lean_ctor_get(v_inst_32_, 0);
lean_inc_ref_n(v_toSemiring_40_, 2);
v_toAddMonoid_41_ = lean_ctor_get(v_inst_36_, 0);
lean_inc_ref(v_toAddMonoid_41_);
v_toAddCommMonoid_42_ = lean_ctor_get(v_toSemiring_40_, 0);
v___x_43_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_40_);
lean_inc_ref(v_toAddCommMonoid_42_);
v___x_44_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddCommMonoid_42_);
v___f_45_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_instSMul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_45_, 0, v___x_43_);
lean_inc(v_inst_37_);
v___x_46_ = lp_tree_Formalism_E_tensorFunctional___redArg(v_inst_32_, v_inst_34_, v_inst_35_, v_inst_36_, v_inst_37_);
v___f_47_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_47_, 0, v_B_u2081_38_);
lean_closure_set(v___f_47_, 1, v___x_46_);
v___f_48_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_compl_u2082___redArg___lam__0), 4, 2);
lean_closure_set(v___f_48_, 0, v___f_47_);
lean_closure_set(v___f_48_, 1, v_B_u2082_39_);
v___x_49_ = lp_mathlib_TensorProduct_liftAux___redArg(v_toSemiring_40_, v_toSemiring_40_, v_inst_33_, v_toAddMonoid_41_, v___x_44_, v_inst_37_, v___f_45_, v___f_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_E_htmul(lean_object* v_R_50_, lean_object* v_M_u2081_51_, lean_object* v_M_u2082_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_B_u2081_59_, lean_object* v_B_u2082_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_tree_Formalism_E_htmul___redArg(v_inst_53_, v_inst_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_inst_58_, v_B_u2081_59_, v_B_u2082_60_);
return v___x_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_StatementLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FockGram_StatementTensor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
