// Lean compiler output
// Module: Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
// Imports: public import Init public meta import Init public import Formalism.CharacterColumnKernels.Statement public import Lemmata.SecondBlockLemmaA.Imports public import Lemmata.AddValuationProducts.AddValProd
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__0(lean_object* v_toOne_1_, lean_object* v_r_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_r_2_);
lean_ctor_set(v___x_3_, 1, v_toOne_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__1(lean_object* v___f_4_, lean_object* v___f_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_4_, v___f_5_, v___y_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg(lean_object* v_inst_9_, lean_object* v_A_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_toSemiring_13_; lean_object* v_toMonoid_14_; lean_object* v___x_15_; lean_object* v_toOne_16_; lean_object* v___f_17_; lean_object* v___f_18_; lean_object* v___f_19_; lean_object* v___x_20_; 
v_toSemiring_13_ = lean_ctor_get(v_inst_9_, 0);
v_toMonoid_14_ = lean_ctor_get(v_toSemiring_13_, 1);
v___x_15_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_14_);
v_toOne_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_toOne_16_);
lean_dec_ref(v___x_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__0), 2, 1);
lean_closure_set(v___f_17_, 0, v_toOne_16_);
v___f_18_ = ((lean_object*)(lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___closed__0));
v___f_19_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__1), 3, 2);
lean_closure_set(v___f_19_, 0, v___f_18_);
lean_closure_set(v___f_19_, 1, v___f_17_);
v___x_20_ = lp_mathlib_Matrix_map___redArg(v_A_10_, v___f_19_, v_a_11_, v_a_12_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___boxed(lean_object* v_inst_21_, lean_object* v_A_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg(v_inst_21_, v_A_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_inst_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK(lean_object* v_O_26_, lean_object* v_inst_27_, lean_object* v_00_u03b9_28_, lean_object* v_A_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_toSemiring_32_; lean_object* v_toMonoid_33_; lean_object* v___x_34_; lean_object* v_toOne_35_; lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_toSemiring_32_ = lean_ctor_get(v_inst_27_, 0);
v_toMonoid_33_ = lean_ctor_get(v_toSemiring_32_, 1);
v___x_34_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_33_);
v_toOne_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_toOne_35_);
lean_dec_ref(v___x_34_);
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__0), 2, 1);
lean_closure_set(v___f_36_, 0, v_toOne_35_);
v___f_37_ = ((lean_object*)(lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___closed__0));
v___f_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___redArg___lam__1), 3, 2);
lean_closure_set(v___f_38_, 0, v___f_37_);
lean_closure_set(v___f_38_, 1, v___f_36_);
v___x_39_ = lp_mathlib_Matrix_map___redArg(v_A_29_, v___f_38_, v_a_30_, v_a_31_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK___boxed(lean_object* v_O_40_, lean_object* v_inst_41_, lean_object* v_00_u03b9_42_, lean_object* v_A_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Formalism_NG_IdempotentNormalFormsLenFacts_AK(v_O_40_, v_inst_41_, v_00_u03b9_42_, v_A_43_, v_a_44_, v_a_45_);
lean_dec_ref(v_inst_41_);
return v_res_46_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CharacterColumnKernels_Statement(uint8_t builtin);
lean_object* initialize_tree_Lemmata_SecondBlockLemmaA_Imports(uint8_t builtin);
lean_object* initialize_tree_Lemmata_AddValuationProducts_AddValProd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CharacterColumnKernels_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_SecondBlockLemmaA_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_AddValuationProducts_AddValProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
