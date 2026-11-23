// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.ProdFormula public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SpecDet public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DeterminantCauchySchwarz public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_DivisionValues_Rb_tw___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DivisionValues_Rb_tw___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_DivisionValues_Rb_tw___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_Rb_tw___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_Rb_tw(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_Rb_tw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_Rb_tw___redArg(lean_object* v_inst_2_, lean_object* v_00_u03c3_3_){
_start:
{
lean_object* v___f_4_; lean_object* v___f_5_; lean_object* v___f_6_; 
v___f_4_ = ((lean_object*)(lp_tree_Formalism_DivisionValues_Rb_tw___redArg___closed__0));
v___f_5_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5_, 0, v_inst_2_);
lean_closure_set(v___f_5_, 1, v_00_u03c3_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6_, 0, v___f_5_);
lean_closure_set(v___f_6_, 1, v___f_4_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_Rb_tw(lean_object* v_K_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_00_u03c3_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_tree_Formalism_DivisionValues_Rb_tw___redArg(v_inst_9_, v_00_u03c3_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_Rb_tw___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03c3_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_DivisionValues_Rb_tw(v_K_12_, v_inst_13_, v_inst_14_, v_00_u03c3_15_);
lean_dec_ref(v_inst_13_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
