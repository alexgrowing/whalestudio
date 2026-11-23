// Lean compiler output
// Module: Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LandauZeroFreeBounds.Statement
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
uint8_t l_Nat_decidable__dvd(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorization(lean_object*);
uint8_t lp_mathlib_Nat_instDecidablePredOdd(lean_object*);
lean_object* lp_mathlib_Nat_primeFactors(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__1___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___closed__0 = (const lean_object*)&lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__0(lean_object* v_m_u2080_1_, lean_object* v_m_2_, lean_object* v_a_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Nat_decidable__dvd(v_a_3_, v_m_u2080_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; lean_object* v_toFun_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_5_ = lp_mathlib_Nat_factorization(v_m_2_);
v_toFun_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_toFun_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_1(v_toFun_6_, v_a_3_);
v___x_8_ = lp_mathlib_Nat_instDecidablePredOdd(v___x_7_);
lean_dec(v___x_7_);
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
lean_dec(v_a_3_);
lean_dec(v_m_2_);
v___x_9_ = 0;
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__0___boxed(lean_object* v_m_u2080_10_, lean_object* v_m_11_, lean_object* v_a_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__0(v_m_u2080_10_, v_m_11_, v_a_12_);
lean_dec(v_m_u2080_10_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__1(lean_object* v_p_15_){
_start:
{
lean_inc(v_p_15_);
return v_p_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__1___boxed(lean_object* v_p_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__1(v_p_16_);
lean_dec(v_p_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart(lean_object* v_m_u2080_19_, lean_object* v_m_20_){
_start:
{
lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc(v_m_20_);
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_21_, 0, v_m_u2080_19_);
lean_closure_set(v___f_21_, 1, v_m_20_);
v___f_22_ = ((lean_object*)(lp_tree_Formalism_HermitianLattices_GL2PrimeSums_outPart___closed__0));
v___x_23_ = lp_mathlib_Nat_primeFactors(v_m_20_);
lean_dec(v_m_20_);
v___x_24_ = lp_mathlib_Multiset_filter___redArg(v___f_21_, v___x_23_);
v___x_25_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_24_, v___f_22_);
return v___x_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LandauZeroFreeBounds_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula(uint8_t builtin) {
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
res = initialize_tree_Formalism_LandauZeroFreeBounds_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
