// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.RatHermLcvTwist public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsChain public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.JwConj public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DualMu public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
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
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___lam__0(lean_object* v_z_1_, lean_object* v_i_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_z_1_, v_a_3_, v_i_2_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___closed__0(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg(lean_object* v_z_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; lean_object* v_toFun_10_; lean_object* v___f_11_; lean_object* v___x_12_; 
v___x_9_ = lean_obj_once(&lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___closed__0, &lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___closed__0_once, _init_lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___closed__0);
v_toFun_10_ = lean_ctor_get(v___x_9_, 0);
v___f_11_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg___lam__0), 3, 1);
lean_closure_set(v___f_11_, 0, v_z_6_);
lean_inc(v_toFun_10_);
v___x_12_ = lean_apply_3(v_toFun_10_, v___f_11_, v_a_7_, v_a_8_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat(lean_object* v_K_13_, lean_object* v_n_14_, lean_object* v_d_15_, lean_object* v_z_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___redArg(v_z_16_, v_a_17_, v_a_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat___boxed(lean_object* v_K_20_, lean_object* v_n_21_, lean_object* v_d_22_, lean_object* v_z_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_DivisionValues_ConjugateWeightGram_colMat(v_K_20_, v_n_21_, v_d_22_, v_z_23_, v_a_24_, v_a_25_);
lean_dec(v_d_22_);
lean_dec(v_n_21_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
