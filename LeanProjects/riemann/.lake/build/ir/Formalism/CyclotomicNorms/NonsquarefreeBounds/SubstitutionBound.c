// Lean compiler output
// Module: Formalism.CyclotomicNorms.NonsquarefreeBounds.SubstitutionBound
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.StatementA
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_SubstitutionExponents_weight___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_SubstitutionExponents_weight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_SubstitutionExponents_weight___lam__0(lean_object* v_d_1_, lean_object* v_n_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_toFun_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_toFun_4_ = lean_ctor_get(v_d_1_, 1);
lean_inc(v_toFun_4_);
lean_dec_ref(v_d_1_);
lean_inc(v_i_3_);
v___x_5_ = lean_apply_1(v_toFun_4_, v_i_3_);
v___x_6_ = lean_apply_1(v_n_2_, v_i_3_);
v___x_7_ = lean_nat_mul(v___x_5_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_SubstitutionExponents_weight(lean_object* v_r_8_, lean_object* v_n_9_, lean_object* v_d_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_11_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_SubstitutionExponents_weight___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_d_10_);
lean_closure_set(v___f_11_, 1, v_n_9_);
v___x_12_ = l_List_finRange(v_r_8_);
v___x_13_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_12_, v___f_11_);
return v___x_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
