// Lean compiler output
// Module: Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_abs___at___00BoundingSieve_errSum_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_area(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_area(lean_object* v_L_1_){
_start:
{
lean_object* v_00_u03c9_u2081_2_; lean_object* v_00_u03c9_u2082_3_; lean_object* v___x_4_; lean_object* v_re_5_; lean_object* v_im_6_; lean_object* v___x_7_; lean_object* v_im_8_; lean_object* v___x_9_; 
v_00_u03c9_u2081_2_ = lean_ctor_get(v_L_1_, 0);
lean_inc_ref(v_00_u03c9_u2081_2_);
v_00_u03c9_u2082_3_ = lean_ctor_get(v_L_1_, 1);
lean_inc_ref(v_00_u03c9_u2082_3_);
lean_dec_ref(v_L_1_);
v___x_4_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0___lam__0(v_00_u03c9_u2081_2_);
v_re_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_re_5_);
v_im_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_im_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_5_, v_im_6_, v_00_u03c9_u2082_3_);
v_im_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_im_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = lp_mathlib_abs___at___00BoundingSieve_errSum_spec__0(v_im_8_);
return v___x_9_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_SemiChar(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
