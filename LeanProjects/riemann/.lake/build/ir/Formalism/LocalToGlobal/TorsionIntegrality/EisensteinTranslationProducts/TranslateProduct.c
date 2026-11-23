// Lean compiler output
// Module: Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
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
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_scalePair___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_scalePair(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_scalePair___redArg(lean_object* v_L_1_, lean_object* v_c_2_){
_start:
{
lean_object* v_00_u03c9_u2081_3_; lean_object* v_00_u03c9_u2082_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_15_; 
v_00_u03c9_u2081_3_ = lean_ctor_get(v_L_1_, 0);
v_00_u03c9_u2082_4_ = lean_ctor_get(v_L_1_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_L_1_);
if (v_isSharedCheck_15_ == 0)
{
v___x_6_ = v_L_1_;
v_isShared_7_ = v_isSharedCheck_15_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_00_u03c9_u2082_4_);
lean_inc(v_00_u03c9_u2081_3_);
lean_dec(v_L_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_15_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v_re_8_; lean_object* v_im_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_13_; 
v_re_8_ = lean_ctor_get(v_c_2_, 0);
lean_inc_n(v_re_8_, 2);
v_im_9_ = lean_ctor_get(v_c_2_, 1);
lean_inc_n(v_im_9_, 2);
lean_dec_ref(v_c_2_);
v___x_10_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_8_, v_im_9_, v_00_u03c9_u2081_3_);
v___x_11_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_8_, v_im_9_, v_00_u03c9_u2082_4_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_11_);
lean_ctor_set(v___x_6_, 0, v___x_10_);
v___x_13_ = v___x_6_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v___x_11_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_F_scalePair(lean_object* v_L_16_, lean_object* v_c_17_, lean_object* v_hc_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_L2_Th1_F_scalePair___redArg(v_L_16_, v_c_17_);
return v___x_19_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
