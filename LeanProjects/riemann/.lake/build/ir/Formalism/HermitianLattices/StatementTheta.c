// Lean compiler output
// Module: Formalism.HermitianLattices.StatementTheta
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.AlphaUniqueness.Statement public import Formalism.LatticeTheta.Statement public import Formalism.HermitianLattices.StatementLat
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_weilT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_weilT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_weilT___redArg(lean_object* v_Q_1_, lean_object* v_f_2_, lean_object* v_00_u03b3_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_re_5_; lean_object* v_im_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc(v_00_u03b3_3_);
v___x_4_ = lean_apply_1(v_Q_1_, v_00_u03b3_3_);
v_re_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_re_5_);
v_im_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_im_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lean_apply_1(v_f_2_, v_00_u03b3_3_);
v___x_8_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_5_, v_im_6_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_weilT(lean_object* v_D_9_, lean_object* v_Q_10_, lean_object* v_f_11_, lean_object* v_00_u03b3_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_tree_Formalism_HermitianLatticesTheory_weilT___redArg(v_Q_10_, v_f_11_, v_00_u03b3_12_);
return v___x_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_AlphaUniqueness_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HermitianLattices_StatementTheta(uint8_t builtin) {
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
res = initialize_tree_Formalism_AlphaUniqueness_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
