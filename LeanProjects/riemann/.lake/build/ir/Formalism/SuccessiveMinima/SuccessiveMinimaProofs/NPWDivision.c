// Lean compiler output
// Module: Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPWDivision
// Imports: public import Init public meta import Init public import Formalism.SuccessiveMinima.DefsNP public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NewtonSlope
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
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Polynomial_coeff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_WDiv_cN___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_WDiv_cN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_WDiv_cN___redArg(lean_object* v_inst_1_, lean_object* v_G_2_, lean_object* v_N_3_, lean_object* v_P_4_){
_start:
{
lean_object* v_toField_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toDiv_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_toField_5_ = lean_ctor_get(v_inst_1_, 1);
lean_inc_ref(v_toField_5_);
lean_dec_ref(v_inst_1_);
v___x_6_ = lp_mathlib_Field_toDivisionRing___redArg(v_toField_5_);
v___x_7_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_6_);
lean_dec_ref(v___x_6_);
v_toDiv_8_ = lean_ctor_get(v___x_7_, 2);
lean_inc(v_toDiv_8_);
lean_dec_ref(v___x_7_);
lean_inc(v_N_3_);
v___x_9_ = lp_mathlib_Polynomial_coeff___redArg(v_P_4_, v_N_3_);
v___x_10_ = lp_mathlib_Polynomial_coeff___redArg(v_G_2_, v_N_3_);
v___x_11_ = lean_apply_2(v_toDiv_8_, v___x_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FN_WDiv_cN(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_G_14_, lean_object* v_N_15_, lean_object* v_P_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_FN_WDiv_cN___redArg(v_inst_13_, v_G_14_, v_N_15_, v_P_16_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_DefsNP(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_DefsNP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
