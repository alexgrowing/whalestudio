// Lean compiler output
// Module: Formalism.JacobiWeightFamilies.Statement
// Imports: public import Init public meta import Init public import Formalism.HalfLinks.Statement
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(lean_object*, lean_object*);
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_WT_chiJ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_WT_chiJ(lean_object* v_d_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_nat_to_int(v_n_2_);
v___x_4_ = lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(v___x_3_, v_d_1_);
lean_dec(v___x_3_);
v___x_5_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_4_);
return v___x_5_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_HalfLinks_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_JacobiWeightFamilies_Statement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HalfLinks_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
