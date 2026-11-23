// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.Statement
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
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_pairMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_pairMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_pairMat___redArg(lean_object* v_X_1_, lean_object* v_Y_2_, lean_object* v_i_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_j_4_);
lean_inc(v_i_3_);
v___x_5_ = lean_apply_2(v_X_1_, v_i_3_, v_j_4_);
v___x_6_ = lean_apply_2(v_Y_2_, v_i_3_, v_j_4_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v___x_5_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_pairMat(lean_object* v_R_8_, lean_object* v_n_9_, lean_object* v_X_10_, lean_object* v_Y_11_, lean_object* v_i_12_, lean_object* v_j_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_UG_P_pairMat___redArg(v_X_10_, v_Y_11_, v_i_12_, v_j_13_);
return v___x_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
