// Lean compiler output
// Module: Formalism.FlagUnipotentLattices.IdealCountLeW
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HyperbolicPlaceProducts.Statement public import Formalism.FlagUnipotentLattices.LiftUnitaryFixesBase
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_hdual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_hdual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_hdual(lean_object* v_K_1_, lean_object* v_U_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_h_7_, lean_object* v_O_8_, lean_object* v_M_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_hdual___boxed(lean_object* v_K_11_, lean_object* v_U_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_h_17_, lean_object* v_O_18_, lean_object* v_M_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_HermitianLatticeCounting_S6_hdual(v_K_11_, v_U_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_inst_16_, v_h_17_, v_O_18_, v_M_19_);
lean_dec(v_h_17_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_15_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FlagUnipotentLattices_IdealCountLeW(uint8_t builtin) {
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
res = initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
