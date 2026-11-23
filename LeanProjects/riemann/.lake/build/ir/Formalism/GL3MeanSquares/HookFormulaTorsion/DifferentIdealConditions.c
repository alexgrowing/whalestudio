// Lean compiler output
// Module: Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.GL3MeanSquares.OrbitPointsDistinct public import Formalism.FrobeniusOrbits.HostCorollaries public import Formalism.DirichletDensity.HostDensityArith
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm(lean_object* v_L_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_00_u03b6_4_, lean_object* v_a_5_, lean_object* v_b_6_, lean_object* v_P_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm___boxed(lean_object* v_L_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_00_u03b6_12_, lean_object* v_a_13_, lean_object* v_b_14_, lean_object* v_P_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm(v_L_9_, v_inst_10_, v_inst_11_, v_00_u03b6_12_, v_a_13_, v_b_14_, v_P_15_);
lean_dec(v_b_14_);
lean_dec(v_a_13_);
lean_dec(v_00_u03b6_12_);
lean_dec_ref(v_inst_10_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_OrbitPointsDistinct(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(uint8_t builtin);
lean_object* initialize_tree_Formalism_DirichletDensity_HostDensityArith(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions(uint8_t builtin) {
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
res = initialize_tree_Formalism_GL3MeanSquares_OrbitPointsDistinct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DirichletDensity_HostDensityArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
