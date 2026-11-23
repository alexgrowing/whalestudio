// Lean compiler output
// Module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep
// Imports: public import Init public meta import Init public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
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
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_monSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_monSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_monSpan(lean_object* v_R_1_, lean_object* v_M_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_d_6_, lean_object* v_g_7_, lean_object* v_k_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_PoleLengthBounds_monSpan___boxed(lean_object* v_R_10_, lean_object* v_M_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_d_15_, lean_object* v_g_16_, lean_object* v_k_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_PoleLengthBounds_monSpan(v_R_10_, v_M_11_, v_inst_12_, v_inst_13_, v_inst_14_, v_d_15_, v_g_16_, v_k_17_);
lean_dec(v_k_17_);
lean_dec(v_g_16_);
lean_dec(v_d_15_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_12_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_TaylorSpanGeneratorsAlt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_TaylorRep(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BaseLengthBound_TaylorSpanGeneratorsAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
