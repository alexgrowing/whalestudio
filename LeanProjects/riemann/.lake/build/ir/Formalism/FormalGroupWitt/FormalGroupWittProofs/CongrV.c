// Lean compiler output
// Module: Formalism.FormalGroupWitt.FormalGroupWittProofs.CongrV
// Imports: public import Init public meta import Init public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV public import Formalism.FormalGroupWitt.FormalGroupWittProofs.CoeffV public import Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector public import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
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
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_CongrVAux_ofFun___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_CongrVAux_ofFun(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_CongrVAux_ofFun___redArg(lean_object* v_g_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_g_1_, v_a_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_CongrVAux_ofFun(lean_object* v_K_4_, lean_object* v_00_u03c4_5_, lean_object* v_g_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_g_6_, v_a_7_);
return v___x_8_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV(uint8_t builtin);
lean_object* initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV(uint8_t builtin);
lean_object* initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector(uint8_t builtin);
lean_object* initialize_tree_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
