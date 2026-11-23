// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic public import Formalism.StatementOC
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
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_level(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_level___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_level(lean_object* v_T_1_, lean_object* v_o_2_){
_start:
{
lean_object* v_toKSet_3_; lean_object* v___x_4_; 
v_toKSet_3_ = lean_ctor_get(v_T_1_, 0);
lean_inc_ref(v_toKSet_3_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_toKSet_3_);
lean_ctor_set(v___x_4_, 1, v_o_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HType_level___boxed(lean_object* v_T_5_, lean_object* v_o_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_tree_Formalism_HC_HType_level(v_T_5_, v_o_6_);
lean_dec_ref(v_T_5_);
return v_res_7_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic(uint8_t builtin);
lean_object* initialize_tree_Formalism_StatementOC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_StatementOC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
