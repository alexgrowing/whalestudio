// Lean compiler output
// Module: Formalism.CyclotomicNorms.NonsquarefreeBounds.Cycles
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.StatementA
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
lean_object* lp_mathlib_LinearMap_restrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleChains_resR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleChains_resR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleChains_resR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleChains_resR___redArg(lean_object* v_00_u03c1_1_, lean_object* v_g_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_apply_1(v_00_u03c1_1_, v_g_2_);
v___x_4_ = lp_mathlib_LinearMap_restrict___redArg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleChains_resR(lean_object* v_k_5_, lean_object* v_inst_6_, lean_object* v_G_7_, lean_object* v_V_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_00_u03c1_12_, lean_object* v_W_13_, lean_object* v_hW_14_, lean_object* v_g_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_tree_Formalism_CyclotomicNorms_CycleChains_resR___redArg(v_00_u03c1_12_, v_g_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CycleChains_resR___boxed(lean_object* v_k_17_, lean_object* v_inst_18_, lean_object* v_G_19_, lean_object* v_V_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_00_u03c1_24_, lean_object* v_W_25_, lean_object* v_hW_26_, lean_object* v_g_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_CyclotomicNorms_CycleChains_resR(v_k_17_, v_inst_18_, v_G_19_, v_V_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_00_u03c1_24_, v_W_25_, v_hW_26_, v_g_27_);
lean_dec(v_inst_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_18_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Cycles(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
