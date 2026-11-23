// Lean compiler output
// Module: Formalism.RankGapBounds.RandomSubsetCounterexample
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_unitOfCoprime___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___redArg(lean_object* v_e_1_, lean_object* v_l_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_3_ = lean_unsigned_to_nat(4u);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_pow(v___x_4_, v_e_1_);
v___x_6_ = lean_nat_mul(v___x_3_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lp_mathlib_ZMod_unitOfCoprime___redArg(v___x_6_, v_l_2_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___redArg___boxed(lean_object* v_e_8_, lean_object* v_l_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___redArg(v_e_8_, v_l_9_);
lean_dec(v_e_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf(lean_object* v_e_11_, lean_object* v_l_12_, lean_object* v_hl_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___redArg(v_e_11_, v_l_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf___boxed(lean_object* v_e_15_, lean_object* v_l_16_, lean_object* v_hl_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_RankGapBounds_LocalQuadraticParts_hOf(v_e_15_, v_l_16_, v_hl_17_);
lean_dec(v_e_15_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RankGapBounds_RandomSubsetCounterexample(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
