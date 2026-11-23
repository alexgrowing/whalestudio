// Lean compiler output
// Module: Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith public import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData public import Formalism.RankGapBounds.RankGapProofs.UniformMeanTopLine
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
static lean_once_cell_t lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1;
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_2_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2_, 0, v___x_1_);
lean_ctor_set(v___x_2_, 1, v___x_1_);
lean_ctor_set(v___x_2_, 2, v___x_1_);
lean_ctor_set(v___x_2_, 3, v___x_1_);
lean_ctor_set(v___x_2_, 4, v___x_1_);
lean_ctor_set(v___x_2_, 5, v___x_1_);
lean_ctor_set(v___x_2_, 6, v___x_1_);
lean_ctor_set(v___x_2_, 7, v___x_1_);
lean_ctor_set(v___x_2_, 8, v___x_1_);
lean_ctor_set(v___x_2_, 9, v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1___closed__0, &lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1___closed__0_once, _init_lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1___closed__0);
return v___x_3_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith(uint8_t builtin);
lean_object* initialize_tree_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData(uint8_t builtin);
lean_object* initialize_tree_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1 = _init_lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1();
lean_mark_persistent(lp_tree_Formalism_LFunctionChainParameters_WeightedSlopeBounds_C1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
