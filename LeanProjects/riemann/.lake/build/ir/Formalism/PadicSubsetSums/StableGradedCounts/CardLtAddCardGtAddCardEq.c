// Lean compiler output
// Module: Formalism.PadicSubsetSums.StableGradedCounts.CardLtAddCardGtAddCardEq
// Imports: public import Init public meta import Init public import Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic public import Formalism.PadicSubsetSums.StableGradedCounts.ZReuse public import Formalism.PadicSubsetSums.StableGradedCounts.ZCircleCharExtends public import Formalism.PadicSubsetSums.StableGradedCounts.FactorOverLocalSubalgebra public import Formalism.PadicSubsetSums.StableGradedCounts.CharpolyFactorAnnihilator public import Formalism.PadicSubsetSums.StableGradedCounts.ZGoodCuspidal public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal(uint8_t builtin);
lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
