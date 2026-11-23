// Lean compiler output
// Module: Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
// Imports: public import Init public meta import Init public import Formalism.HyperbolicPlaceProducts.Statement public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CardEqCardRangeNsmulMulCardKer public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SesquilinearDeterminantHolds public import Mathlib public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SubgroupCount public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.OmegaPow public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CountO public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions
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
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
