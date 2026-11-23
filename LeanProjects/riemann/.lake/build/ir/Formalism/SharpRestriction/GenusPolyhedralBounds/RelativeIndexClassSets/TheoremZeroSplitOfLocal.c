// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocal
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VanishingOrderLeWeightSize public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PvsDimYPos
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
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroSplitOfLocalAndSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_VanishingOrderLeWeightSize(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_PvsDimYPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroSplitOfLocal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroSplitOfLocalAndSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_VanishingOrderLeWeightSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_PvsDimYPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
