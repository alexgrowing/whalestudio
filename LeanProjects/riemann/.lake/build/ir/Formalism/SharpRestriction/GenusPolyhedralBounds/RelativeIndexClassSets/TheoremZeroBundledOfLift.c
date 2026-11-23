// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift
// Imports: public import Init public meta import Init public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthBaseT0 public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthPoleInLift public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLengths
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
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LengthBaseT0(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LengthPoleInLift(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroBundledOfLengths(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroBundledOfLift(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LengthBaseT0(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LengthPoleInLift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_TheoremZeroBundledOfLengths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
