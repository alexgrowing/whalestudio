// Lean compiler output
// Module: Formalism.SuccessiveMinima.MinkowskiIIUpper
// Imports: public import Init public meta import Init public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.SuccMin public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.AdaptedBasis public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MeasureEqCovolumeMulVolumeImage public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NewtonSlope public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkowskiIILowerOf public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPWDivision public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPUnit
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
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkCore(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjLevel(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_AdaptedBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MeasureEqCovolumeMulVolumeImage(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision(uint8_t builtin);
lean_object* initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SuccessiveMinima_MinkowskiIIUpper(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_AdaptedBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MeasureEqCovolumeMulVolumeImage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPUnit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
