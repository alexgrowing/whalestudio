// Lean compiler output
// Module: Formalism.HarderNarasimhan.ShiftInvariance
// Imports: public import Init public meta import Init public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
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
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HarderNarasimhan_ShiftInvariance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
