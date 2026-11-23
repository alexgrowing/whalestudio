// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.DualWeylDominanceOf
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockHerm public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockPos public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf
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
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HighestWeightVectorNeZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRowWeight(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylSat(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylPoint(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowGraded(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylIntRat(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMul(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylRowDivStable(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowNuSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockHerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockPos(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockWeightOrth(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HighestWeightVectorNeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRowWeight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylSat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylPoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowGraded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylIntRat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylRowDivStable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowNuSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockHerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockWeightOrth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
