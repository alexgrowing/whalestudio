// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.FinalD public import Formalism.GradedWeylDivisibility.StatementE public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQWordAdj public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas public import Formalism.PieriBlockIdeals.PieriColumnMinors.LowerTriangularIntegral public import Formalism.PieriBlockIdeals.PieriColumnMinors.LrfcApplyWordAppendSingle public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
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
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalD(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementE(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral(uint8_t builtin);
lean_object* initialize_tree_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
