// Lean compiler output
// Module: Formalism.GaussJetBounds.GaussJetProofs.ThmAJet
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.GenLogInverse public import Formalism.GaussJetBounds.StatementE public import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound public import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight public import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight public import Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity public import Formalism.IncomingBounds.WeightIdentities public import Formalism.GaussJetBounds.OneLetterRadius public import Formalism.GaussJetBounds.GaussJetProofs.FrameCoeffMulLin public import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity
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
lean_object* initialize_tree_Formalism_GaussJetBounds_GenLogInverse(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementE(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity(uint8_t builtin);
lean_object* initialize_tree_Formalism_IncomingBounds_WeightIdentities(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GenLogInverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_IncomingBounds_WeightIdentities(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_OneLetterRadius(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
