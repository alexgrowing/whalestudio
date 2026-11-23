// Lean compiler output
// Module: Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
// Imports: public import Init public meta import Init public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf public import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties public import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector public import Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin public import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum
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
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxLeMin(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxLeMin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
