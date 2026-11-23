// Lean compiler output
// Module: Formalism.LatticeTheta.ThetaShiftInversion
// Imports: public import Init public meta import Init public import Formalism.LatticeTheta.LatticeThetaProofs.Assembly public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeSummableDecay public import Formalism.LatticeTheta.LatticeThetaProofs.Periodization public import Formalism.LatticeTheta.LatticeThetaProofs.UnfoldCoeff public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeFourierSeries public import Formalism.LatticeTheta.LatticeThetaProofs.GaussSchwartz public import Formalism.LatticeTheta.LatticeThetaProofs.DualLattice public import Formalism.LatticeTheta.LatticeThetaProofs.CovolumeDual
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
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_Assembly(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_Periodization(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LatticeTheta_ThetaShiftInversion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_Assembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_Periodization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
