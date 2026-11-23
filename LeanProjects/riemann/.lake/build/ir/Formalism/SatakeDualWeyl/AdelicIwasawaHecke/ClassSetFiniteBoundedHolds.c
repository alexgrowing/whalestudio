// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSetFiniteBoundedHolds
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.DefsCS public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal public import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors public import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
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
lean_object* initialize_tree_Formalism_SatakeDualWeyl_DefsCS(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassSetFiniteBoundedHolds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_DefsCS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
