// Lean compiler output
// Module: Formalism.GaloisIrreducibility.NoSolvableTransitive
// Imports: public import Init public meta import Init public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.LemmaAOf public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.IrredOf public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.ResiduesLe public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.FewLargeParts public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.BlockBoundOfOrbits public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.NoSolvableOf public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.JordanPrime
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
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_BlockBoundOfOrbits(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_AltNotSolvable(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_NoSolvableOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PrimitiveOfPCycle(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaloisIrreducibility_NoSolvableTransitive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_BlockBoundOfOrbits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_AltNotSolvable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_NoSolvableOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PrimitiveOfPCycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
