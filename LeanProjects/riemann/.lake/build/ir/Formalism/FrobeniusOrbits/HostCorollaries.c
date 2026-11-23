// Lean compiler output
// Module: Formalism.FrobeniusOrbits.HostCorollaries
// Imports: public import Init public meta import Init public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardExtendedGaloisGroup public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickOrbit public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickFrames public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ExistsOpenNormalOrderOf public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrdUnimod public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrbitSg public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
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
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_HostCorollaries(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
