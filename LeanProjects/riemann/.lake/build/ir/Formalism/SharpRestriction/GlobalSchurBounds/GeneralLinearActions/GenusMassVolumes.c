// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SatakeDualWeyl.Statement
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Algebra_TensorProduct_includeRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Algebra_TensorProduct_instNonUnitalNonAssocSemiring___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_mulVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Algebra_TensorProduct_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_nonAssocSemiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lp_mathlib_npowBinRec_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
lean_object* lp_mathlib_TensorProduct_tmul___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_AlgHom_funLike___lam__0(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_UG_hform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Algebra_TensorProduct_instRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFinIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFinIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HermR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HermR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_topTens(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_topTens___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measTens(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measTens___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instTopologicalSpaceHA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instTopologicalSpaceHA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMeasurableSpaceHAOfTopologicalSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMeasurableSpaceHAOfTopologicalSpace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_Hstab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_Hstab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HstabFin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HstabFin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measHerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measHerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE___redArg(lean_object* v_inst_1_, lean_object* v_00_u03c3_2_, lean_object* v_M_3_, lean_object* v_J_4_, lean_object* v_x_5_, lean_object* v_y_6_){
_start:
{
lean_object* v_toCommRing_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_toCommRing_7_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toCommRing_7_);
lean_dec_ref(v_inst_1_);
v___x_8_ = l_List_finRange(v_M_3_);
v___x_9_ = lean_alloc_closure((void*)(lp_mathlib_AlgHom_funLike___lam__0), 2, 1);
lean_closure_set(v___x_9_, 0, v_00_u03c3_2_);
v___x_10_ = lp_tree_Formalism_UG_hform___redArg(v_toCommRing_7_, v___x_8_, v___x_9_, v_J_4_, v_x_5_, v_y_6_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE(lean_object* v_F_11_, lean_object* v_E_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_00_u03c3_16_, lean_object* v_M_17_, lean_object* v_J_18_, lean_object* v_x_19_, lean_object* v_y_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE___redArg(v_inst_14_, v_00_u03c3_16_, v_M_17_, v_J_18_, v_x_19_, v_y_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE___boxed(lean_object* v_F_22_, lean_object* v_E_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_00_u03c3_27_, lean_object* v_M_28_, lean_object* v_J_29_, lean_object* v_x_30_, lean_object* v_y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE(v_F_22_, v_E_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_00_u03c3_27_, v_M_28_, v_J_29_, v_x_30_, v_y_31_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_24_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE___redArg(lean_object* v_inst_33_, lean_object* v_00_u03c3_34_, lean_object* v_M_35_, lean_object* v_J_36_, lean_object* v_X_37_, lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc(v_X_37_);
v___x_40_ = lean_apply_1(v_X_37_, v_a_38_);
v___x_41_ = lean_apply_1(v_X_37_, v_b_39_);
v___x_42_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hE___redArg(v_inst_33_, v_00_u03c3_34_, v_M_35_, v_J_36_, v___x_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE(lean_object* v_F_43_, lean_object* v_E_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_00_u03c3_48_, lean_object* v_M_49_, lean_object* v_n_50_, lean_object* v_J_51_, lean_object* v_X_52_, lean_object* v_a_53_, lean_object* v_b_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE___redArg(v_inst_46_, v_00_u03c3_48_, v_M_49_, v_J_51_, v_X_52_, v_a_53_, v_b_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE___boxed(lean_object* v_F_56_, lean_object* v_E_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_00_u03c3_61_, lean_object* v_M_62_, lean_object* v_n_63_, lean_object* v_J_64_, lean_object* v_X_65_, lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramE(v_F_56_, v_E_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_00_u03c3_61_, v_M_62_, v_n_63_, v_J_64_, v_X_65_, v_a_66_, v_b_67_);
lean_dec(v_n_63_);
lean_dec_ref(v_inst_60_);
lean_dec_ref(v_inst_58_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_00_u03c3_75_){
_start:
{
lean_object* v___x_76_; lean_object* v_toCommSemiring_77_; lean_object* v_toSemiring_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_toSemiring_81_; lean_object* v___f_82_; lean_object* v___x_83_; 
v___x_76_ = lp_mathlib_Field_toSemifield___redArg(v_inst_70_);
v_toCommSemiring_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_toCommSemiring_77_);
lean_dec_ref(v___x_76_);
v_toSemiring_78_ = lean_ctor_get(v_inst_73_, 0);
lean_inc_ref(v_toSemiring_78_);
lean_dec_ref(v_inst_73_);
v___x_79_ = lp_mathlib_Field_toSemifield___redArg(v_inst_71_);
v___x_80_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_79_);
v_toSemiring_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc_ref_n(v_toSemiring_81_, 2);
lean_dec_ref(v___x_80_);
v___f_82_ = ((lean_object*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg___closed__0));
lean_inc_ref(v_inst_72_);
v___x_83_ = lp_mathlib_Algebra_TensorProduct_map___redArg(v_toCommSemiring_77_, v_toSemiring_81_, v_inst_72_, v_toSemiring_78_, v_inst_74_, v_toSemiring_81_, v_inst_72_, v___f_82_, v_00_u03c3_75_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg___boxed(lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_00_u03c3_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg(v_inst_84_, v_inst_85_, v_inst_86_, v_inst_87_, v_inst_88_, v_00_u03c3_89_);
lean_dec_ref(v_inst_85_);
lean_dec_ref(v_inst_84_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR(lean_object* v_F_91_, lean_object* v_E_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_R_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_00_u03c3_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg(v_inst_93_, v_inst_94_, v_inst_95_, v_inst_97_, v_inst_98_, v_00_u03c3_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___boxed(lean_object* v_F_101_, lean_object* v_E_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_R_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_00_u03c3_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR(v_F_101_, v_E_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_R_106_, v_inst_107_, v_inst_108_, v_00_u03c3_109_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v___x_116_; lean_object* v_toCommSemiring_117_; lean_object* v_toSemiring_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_toSemiring_121_; lean_object* v___x_122_; 
v___x_116_ = lp_mathlib_Field_toSemifield___redArg(v_inst_111_);
v_toCommSemiring_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc_ref(v_toCommSemiring_117_);
lean_dec_ref(v___x_116_);
v_toSemiring_118_ = lean_ctor_get(v_inst_114_, 0);
lean_inc_ref(v_toSemiring_118_);
lean_dec_ref(v_inst_114_);
v___x_119_ = lp_mathlib_Field_toSemifield___redArg(v_inst_112_);
v___x_120_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_119_);
v_toSemiring_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc_ref(v_toSemiring_121_);
lean_dec_ref(v___x_120_);
v___x_122_ = lp_mathlib_Algebra_TensorProduct_includeRight___redArg(v_toCommSemiring_117_, v_toSemiring_118_, v_inst_115_, v_toSemiring_121_, v_inst_113_);
lean_dec_ref(v_toSemiring_121_);
lean_dec_ref(v_toCommSemiring_117_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg___boxed(lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg(v_inst_123_, v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_125_);
lean_dec_ref(v_inst_124_);
lean_dec_ref(v_inst_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR(lean_object* v_F_129_, lean_object* v_E_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_R_134_, lean_object* v_inst_135_, lean_object* v_inst_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg(v_inst_131_, v_inst_132_, v_inst_133_, v_inst_135_, v_inst_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___boxed(lean_object* v_F_138_, lean_object* v_E_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_R_143_, lean_object* v_inst_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR(v_F_138_, v_E_139_, v_inst_140_, v_inst_141_, v_inst_142_, v_R_143_, v_inst_144_, v_inst_145_);
lean_dec_ref(v_inst_145_);
lean_dec_ref(v_inst_142_);
lean_dec_ref(v_inst_141_);
lean_dec_ref(v_inst_140_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_53__overap_153_; lean_object* v___x_154_; 
v___x_53__overap_153_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg(v_inst_147_, v_inst_148_, v_inst_149_, v_inst_150_, v_inst_151_);
v___x_154_ = lean_apply_1(v___x_53__overap_153_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0___boxed(lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0(v_inst_155_, v_inst_156_, v_inst_157_, v_inst_158_, v_inst_159_, v___y_160_);
lean_dec_ref(v_inst_159_);
lean_dec_ref(v_inst_157_);
lean_dec_ref(v_inst_156_);
lean_dec_ref(v_inst_155_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_J_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___x_171_; 
v___f_170_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_170_, 0, v_inst_162_);
lean_closure_set(v___f_170_, 1, v_inst_163_);
lean_closure_set(v___f_170_, 2, v_inst_164_);
lean_closure_set(v___f_170_, 3, v_inst_165_);
lean_closure_set(v___f_170_, 4, v_inst_166_);
v___x_171_ = lp_mathlib_Matrix_map___redArg(v_J_167_, v___f_170_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR(lean_object* v_F_172_, lean_object* v_E_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_R_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_M_180_, lean_object* v_J_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg(v_inst_174_, v_inst_175_, v_inst_176_, v_inst_178_, v_inst_179_, v_J_181_, v_a_182_, v_a_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___boxed(lean_object* v_F_185_, lean_object* v_E_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_R_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_M_193_, lean_object* v_J_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR(v_F_185_, v_E_186_, v_inst_187_, v_inst_188_, v_inst_189_, v_R_190_, v_inst_191_, v_inst_192_, v_M_193_, v_J_194_, v_a_195_, v_a_196_);
lean_dec(v_M_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HR(lean_object* v_F_198_, lean_object* v_E_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_R_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_00_u03c3_206_, lean_object* v_M_207_, lean_object* v_J_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HR___boxed(lean_object* v_F_210_, lean_object* v_E_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_R_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_00_u03c3_218_, lean_object* v_M_219_, lean_object* v_J_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HR(v_F_210_, v_E_211_, v_inst_212_, v_inst_213_, v_inst_214_, v_R_215_, v_inst_216_, v_inst_217_, v_00_u03c3_218_, v_M_219_, v_J_220_);
lean_dec(v_J_220_);
lean_dec(v_M_219_);
lean_dec(v_00_u03c3_218_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_inst_216_);
lean_dec_ref(v_inst_214_);
lean_dec_ref(v_inst_213_);
lean_dec_ref(v_inst_212_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFin(lean_object* v_F_222_, lean_object* v_E_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_R_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_00_u03c3_230_, lean_object* v_M_231_, lean_object* v_J_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFin___boxed(lean_object* v_F_234_, lean_object* v_E_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_R_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_00_u03c3_242_, lean_object* v_M_243_, lean_object* v_J_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFin(v_F_234_, v_E_235_, v_inst_236_, v_inst_237_, v_inst_238_, v_R_239_, v_inst_240_, v_inst_241_, v_00_u03c3_242_, v_M_243_, v_J_244_);
lean_dec(v_J_244_);
lean_dec(v_M_243_);
lean_dec(v_00_u03c3_242_);
lean_dec_ref(v_inst_241_);
lean_dec_ref(v_inst_240_);
lean_dec_ref(v_inst_238_);
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFinIn(lean_object* v_F_246_, lean_object* v_E_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_R_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_00_u03c3_254_, lean_object* v_M_255_, lean_object* v_J_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFinIn___boxed(lean_object* v_F_258_, lean_object* v_E_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_R_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_00_u03c3_266_, lean_object* v_M_267_, lean_object* v_J_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HFinIn(v_F_258_, v_E_259_, v_inst_260_, v_inst_261_, v_inst_262_, v_R_263_, v_inst_264_, v_inst_265_, v_00_u03c3_266_, v_M_267_, v_J_268_);
lean_dec(v_J_268_);
lean_dec(v_M_267_);
lean_dec(v_00_u03c3_266_);
lean_dec_ref(v_inst_265_);
lean_dec_ref(v_inst_264_);
lean_dec_ref(v_inst_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_260_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hR___redArg(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_00_u03c3_275_, lean_object* v_M_276_, lean_object* v_J_277_, lean_object* v_x_278_, lean_object* v_y_279_){
_start:
{
lean_object* v___x_280_; lean_object* v_toCommSemiring_281_; lean_object* v___x_282_; lean_object* v_toCommSemiring_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_280_ = lp_mathlib_Field_toSemifield___redArg(v_inst_270_);
v_toCommSemiring_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_toCommSemiring_281_);
lean_dec_ref(v___x_280_);
v___x_282_ = lp_mathlib_Field_toSemifield___redArg(v_inst_271_);
v_toCommSemiring_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_toCommSemiring_283_);
lean_dec_ref(v___x_282_);
lean_inc_ref_n(v_inst_272_, 2);
lean_inc_ref_n(v_inst_274_, 2);
lean_inc_ref_n(v_inst_273_, 2);
v___x_284_ = lp_mathlib_Algebra_TensorProduct_instRing___redArg(v_toCommSemiring_281_, v_inst_273_, v_inst_274_, v_toCommSemiring_283_, v_inst_272_);
lean_inc(v_M_276_);
v___x_285_ = l_List_finRange(v_M_276_);
v___x_286_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_sigR___redArg(v_inst_270_, v_inst_271_, v_inst_272_, v_inst_273_, v_inst_274_, v_00_u03c3_275_);
v___x_287_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___boxed), 12, 10);
lean_closure_set(v___x_287_, 0, lean_box(0));
lean_closure_set(v___x_287_, 1, lean_box(0));
lean_closure_set(v___x_287_, 2, v_inst_270_);
lean_closure_set(v___x_287_, 3, v_inst_271_);
lean_closure_set(v___x_287_, 4, v_inst_272_);
lean_closure_set(v___x_287_, 5, lean_box(0));
lean_closure_set(v___x_287_, 6, v_inst_273_);
lean_closure_set(v___x_287_, 7, v_inst_274_);
lean_closure_set(v___x_287_, 8, v_M_276_);
lean_closure_set(v___x_287_, 9, v_J_277_);
v___x_288_ = lp_tree_Formalism_UG_hform___redArg(v___x_284_, v___x_285_, v___x_286_, v___x_287_, v_x_278_, v_y_279_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hR(lean_object* v_F_289_, lean_object* v_E_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_R_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_00_u03c3_297_, lean_object* v_M_298_, lean_object* v_J_299_, lean_object* v_x_300_, lean_object* v_y_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hR___redArg(v_inst_291_, v_inst_292_, v_inst_293_, v_inst_295_, v_inst_296_, v_00_u03c3_297_, v_M_298_, v_J_299_, v_x_300_, v_y_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR___redArg(lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_00_u03c3_308_, lean_object* v_M_309_, lean_object* v_J_310_, lean_object* v_X_311_, lean_object* v_a_312_, lean_object* v_b_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_inc(v_X_311_);
v___x_314_ = lean_apply_1(v_X_311_, v_a_312_);
v___x_315_ = lean_apply_1(v_X_311_, v_b_313_);
v___x_316_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hR___redArg(v_inst_303_, v_inst_304_, v_inst_305_, v_inst_306_, v_inst_307_, v_00_u03c3_308_, v_M_309_, v_J_310_, v___x_314_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR(lean_object* v_F_317_, lean_object* v_E_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_R_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_00_u03c3_325_, lean_object* v_M_326_, lean_object* v_n_327_, lean_object* v_J_328_, lean_object* v_X_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR___redArg(v_inst_319_, v_inst_320_, v_inst_321_, v_inst_323_, v_inst_324_, v_00_u03c3_325_, v_M_326_, v_J_328_, v_X_329_, v_a_330_, v_b_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR___boxed(lean_object* v_F_333_, lean_object* v_E_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_R_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_00_u03c3_341_, lean_object* v_M_342_, lean_object* v_n_343_, lean_object* v_J_344_, lean_object* v_X_345_, lean_object* v_a_346_, lean_object* v_b_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_gramR(v_F_333_, v_E_334_, v_inst_335_, v_inst_336_, v_inst_337_, v_R_338_, v_inst_339_, v_inst_340_, v_00_u03c3_341_, v_M_342_, v_n_343_, v_J_344_, v_X_345_, v_a_346_, v_b_347_);
lean_dec(v_n_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HermR(lean_object* v_F_349_, lean_object* v_E_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_R_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_00_u03c3_357_, lean_object* v_n_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_box(0);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HermR___boxed(lean_object* v_F_360_, lean_object* v_E_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_inst_364_, lean_object* v_R_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_00_u03c3_368_, lean_object* v_n_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HermR(v_F_360_, v_E_361_, v_inst_362_, v_inst_363_, v_inst_364_, v_R_365_, v_inst_366_, v_inst_367_, v_00_u03c3_368_, v_n_369_);
lean_dec(v_n_369_);
lean_dec(v_00_u03c3_368_);
lean_dec_ref(v_inst_367_);
lean_dec_ref(v_inst_366_);
lean_dec_ref(v_inst_364_);
lean_dec_ref(v_inst_363_);
lean_dec_ref(v_inst_362_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_X_376_, lean_object* v_a_377_, lean_object* v_i_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_34__overap_380_; lean_object* v___x_381_; 
v___x_379_ = lean_apply_2(v_X_376_, v_a_377_, v_i_378_);
v___x_34__overap_380_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_inclR___redArg(v_inst_371_, v_inst_372_, v_inst_373_, v_inst_374_, v_inst_375_);
v___x_381_ = lean_apply_1(v___x_34__overap_380_, v___x_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___redArg___boxed(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_X_387_, lean_object* v_a_388_, lean_object* v_i_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___redArg(v_inst_382_, v_inst_383_, v_inst_384_, v_inst_385_, v_inst_386_, v_X_387_, v_a_388_, v_i_389_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_384_);
lean_dec_ref(v_inst_383_);
lean_dec_ref(v_inst_382_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup(lean_object* v_F_391_, lean_object* v_E_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_R_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_M_399_, lean_object* v_n_400_, lean_object* v_X_401_, lean_object* v_a_402_, lean_object* v_i_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___redArg(v_inst_393_, v_inst_394_, v_inst_395_, v_inst_397_, v_inst_398_, v_X_401_, v_a_402_, v_i_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup___boxed(lean_object* v_F_405_, lean_object* v_E_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_R_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_M_413_, lean_object* v_n_414_, lean_object* v_X_415_, lean_object* v_a_416_, lean_object* v_i_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_ratTup(v_F_405_, v_E_406_, v_inst_407_, v_inst_408_, v_inst_409_, v_R_410_, v_inst_411_, v_inst_412_, v_M_413_, v_n_414_, v_X_415_, v_a_416_, v_i_417_);
lean_dec(v_n_414_);
lean_dec(v_M_413_);
lean_dec_ref(v_inst_412_);
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_407_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg(lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_M_424_, lean_object* v_g_425_, lean_object* v_X_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; lean_object* v_toCommSemiring_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_toSMul_433_; lean_object* v_toCommRing_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_toSMul_437_; lean_object* v___x_438_; lean_object* v_val_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_429_ = lp_mathlib_Field_toSemifield___redArg(v_inst_419_);
v_toCommSemiring_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_toCommSemiring_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_422_);
v___x_432_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_431_);
v_toSMul_433_ = lean_ctor_get(v_inst_423_, 0);
lean_inc(v_toSMul_433_);
lean_dec_ref(v_inst_423_);
v_toCommRing_434_ = lean_ctor_get(v_inst_420_, 0);
v___x_435_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_434_);
v___x_436_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_435_);
v_toSMul_437_ = lean_ctor_get(v_inst_421_, 0);
lean_inc(v_toSMul_437_);
lean_dec_ref(v_inst_421_);
v___x_438_ = lp_mathlib_Algebra_TensorProduct_instNonUnitalNonAssocSemiring___redArg(v_toCommSemiring_430_, v___x_432_, v_toSMul_433_, v___x_436_, v_toSMul_437_);
v_val_439_ = lean_ctor_get(v_g_425_, 0);
lean_inc(v_val_439_);
lean_dec_ref(v_g_425_);
v___x_440_ = l_List_finRange(v_M_424_);
v___x_441_ = lean_apply_1(v_X_426_, v_a_427_);
v___x_442_ = lp_mathlib_Matrix_mulVec___redArg(v___x_438_, v___x_440_, v_val_439_, v___x_441_, v_a_428_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg___boxed(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_M_448_, lean_object* v_g_449_, lean_object* v_X_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg(v_inst_443_, v_inst_444_, v_inst_445_, v_inst_446_, v_inst_447_, v_M_448_, v_g_449_, v_X_450_, v_a_451_, v_a_452_);
lean_dec_ref(v_inst_446_);
lean_dec_ref(v_inst_444_);
lean_dec_ref(v_inst_443_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup(lean_object* v_F_454_, lean_object* v_E_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_R_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_M_462_, lean_object* v_n_463_, lean_object* v_g_464_, lean_object* v_X_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg(v_inst_456_, v_inst_457_, v_inst_458_, v_inst_460_, v_inst_461_, v_M_462_, v_g_464_, v_X_465_, v_a_466_, v_a_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___boxed(lean_object* v_F_469_, lean_object* v_E_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_R_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_M_477_, lean_object* v_n_478_, lean_object* v_g_479_, lean_object* v_X_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup(v_F_469_, v_E_470_, v_inst_471_, v_inst_472_, v_inst_473_, v_R_474_, v_inst_475_, v_inst_476_, v_M_477_, v_n_478_, v_g_479_, v_X_480_, v_a_481_, v_a_482_);
lean_dec(v_n_478_);
lean_dec_ref(v_inst_475_);
lean_dec_ref(v_inst_472_);
lean_dec_ref(v_inst_471_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_topTens(lean_object* v_F_484_, lean_object* v_E_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_R_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(0);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_topTens___boxed(lean_object* v_F_494_, lean_object* v_E_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_R_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_topTens(v_F_494_, v_E_495_, v_inst_496_, v_inst_497_, v_inst_498_, v_R_499_, v_inst_500_, v_inst_501_, v_inst_502_);
lean_dec_ref(v_inst_501_);
lean_dec_ref(v_inst_500_);
lean_dec_ref(v_inst_498_);
lean_dec_ref(v_inst_497_);
lean_dec_ref(v_inst_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measTens(lean_object* v_F_504_, lean_object* v_E_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_R_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measTens___boxed(lean_object* v_F_514_, lean_object* v_E_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_R_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measTens(v_F_514_, v_E_515_, v_inst_516_, v_inst_517_, v_inst_518_, v_R_519_, v_inst_520_, v_inst_521_, v_inst_522_);
lean_dec_ref(v_inst_521_);
lean_dec_ref(v_inst_520_);
lean_dec_ref(v_inst_518_);
lean_dec_ref(v_inst_517_);
lean_dec_ref(v_inst_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__0(lean_object* v_inv_524_, lean_object* v___y_525_, lean_object* v_j_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_apply_2(v_inv_524_, v_j_526_, v___y_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__1(lean_object* v_inv_528_, lean_object* v___y_529_, lean_object* v_j_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_apply_2(v_inv_528_, v___y_529_, v_j_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2(lean_object* v_inv_532_, lean_object* v_inv_533_, lean_object* v___x_534_, lean_object* v_toMul_535_, lean_object* v_toAddCommMonoid_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___f_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v___f_539_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_539_, 0, v_inv_532_);
lean_closure_set(v___f_539_, 1, v___y_538_);
v___f_540_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__1), 3, 2);
lean_closure_set(v___f_540_, 0, v_inv_533_);
lean_closure_set(v___f_540_, 1, v___y_537_);
v___x_541_ = lp_mathlib_dotProduct___redArg(v___x_534_, v_toMul_535_, v_toAddCommMonoid_536_, v___f_540_, v___f_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2___boxed(lean_object* v_inv_542_, lean_object* v_inv_543_, lean_object* v___x_544_, lean_object* v_toMul_545_, lean_object* v_toAddCommMonoid_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2(v_inv_542_, v_inv_543_, v___x_544_, v_toMul_545_, v_toAddCommMonoid_546_, v___y_547_, v___y_548_);
lean_dec_ref(v_toAddCommMonoid_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__3(lean_object* v_val_550_, lean_object* v___y_551_, lean_object* v_j_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_apply_2(v_val_550_, v_j_552_, v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__4(lean_object* v_val_554_, lean_object* v___y_555_, lean_object* v_j_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_apply_2(v_val_554_, v___y_555_, v_j_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5(lean_object* v_val_558_, lean_object* v_val_559_, lean_object* v___x_560_, lean_object* v_toMul_561_, lean_object* v_toAddCommMonoid_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_567_; 
v___f_565_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__3), 3, 2);
lean_closure_set(v___f_565_, 0, v_val_558_);
lean_closure_set(v___f_565_, 1, v___y_564_);
v___f_566_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__4), 3, 2);
lean_closure_set(v___f_566_, 0, v_val_559_);
lean_closure_set(v___f_566_, 1, v___y_563_);
v___x_567_ = lp_mathlib_dotProduct___redArg(v___x_560_, v_toMul_561_, v_toAddCommMonoid_562_, v___f_566_, v___f_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5___boxed(lean_object* v_val_568_, lean_object* v_val_569_, lean_object* v___x_570_, lean_object* v_toMul_571_, lean_object* v_toAddCommMonoid_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5(v_val_568_, v_val_569_, v___x_570_, v_toMul_571_, v_toAddCommMonoid_572_, v___y_573_, v___y_574_);
lean_dec_ref(v_toAddCommMonoid_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg(lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_M_581_, lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v___x_584_; lean_object* v_toCommSemiring_585_; lean_object* v_toSemiring_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_toSemiring_589_; lean_object* v___x_590_; lean_object* v_val_591_; lean_object* v_inv_592_; lean_object* v_val_593_; lean_object* v_inv_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_608_; 
v___x_584_ = lp_mathlib_Field_toSemifield___redArg(v_inst_576_);
v_toCommSemiring_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc_ref(v_toCommSemiring_585_);
lean_dec_ref(v___x_584_);
v_toSemiring_586_ = lean_ctor_get(v_inst_579_, 0);
lean_inc_ref(v_toSemiring_586_);
lean_dec_ref(v_inst_579_);
v___x_587_ = lp_mathlib_Field_toSemifield___redArg(v_inst_577_);
v___x_588_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_587_);
v_toSemiring_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_toSemiring_589_);
lean_dec_ref(v___x_588_);
v___x_590_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_585_, v_toSemiring_586_, v_inst_580_, v_toSemiring_589_, v_inst_578_);
v_val_591_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_val_591_);
v_inv_592_ = lean_ctor_get(v_a_582_, 1);
lean_inc(v_inv_592_);
lean_dec_ref(v_a_582_);
v_val_593_ = lean_ctor_get(v_b_583_, 0);
v_inv_594_ = lean_ctor_get(v_b_583_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_b_583_);
if (v_isSharedCheck_608_ == 0)
{
v___x_596_ = v_b_583_;
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_inv_594_);
lean_inc(v_val_593_);
lean_dec(v_b_583_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v_toAddCommMonoid_599_; lean_object* v___x_600_; lean_object* v_toMul_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_606_; 
v___x_598_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_590_);
lean_dec_ref(v___x_590_);
v_toAddCommMonoid_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref_n(v_toAddCommMonoid_599_, 2);
v___x_600_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_598_);
v_toMul_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc_n(v_toMul_601_, 2);
lean_dec_ref(v___x_600_);
v___x_602_ = l_List_finRange(v_M_581_);
lean_inc(v___x_602_);
v___f_603_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_603_, 0, v_inv_592_);
lean_closure_set(v___f_603_, 1, v_inv_594_);
lean_closure_set(v___f_603_, 2, v___x_602_);
lean_closure_set(v___f_603_, 3, v_toMul_601_);
lean_closure_set(v___f_603_, 4, v_toAddCommMonoid_599_);
v___f_604_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_604_, 0, v_val_593_);
lean_closure_set(v___f_604_, 1, v_val_591_);
lean_closure_set(v___f_604_, 2, v___x_602_);
lean_closure_set(v___f_604_, 3, v_toMul_601_);
lean_closure_set(v___f_604_, 4, v_toAddCommMonoid_599_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___f_603_);
lean_ctor_set(v___x_596_, 0, v___f_604_);
v___x_606_ = v___x_596_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___f_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___f_603_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___boxed(lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_M_614_, lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg(v_inst_609_, v_inst_610_, v_inst_611_, v_inst_612_, v_inst_613_, v_M_614_, v_a_615_, v_b_616_);
lean_dec_ref(v_inst_610_);
lean_dec_ref(v_inst_609_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1(lean_object* v_F_618_, lean_object* v_E_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_R_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_00_u03c3_626_, lean_object* v_M_627_, lean_object* v_J_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v___x_631_; lean_object* v_toCommSemiring_632_; lean_object* v_toSemiring_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_toSemiring_636_; lean_object* v___x_637_; lean_object* v_val_638_; lean_object* v_inv_639_; lean_object* v_val_640_; lean_object* v_inv_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_655_; 
v___x_631_ = lp_mathlib_Field_toSemifield___redArg(v_inst_620_);
v_toCommSemiring_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_toCommSemiring_632_);
lean_dec_ref(v___x_631_);
v_toSemiring_633_ = lean_ctor_get(v_inst_624_, 0);
lean_inc_ref(v_toSemiring_633_);
lean_dec_ref(v_inst_624_);
v___x_634_ = lp_mathlib_Field_toSemifield___redArg(v_inst_621_);
v___x_635_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_634_);
v_toSemiring_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_toSemiring_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_632_, v_toSemiring_633_, v_inst_625_, v_toSemiring_636_, v_inst_622_);
v_val_638_ = lean_ctor_get(v_a_629_, 0);
lean_inc(v_val_638_);
v_inv_639_ = lean_ctor_get(v_a_629_, 1);
lean_inc(v_inv_639_);
lean_dec_ref(v_a_629_);
v_val_640_ = lean_ctor_get(v_b_630_, 0);
v_inv_641_ = lean_ctor_get(v_b_630_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_b_630_);
if (v_isSharedCheck_655_ == 0)
{
v___x_643_ = v_b_630_;
v_isShared_644_ = v_isSharedCheck_655_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_inv_641_);
lean_inc(v_val_640_);
lean_dec(v_b_630_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_655_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v_toAddCommMonoid_646_; lean_object* v___x_647_; lean_object* v_toMul_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___x_653_; 
v___x_645_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_637_);
lean_dec_ref(v___x_637_);
v_toAddCommMonoid_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref_n(v_toAddCommMonoid_646_, 2);
v___x_647_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_645_);
v_toMul_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_n(v_toMul_648_, 2);
lean_dec_ref(v___x_647_);
v___x_649_ = l_List_finRange(v_M_627_);
lean_inc(v___x_649_);
v___f_650_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_650_, 0, v_inv_639_);
lean_closure_set(v___f_650_, 1, v_inv_641_);
lean_closure_set(v___f_650_, 2, v___x_649_);
lean_closure_set(v___f_650_, 3, v_toMul_648_);
lean_closure_set(v___f_650_, 4, v_toAddCommMonoid_646_);
v___f_651_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_651_, 0, v_val_640_);
lean_closure_set(v___f_651_, 1, v_val_638_);
lean_closure_set(v___f_651_, 2, v___x_649_);
lean_closure_set(v___f_651_, 3, v_toMul_648_);
lean_closure_set(v___f_651_, 4, v_toAddCommMonoid_646_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___f_650_);
lean_ctor_set(v___x_643_, 0, v___f_651_);
v___x_653_ = v___x_643_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___f_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___f_650_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___boxed(lean_object* v_F_656_, lean_object* v_E_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_R_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_00_u03c3_664_, lean_object* v_M_665_, lean_object* v_J_666_, lean_object* v_a_667_, lean_object* v_b_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1(v_F_656_, v_E_657_, v_inst_658_, v_inst_659_, v_inst_660_, v_R_661_, v_inst_662_, v_inst_663_, v_00_u03c3_664_, v_M_665_, v_J_666_, v_a_667_, v_b_668_);
lean_dec(v_J_666_);
lean_dec(v_00_u03c3_664_);
lean_dec_ref(v_inst_659_);
lean_dec_ref(v_inst_658_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0(lean_object* v_toSemiring_670_, lean_object* v_toSemiring_671_, lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_toOne_677_; lean_object* v_toOne_678_; lean_object* v___x_679_; 
v___x_673_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_670_);
v___x_674_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_671_);
v___x_675_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_673_);
v___x_676_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_674_);
v_toOne_677_ = lean_ctor_get(v___x_675_, 2);
lean_inc(v_toOne_677_);
lean_dec_ref(v___x_675_);
v_toOne_678_ = lean_ctor_get(v___x_676_, 2);
lean_inc(v_toOne_678_);
lean_dec_ref(v___x_676_);
v___x_679_ = lp_mathlib_TensorProduct_tmul___redArg(v_toOne_677_, v_toOne_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0___boxed(lean_object* v_toSemiring_680_, lean_object* v_toSemiring_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0(v_toSemiring_680_, v_toSemiring_681_, v_x_682_);
lean_dec(v_x_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg(lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_M_689_){
_start:
{
lean_object* v___x_690_; lean_object* v_toCommSemiring_691_; lean_object* v_toSemiring_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_toSemiring_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_toAddMonoid_699_; lean_object* v___x_700_; lean_object* v_toZero_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v___x_690_ = lp_mathlib_Field_toSemifield___redArg(v_inst_684_);
v_toCommSemiring_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_toCommSemiring_691_);
lean_dec_ref(v___x_690_);
v_toSemiring_692_ = lean_ctor_get(v_inst_687_, 0);
lean_inc_ref_n(v_toSemiring_692_, 2);
lean_dec_ref(v_inst_687_);
v___x_693_ = lp_mathlib_Field_toSemifield___redArg(v_inst_685_);
v___x_694_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_693_);
v_toSemiring_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc_ref_n(v_toSemiring_695_, 2);
lean_dec_ref(v___x_694_);
v___x_696_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_691_, v_toSemiring_692_, v_inst_688_, v_toSemiring_695_, v_inst_686_);
v___x_697_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_696_);
v___x_698_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_697_);
v_toAddMonoid_699_ = lean_ctor_get(v___x_698_, 1);
lean_inc_ref(v_toAddMonoid_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_699_);
lean_dec_ref(v_toAddMonoid_699_);
v_toZero_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v___x_700_, 1);
lean_dec(v_unused_712_);
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_toZero_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___f_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___f_705_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_705_, 0, v_toSemiring_692_);
lean_closure_set(v___f_705_, 1, v_toSemiring_695_);
v___x_706_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_706_, 0, v_M_689_);
v___x_707_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_707_, 0, lean_box(0));
lean_closure_set(v___x_707_, 1, lean_box(0));
lean_closure_set(v___x_707_, 2, v___x_706_);
lean_closure_set(v___x_707_, 3, v_toZero_701_);
lean_closure_set(v___x_707_, 4, v___f_705_);
lean_inc_ref(v___x_707_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_707_);
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___boxed(lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_M_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg(v_inst_713_, v_inst_714_, v_inst_715_, v_inst_716_, v_inst_717_, v_M_718_);
lean_dec_ref(v_inst_714_);
lean_dec_ref(v_inst_713_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4(lean_object* v_F_720_, lean_object* v_E_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_R_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_00_u03c3_728_, lean_object* v_M_729_, lean_object* v_J_730_){
_start:
{
lean_object* v___x_731_; lean_object* v_toCommSemiring_732_; lean_object* v_toSemiring_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_toSemiring_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_toAddMonoid_740_; lean_object* v___x_741_; lean_object* v_toZero_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_752_; 
v___x_731_ = lp_mathlib_Field_toSemifield___redArg(v_inst_722_);
v_toCommSemiring_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_toCommSemiring_732_);
lean_dec_ref(v___x_731_);
v_toSemiring_733_ = lean_ctor_get(v_inst_726_, 0);
lean_inc_ref_n(v_toSemiring_733_, 2);
lean_dec_ref(v_inst_726_);
v___x_734_ = lp_mathlib_Field_toSemifield___redArg(v_inst_723_);
v___x_735_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_734_);
v_toSemiring_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc_ref_n(v_toSemiring_736_, 2);
lean_dec_ref(v___x_735_);
v___x_737_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_732_, v_toSemiring_733_, v_inst_727_, v_toSemiring_736_, v_inst_724_);
v___x_738_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_737_);
v___x_739_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_738_);
v_toAddMonoid_740_ = lean_ctor_get(v___x_739_, 1);
lean_inc_ref(v_toAddMonoid_740_);
lean_dec_ref(v___x_739_);
v___x_741_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_740_);
lean_dec_ref(v_toAddMonoid_740_);
v_toZero_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_741_, 1);
lean_dec(v_unused_753_);
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_toZero_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_752_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___f_746_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_746_, 0, v_toSemiring_733_);
lean_closure_set(v___f_746_, 1, v_toSemiring_736_);
v___x_747_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_747_, 0, v_M_729_);
v___x_748_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_748_, 0, lean_box(0));
lean_closure_set(v___x_748_, 1, lean_box(0));
lean_closure_set(v___x_748_, 2, v___x_747_);
lean_closure_set(v___x_748_, 3, v_toZero_742_);
lean_closure_set(v___x_748_, 4, v___f_746_);
lean_inc_ref(v___x_748_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_748_);
lean_ctor_set(v___x_744_, 0, v___x_748_);
v___x_750_ = v___x_744_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___boxed(lean_object* v_F_754_, lean_object* v_E_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_R_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_00_u03c3_762_, lean_object* v_M_763_, lean_object* v_J_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4(v_F_754_, v_E_755_, v_inst_756_, v_inst_757_, v_inst_758_, v_R_759_, v_inst_760_, v_inst_761_, v_00_u03c3_762_, v_M_763_, v_J_764_);
lean_dec(v_J_764_);
lean_dec(v_00_u03c3_762_);
lean_dec_ref(v_inst_757_);
lean_dec_ref(v_inst_756_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___redArg(lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_M_771_, lean_object* v_n_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; lean_object* v_toCommSemiring_775_; lean_object* v_toSemiring_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_toSemiring_779_; lean_object* v___x_780_; lean_object* v_val_781_; lean_object* v_inv_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_799_; 
v___x_774_ = lp_mathlib_Field_toSemifield___redArg(v_inst_766_);
v_toCommSemiring_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_ref(v_toCommSemiring_775_);
lean_dec_ref(v___x_774_);
v_toSemiring_776_ = lean_ctor_get(v_inst_769_, 0);
lean_inc_ref(v_toSemiring_776_);
lean_dec_ref(v_inst_769_);
v___x_777_ = lp_mathlib_Field_toSemifield___redArg(v_inst_767_);
v___x_778_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_777_);
v_toSemiring_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc_ref(v_toSemiring_779_);
lean_dec_ref(v___x_778_);
v___x_780_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_775_, v_toSemiring_776_, v_inst_770_, v_toSemiring_779_, v_inst_768_);
v_val_781_ = lean_ctor_get(v_x_773_, 0);
v_inv_782_ = lean_ctor_get(v_x_773_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_799_ == 0)
{
v___x_784_ = v_x_773_;
v_isShared_785_ = v_isSharedCheck_799_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_inv_782_);
lean_inc(v_val_781_);
lean_dec(v_x_773_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_799_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_toMul_792_; lean_object* v_toOne_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc(v_M_771_);
v___x_786_ = l_List_finRange(v_M_771_);
v___x_787_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_787_, 0, v_M_771_);
v___x_788_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_780_);
lean_inc(v___x_786_);
v___x_789_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_788_, v___x_786_);
v___x_790_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_780_);
v___x_791_ = lp_mathlib_Matrix_nonAssocSemiring___redArg(v___x_790_, v___x_786_, v___x_787_);
v_toMul_792_ = lean_ctor_get(v___x_789_, 1);
lean_inc_n(v_toMul_792_, 2);
lean_dec_ref(v___x_789_);
v_toOne_793_ = lean_ctor_get(v___x_791_, 1);
lean_inc_n(v_toOne_793_, 2);
lean_dec_ref(v___x_791_);
v___x_794_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_792_, v_n_772_, v_toOne_793_, v_val_781_);
v___x_795_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_792_, v_n_772_, v_toOne_793_, v_inv_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_795_);
lean_ctor_set(v___x_784_, 0, v___x_794_);
v___x_797_ = v___x_784_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___redArg___boxed(lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_M_805_, lean_object* v_n_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___redArg(v_inst_800_, v_inst_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_M_805_, v_n_806_, v_x_807_);
lean_dec(v_n_806_);
lean_dec_ref(v_inst_801_);
lean_dec_ref(v_inst_800_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8(lean_object* v_F_809_, lean_object* v_E_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_R_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_00_u03c3_817_, lean_object* v_M_818_, lean_object* v_J_819_, lean_object* v_n_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; lean_object* v_toCommSemiring_823_; lean_object* v_toSemiring_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_toSemiring_827_; lean_object* v___x_828_; lean_object* v_val_829_; lean_object* v_inv_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_847_; 
v___x_822_ = lp_mathlib_Field_toSemifield___redArg(v_inst_811_);
v_toCommSemiring_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_ref(v_toCommSemiring_823_);
lean_dec_ref(v___x_822_);
v_toSemiring_824_ = lean_ctor_get(v_inst_815_, 0);
lean_inc_ref(v_toSemiring_824_);
lean_dec_ref(v_inst_815_);
v___x_825_ = lp_mathlib_Field_toSemifield___redArg(v_inst_812_);
v___x_826_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_825_);
v_toSemiring_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_ref(v_toSemiring_827_);
lean_dec_ref(v___x_826_);
v___x_828_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_823_, v_toSemiring_824_, v_inst_816_, v_toSemiring_827_, v_inst_813_);
v_val_829_ = lean_ctor_get(v_x_821_, 0);
v_inv_830_ = lean_ctor_get(v_x_821_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_847_ == 0)
{
v___x_832_ = v_x_821_;
v_isShared_833_ = v_isSharedCheck_847_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_inv_830_);
lean_inc(v_val_829_);
lean_dec(v_x_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_847_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_toMul_840_; lean_object* v_toOne_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
lean_inc(v_M_818_);
v___x_834_ = l_List_finRange(v_M_818_);
v___x_835_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_835_, 0, v_M_818_);
v___x_836_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_828_);
lean_inc(v___x_834_);
v___x_837_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_836_, v___x_834_);
v___x_838_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_828_);
v___x_839_ = lp_mathlib_Matrix_nonAssocSemiring___redArg(v___x_838_, v___x_834_, v___x_835_);
v_toMul_840_ = lean_ctor_get(v___x_837_, 1);
lean_inc_n(v_toMul_840_, 2);
lean_dec_ref(v___x_837_);
v_toOne_841_ = lean_ctor_get(v___x_839_, 1);
lean_inc_n(v_toOne_841_, 2);
lean_dec_ref(v___x_839_);
v___x_842_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_840_, v_n_820_, v_toOne_841_, v_val_829_);
v___x_843_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_840_, v_n_820_, v_toOne_841_, v_inv_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_843_);
lean_ctor_set(v___x_832_, 0, v___x_842_);
v___x_845_ = v___x_832_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___boxed(lean_object* v_F_848_, lean_object* v_E_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_R_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_00_u03c3_856_, lean_object* v_M_857_, lean_object* v_J_858_, lean_object* v_n_859_, lean_object* v_x_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8(v_F_848_, v_E_849_, v_inst_850_, v_inst_851_, v_inst_852_, v_R_853_, v_inst_854_, v_inst_855_, v_00_u03c3_856_, v_M_857_, v_J_858_, v_n_859_, v_x_860_);
lean_dec(v_n_859_);
lean_dec(v_J_858_);
lean_dec(v_00_u03c3_856_);
lean_dec_ref(v_inst_851_);
lean_dec_ref(v_inst_850_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12___redArg(lean_object* v_a_862_){
_start:
{
lean_object* v_val_863_; lean_object* v_inv_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_val_863_ = lean_ctor_get(v_a_862_, 0);
v_inv_864_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v_a_862_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_inv_864_);
lean_inc(v_val_863_);
lean_dec(v_a_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_val_863_);
lean_ctor_set(v___x_866_, 0, v_inv_864_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_inv_864_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_val_863_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12(lean_object* v_F_872_, lean_object* v_E_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_R_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_00_u03c3_880_, lean_object* v_M_881_, lean_object* v_J_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_val_884_; lean_object* v_inv_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_val_884_ = lean_ctor_get(v_a_883_, 0);
v_inv_885_ = lean_ctor_get(v_a_883_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_a_883_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v_a_883_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_inv_885_);
lean_inc(v_val_884_);
lean_dec(v_a_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_val_884_);
lean_ctor_set(v___x_887_, 0, v_inv_885_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_inv_885_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_val_884_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12___boxed(lean_object* v_F_893_, lean_object* v_E_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_R_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_00_u03c3_901_, lean_object* v_M_902_, lean_object* v_J_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12(v_F_893_, v_E_894_, v_inst_895_, v_inst_896_, v_inst_897_, v_R_898_, v_inst_899_, v_inst_900_, v_00_u03c3_901_, v_M_902_, v_J_903_, v_a_904_);
lean_dec(v_J_903_);
lean_dec(v_M_902_);
lean_dec(v_00_u03c3_901_);
lean_dec_ref(v_inst_900_);
lean_dec_ref(v_inst_899_);
lean_dec_ref(v_inst_897_);
lean_dec_ref(v_inst_896_);
lean_dec_ref(v_inst_895_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2(lean_object* v_inv_906_, lean_object* v_val_907_, lean_object* v___x_908_, lean_object* v_toMul_909_, lean_object* v_toAddCommMonoid_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___x_915_; 
v___f_913_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_913_, 0, v_inv_906_);
lean_closure_set(v___f_913_, 1, v___y_912_);
v___f_914_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__4), 3, 2);
lean_closure_set(v___f_914_, 0, v_val_907_);
lean_closure_set(v___f_914_, 1, v___y_911_);
v___x_915_ = lp_mathlib_dotProduct___redArg(v___x_908_, v_toMul_909_, v_toAddCommMonoid_910_, v___f_914_, v___f_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2___boxed(lean_object* v_inv_916_, lean_object* v_val_917_, lean_object* v___x_918_, lean_object* v_toMul_919_, lean_object* v_toAddCommMonoid_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2(v_inv_916_, v_val_917_, v___x_918_, v_toMul_919_, v_toAddCommMonoid_920_, v___y_921_, v___y_922_);
lean_dec_ref(v_toAddCommMonoid_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg(lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_M_929_, lean_object* v_a_930_, lean_object* v_b_931_){
_start:
{
lean_object* v___x_932_; lean_object* v_toCommSemiring_933_; lean_object* v_toSemiring_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_toSemiring_937_; lean_object* v___x_938_; lean_object* v_val_939_; lean_object* v_inv_940_; lean_object* v_val_941_; lean_object* v_inv_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_956_; 
v___x_932_ = lp_mathlib_Field_toSemifield___redArg(v_inst_924_);
v_toCommSemiring_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc_ref(v_toCommSemiring_933_);
lean_dec_ref(v___x_932_);
v_toSemiring_934_ = lean_ctor_get(v_inst_927_, 0);
lean_inc_ref(v_toSemiring_934_);
lean_dec_ref(v_inst_927_);
v___x_935_ = lp_mathlib_Field_toSemifield___redArg(v_inst_925_);
v___x_936_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_935_);
v_toSemiring_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_toSemiring_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_933_, v_toSemiring_934_, v_inst_928_, v_toSemiring_937_, v_inst_926_);
v_val_939_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_val_939_);
v_inv_940_ = lean_ctor_get(v_a_930_, 1);
lean_inc(v_inv_940_);
lean_dec_ref(v_a_930_);
v_val_941_ = lean_ctor_get(v_b_931_, 0);
v_inv_942_ = lean_ctor_get(v_b_931_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_b_931_);
if (v_isSharedCheck_956_ == 0)
{
v___x_944_ = v_b_931_;
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_inv_942_);
lean_inc(v_val_941_);
lean_dec(v_b_931_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v_toAddCommMonoid_947_; lean_object* v___x_948_; lean_object* v_toMul_949_; lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_954_; 
v___x_946_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_938_);
lean_dec_ref(v___x_938_);
v_toAddCommMonoid_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc_ref_n(v_toAddCommMonoid_947_, 2);
v___x_948_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_946_);
v_toMul_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_n(v_toMul_949_, 2);
lean_dec_ref(v___x_948_);
v___x_950_ = l_List_finRange(v_M_929_);
lean_inc(v___x_950_);
v___f_951_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_951_, 0, v_inv_940_);
lean_closure_set(v___f_951_, 1, v_val_941_);
lean_closure_set(v___f_951_, 2, v___x_950_);
lean_closure_set(v___f_951_, 3, v_toMul_949_);
lean_closure_set(v___f_951_, 4, v_toAddCommMonoid_947_);
v___f_952_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_952_, 0, v_inv_942_);
lean_closure_set(v___f_952_, 1, v_val_939_);
lean_closure_set(v___f_952_, 2, v___x_950_);
lean_closure_set(v___f_952_, 3, v_toMul_949_);
lean_closure_set(v___f_952_, 4, v_toAddCommMonoid_947_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___f_951_);
lean_ctor_set(v___x_944_, 0, v___f_952_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___f_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___f_951_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___boxed(lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_M_962_, lean_object* v_a_963_, lean_object* v_b_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg(v_inst_957_, v_inst_958_, v_inst_959_, v_inst_960_, v_inst_961_, v_M_962_, v_a_963_, v_b_964_);
lean_dec_ref(v_inst_958_);
lean_dec_ref(v_inst_957_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14(lean_object* v_F_966_, lean_object* v_E_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_R_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_00_u03c3_974_, lean_object* v_M_975_, lean_object* v_J_976_, lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
lean_object* v___x_979_; lean_object* v_toCommSemiring_980_; lean_object* v_toSemiring_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_toSemiring_984_; lean_object* v___x_985_; lean_object* v_val_986_; lean_object* v_inv_987_; lean_object* v_val_988_; lean_object* v_inv_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1003_; 
v___x_979_ = lp_mathlib_Field_toSemifield___redArg(v_inst_968_);
v_toCommSemiring_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc_ref(v_toCommSemiring_980_);
lean_dec_ref(v___x_979_);
v_toSemiring_981_ = lean_ctor_get(v_inst_972_, 0);
lean_inc_ref(v_toSemiring_981_);
lean_dec_ref(v_inst_972_);
v___x_982_ = lp_mathlib_Field_toSemifield___redArg(v_inst_969_);
v___x_983_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_982_);
v_toSemiring_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc_ref(v_toSemiring_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_980_, v_toSemiring_981_, v_inst_973_, v_toSemiring_984_, v_inst_970_);
v_val_986_ = lean_ctor_get(v_a_977_, 0);
lean_inc(v_val_986_);
v_inv_987_ = lean_ctor_get(v_a_977_, 1);
lean_inc(v_inv_987_);
lean_dec_ref(v_a_977_);
v_val_988_ = lean_ctor_get(v_b_978_, 0);
v_inv_989_ = lean_ctor_get(v_b_978_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_b_978_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_991_ = v_b_978_;
v_isShared_992_ = v_isSharedCheck_1003_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_inv_989_);
lean_inc(v_val_988_);
lean_dec(v_b_978_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1003_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v_toAddCommMonoid_994_; lean_object* v___x_995_; lean_object* v_toMul_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_1001_; 
v___x_993_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_985_);
lean_dec_ref(v___x_985_);
v_toAddCommMonoid_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc_ref_n(v_toAddCommMonoid_994_, 2);
v___x_995_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_993_);
v_toMul_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_n(v_toMul_996_, 2);
lean_dec_ref(v___x_995_);
v___x_997_ = l_List_finRange(v_M_975_);
lean_inc(v___x_997_);
v___f_998_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_998_, 0, v_inv_987_);
lean_closure_set(v___f_998_, 1, v_val_988_);
lean_closure_set(v___f_998_, 2, v___x_997_);
lean_closure_set(v___f_998_, 3, v_toMul_996_);
lean_closure_set(v___f_998_, 4, v_toAddCommMonoid_994_);
v___f_999_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_999_, 0, v_inv_989_);
lean_closure_set(v___f_999_, 1, v_val_986_);
lean_closure_set(v___f_999_, 2, v___x_997_);
lean_closure_set(v___f_999_, 3, v_toMul_996_);
lean_closure_set(v___f_999_, 4, v_toAddCommMonoid_994_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___f_998_);
lean_ctor_set(v___x_991_, 0, v___f_999_);
v___x_1001_ = v___x_991_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___f_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___f_998_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___boxed(lean_object* v_F_1004_, lean_object* v_E_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_R_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_00_u03c3_1012_, lean_object* v_M_1013_, lean_object* v_J_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14(v_F_1004_, v_E_1005_, v_inst_1006_, v_inst_1007_, v_inst_1008_, v_R_1009_, v_inst_1010_, v_inst_1011_, v_00_u03c3_1012_, v_M_1013_, v_J_1014_, v_a_1015_, v_b_1016_);
lean_dec(v_J_1014_);
lean_dec(v_00_u03c3_1012_);
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
return v_res_1017_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1018_; lean_object* v_intZero_1019_; 
v_natZero_1018_ = lean_unsigned_to_nat(0u);
v_intZero_1019_ = lean_nat_to_int(v_natZero_1018_);
return v_intZero_1019_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_M_1025_, lean_object* v_n_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v___x_1028_; lean_object* v_toCommSemiring_1029_; lean_object* v_toSemiring_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_toSemiring_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_intZero_1037_; uint8_t v_isNeg_1038_; 
v___x_1028_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1020_);
v_toCommSemiring_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_toCommSemiring_1029_);
lean_dec_ref(v___x_1028_);
v_toSemiring_1030_ = lean_ctor_get(v_inst_1023_, 0);
lean_inc_ref(v_toSemiring_1030_);
lean_dec_ref(v_inst_1023_);
v___x_1031_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1021_);
v___x_1032_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1031_);
v_toSemiring_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_toSemiring_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_1029_, v_toSemiring_1030_, v_inst_1024_, v_toSemiring_1033_, v_inst_1022_);
lean_inc(v_M_1025_);
v___x_1035_ = l_List_finRange(v_M_1025_);
v___x_1036_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1036_, 0, v_M_1025_);
v_intZero_1037_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0);
v_isNeg_1038_ = lean_int_dec_lt(v_n_1026_, v_intZero_1037_);
if (v_isNeg_1038_ == 0)
{
lean_object* v_val_1039_; lean_object* v_inv_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1056_; 
v_val_1039_ = lean_ctor_get(v_x_1027_, 0);
v_inv_1040_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1042_ = v_x_1027_;
v_isShared_1043_ = v_isSharedCheck_1056_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_inv_1040_);
lean_inc(v_val_1039_);
lean_dec(v_x_1027_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1056_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_toMul_1048_; lean_object* v_toOne_1049_; lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1044_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_1034_);
lean_inc(v___x_1035_);
v___x_1045_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_1044_, v___x_1035_);
v___x_1046_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_1034_);
v___x_1047_ = lp_mathlib_Matrix_nonAssocSemiring___redArg(v___x_1046_, v___x_1035_, v___x_1036_);
v_toMul_1048_ = lean_ctor_get(v___x_1045_, 1);
lean_inc_n(v_toMul_1048_, 2);
lean_dec_ref(v___x_1045_);
v_toOne_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc_n(v_toOne_1049_, 2);
lean_dec_ref(v___x_1047_);
v_a_1050_ = lean_nat_abs(v_n_1026_);
v___x_1051_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1048_, v_a_1050_, v_toOne_1049_, v_val_1039_);
v___x_1052_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1048_, v_a_1050_, v_toOne_1049_, v_inv_1040_);
lean_dec(v_a_1050_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1052_);
lean_ctor_set(v___x_1042_, 0, v___x_1051_);
v___x_1054_ = v___x_1042_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
else
{
lean_object* v_val_1057_; lean_object* v_inv_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1077_; 
v_val_1057_ = lean_ctor_get(v_x_1027_, 0);
v_inv_1058_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1060_ = v_x_1027_;
v_isShared_1061_ = v_isSharedCheck_1077_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_inv_1058_);
lean_inc(v_val_1057_);
lean_dec(v_x_1027_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1077_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_toMul_1066_; lean_object* v_toOne_1067_; lean_object* v_abs_1068_; lean_object* v_one_1069_; lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1062_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_1034_);
lean_inc(v___x_1035_);
v___x_1063_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_1062_, v___x_1035_);
v___x_1064_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_1034_);
v___x_1065_ = lp_mathlib_Matrix_nonAssocSemiring___redArg(v___x_1064_, v___x_1035_, v___x_1036_);
v_toMul_1066_ = lean_ctor_get(v___x_1063_, 1);
lean_inc_n(v_toMul_1066_, 2);
lean_dec_ref(v___x_1063_);
v_toOne_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc_n(v_toOne_1067_, 2);
lean_dec_ref(v___x_1065_);
v_abs_1068_ = lean_nat_abs(v_n_1026_);
v_one_1069_ = lean_unsigned_to_nat(1u);
v_a_1070_ = lean_nat_sub(v_abs_1068_, v_one_1069_);
lean_dec(v_abs_1068_);
v___x_1071_ = lean_nat_add(v_a_1070_, v_one_1069_);
lean_dec(v_a_1070_);
v___x_1072_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1066_, v___x_1071_, v_toOne_1067_, v_val_1057_);
v___x_1073_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1066_, v___x_1071_, v_toOne_1067_, v_inv_1058_);
lean_dec(v___x_1071_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___x_1072_);
lean_ctor_set(v___x_1060_, 0, v___x_1073_);
v___x_1075_ = v___x_1060_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1072_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___boxed(lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_M_1083_, lean_object* v_n_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg(v_inst_1078_, v_inst_1079_, v_inst_1080_, v_inst_1081_, v_inst_1082_, v_M_1083_, v_n_1084_, v_x_1085_);
lean_dec(v_n_1084_);
lean_dec_ref(v_inst_1079_);
lean_dec_ref(v_inst_1078_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16(lean_object* v_F_1087_, lean_object* v_E_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_R_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_00_u03c3_1095_, lean_object* v_M_1096_, lean_object* v_J_1097_, lean_object* v_n_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v_toCommSemiring_1101_; lean_object* v_toSemiring_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_toSemiring_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_intZero_1109_; uint8_t v_isNeg_1110_; 
v___x_1100_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1089_);
v_toCommSemiring_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_toCommSemiring_1101_);
lean_dec_ref(v___x_1100_);
v_toSemiring_1102_ = lean_ctor_get(v_inst_1093_, 0);
lean_inc_ref(v_toSemiring_1102_);
lean_dec_ref(v_inst_1093_);
v___x_1103_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1090_);
v___x_1104_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1103_);
v_toSemiring_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_toSemiring_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_1101_, v_toSemiring_1102_, v_inst_1094_, v_toSemiring_1105_, v_inst_1091_);
lean_inc(v_M_1096_);
v___x_1107_ = l_List_finRange(v_M_1096_);
v___x_1108_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1108_, 0, v_M_1096_);
v_intZero_1109_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___redArg___closed__0);
v_isNeg_1110_ = lean_int_dec_lt(v_n_1098_, v_intZero_1109_);
if (v_isNeg_1110_ == 0)
{
lean_object* v_val_1111_; lean_object* v_inv_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1128_; 
v_val_1111_ = lean_ctor_get(v_x_1099_, 0);
v_inv_1112_ = lean_ctor_get(v_x_1099_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1099_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1114_ = v_x_1099_;
v_isShared_1115_ = v_isSharedCheck_1128_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_inv_1112_);
lean_inc(v_val_1111_);
lean_dec(v_x_1099_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1128_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_toMul_1120_; lean_object* v_toOne_1121_; lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1116_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_1106_);
lean_inc(v___x_1107_);
v___x_1117_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_1116_, v___x_1107_);
v___x_1118_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_1106_);
v___x_1119_ = lp_mathlib_Matrix_nonAssocSemiring___redArg(v___x_1118_, v___x_1107_, v___x_1108_);
v_toMul_1120_ = lean_ctor_get(v___x_1117_, 1);
lean_inc_n(v_toMul_1120_, 2);
lean_dec_ref(v___x_1117_);
v_toOne_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc_n(v_toOne_1121_, 2);
lean_dec_ref(v___x_1119_);
v_a_1122_ = lean_nat_abs(v_n_1098_);
v___x_1123_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1120_, v_a_1122_, v_toOne_1121_, v_val_1111_);
v___x_1124_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1120_, v_a_1122_, v_toOne_1121_, v_inv_1112_);
lean_dec(v_a_1122_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1124_);
lean_ctor_set(v___x_1114_, 0, v___x_1123_);
v___x_1126_ = v___x_1114_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_val_1129_; lean_object* v_inv_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1149_; 
v_val_1129_ = lean_ctor_get(v_x_1099_, 0);
v_inv_1130_ = lean_ctor_get(v_x_1099_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1099_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1132_ = v_x_1099_;
v_isShared_1133_ = v_isSharedCheck_1149_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_inv_1130_);
lean_inc(v_val_1129_);
lean_dec(v_x_1099_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1149_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_toMul_1138_; lean_object* v_toOne_1139_; lean_object* v_abs_1140_; lean_object* v_one_1141_; lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1134_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_1106_);
lean_inc(v___x_1107_);
v___x_1135_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_1134_, v___x_1107_);
v___x_1136_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_1106_);
v___x_1137_ = lp_mathlib_Matrix_nonAssocSemiring___redArg(v___x_1136_, v___x_1107_, v___x_1108_);
v_toMul_1138_ = lean_ctor_get(v___x_1135_, 1);
lean_inc_n(v_toMul_1138_, 2);
lean_dec_ref(v___x_1135_);
v_toOne_1139_ = lean_ctor_get(v___x_1137_, 1);
lean_inc_n(v_toOne_1139_, 2);
lean_dec_ref(v___x_1137_);
v_abs_1140_ = lean_nat_abs(v_n_1098_);
v_one_1141_ = lean_unsigned_to_nat(1u);
v_a_1142_ = lean_nat_sub(v_abs_1140_, v_one_1141_);
lean_dec(v_abs_1140_);
v___x_1143_ = lean_nat_add(v_a_1142_, v_one_1141_);
lean_dec(v_a_1142_);
v___x_1144_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1138_, v___x_1143_, v_toOne_1139_, v_val_1129_);
v___x_1145_ = lp_mathlib_npowBinRec_go___redArg(v_toMul_1138_, v___x_1143_, v_toOne_1139_, v_inv_1130_);
lean_dec(v___x_1143_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1144_);
lean_ctor_set(v___x_1132_, 0, v___x_1145_);
v___x_1147_ = v___x_1132_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1144_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___boxed(lean_object* v_F_1150_, lean_object* v_E_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_R_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_00_u03c3_1158_, lean_object* v_M_1159_, lean_object* v_J_1160_, lean_object* v_n_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16(v_F_1150_, v_E_1151_, v_inst_1152_, v_inst_1153_, v_inst_1154_, v_R_1155_, v_inst_1156_, v_inst_1157_, v_00_u03c3_1158_, v_M_1159_, v_J_1160_, v_n_1161_, v_x_1162_);
lean_dec(v_n_1161_);
lean_dec(v_J_1160_);
lean_dec(v_00_u03c3_1158_);
lean_dec_ref(v_inst_1153_);
lean_dec_ref(v_inst_1152_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___redArg(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_00_u03c3_1169_, lean_object* v_M_1170_, lean_object* v_J_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v_toCommSemiring_1173_; lean_object* v_toSemiring_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_toSemiring_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_toAddMonoid_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1207_; 
v___x_1172_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1164_);
v_toCommSemiring_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_ref(v_toCommSemiring_1173_);
lean_dec_ref(v___x_1172_);
v_toSemiring_1174_ = lean_ctor_get(v_inst_1167_, 0);
v___x_1175_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1165_);
v___x_1176_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1175_);
v_toSemiring_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc_ref_n(v_toSemiring_1177_, 2);
lean_dec_ref(v___x_1176_);
lean_inc_ref(v_inst_1166_);
lean_inc_ref(v_inst_1168_);
lean_inc_ref(v_toSemiring_1174_);
v___x_1178_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_1173_, v_toSemiring_1174_, v_inst_1168_, v_toSemiring_1177_, v_inst_1166_);
v___x_1179_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_1178_);
v___x_1180_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_1179_);
v_toAddMonoid_1181_ = lean_ctor_get(v___x_1180_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1208_ = lean_ctor_get(v___x_1180_, 2);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v___x_1180_, 0);
lean_dec(v_unused_1209_);
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_toAddMonoid_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v_toZero_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1205_; 
v___x_1185_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_1181_);
lean_dec_ref(v_toAddMonoid_1181_);
v_toZero_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v___x_1185_, 1);
lean_dec(v_unused_1206_);
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1205_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_toZero_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1205_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_inc(v_J_1171_);
lean_inc_n(v_M_1170_, 2);
lean_inc(v_00_u03c3_1169_);
lean_inc_ref(v_inst_1168_);
lean_inc_ref(v_inst_1167_);
lean_inc_ref(v_inst_1166_);
lean_inc_ref(v_inst_1165_);
lean_inc_ref(v_inst_1164_);
v___x_1190_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___boxed), 13, 11);
lean_closure_set(v___x_1190_, 0, lean_box(0));
lean_closure_set(v___x_1190_, 1, lean_box(0));
lean_closure_set(v___x_1190_, 2, v_inst_1164_);
lean_closure_set(v___x_1190_, 3, v_inst_1165_);
lean_closure_set(v___x_1190_, 4, v_inst_1166_);
lean_closure_set(v___x_1190_, 5, lean_box(0));
lean_closure_set(v___x_1190_, 6, v_inst_1167_);
lean_closure_set(v___x_1190_, 7, v_inst_1168_);
lean_closure_set(v___x_1190_, 8, v_00_u03c3_1169_);
lean_closure_set(v___x_1190_, 9, v_M_1170_);
lean_closure_set(v___x_1190_, 10, v_J_1171_);
lean_inc_ref(v_toSemiring_1174_);
v___f_1191_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__4___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1191_, 0, v_toSemiring_1174_);
lean_closure_set(v___f_1191_, 1, v_toSemiring_1177_);
v___x_1192_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1192_, 0, v_M_1170_);
v___x_1193_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_1193_, 0, lean_box(0));
lean_closure_set(v___x_1193_, 1, lean_box(0));
lean_closure_set(v___x_1193_, 2, v___x_1192_);
lean_closure_set(v___x_1193_, 3, v_toZero_1186_);
lean_closure_set(v___x_1193_, 4, v___f_1191_);
lean_inc_ref(v___x_1193_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1193_);
lean_ctor_set(v___x_1188_, 0, v___x_1193_);
v___x_1195_ = v___x_1188_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc(v_J_1171_);
lean_inc(v_M_1170_);
lean_inc(v_00_u03c3_1169_);
lean_inc_ref(v_inst_1168_);
lean_inc_ref(v_inst_1167_);
lean_inc_ref(v_inst_1166_);
lean_inc_ref(v_inst_1165_);
lean_inc_ref(v_inst_1164_);
v___x_1196_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__8___boxed), 13, 11);
lean_closure_set(v___x_1196_, 0, lean_box(0));
lean_closure_set(v___x_1196_, 1, lean_box(0));
lean_closure_set(v___x_1196_, 2, v_inst_1164_);
lean_closure_set(v___x_1196_, 3, v_inst_1165_);
lean_closure_set(v___x_1196_, 4, v_inst_1166_);
lean_closure_set(v___x_1196_, 5, lean_box(0));
lean_closure_set(v___x_1196_, 6, v_inst_1167_);
lean_closure_set(v___x_1196_, 7, v_inst_1168_);
lean_closure_set(v___x_1196_, 8, v_00_u03c3_1169_);
lean_closure_set(v___x_1196_, 9, v_M_1170_);
lean_closure_set(v___x_1196_, 10, v_J_1171_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 2, v___x_1196_);
lean_ctor_set(v___x_1183_, 1, v___x_1195_);
lean_ctor_set(v___x_1183_, 0, v___x_1190_);
v___x_1198_ = v___x_1183_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_inc_n(v_J_1171_, 2);
lean_inc_n(v_M_1170_, 2);
lean_inc_n(v_00_u03c3_1169_, 2);
lean_inc_ref_n(v_inst_1168_, 2);
lean_inc_ref_n(v_inst_1167_, 2);
lean_inc_ref_n(v_inst_1166_, 2);
lean_inc_ref_n(v_inst_1165_, 2);
lean_inc_ref_n(v_inst_1164_, 2);
v___x_1199_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__12___boxed), 12, 11);
lean_closure_set(v___x_1199_, 0, lean_box(0));
lean_closure_set(v___x_1199_, 1, lean_box(0));
lean_closure_set(v___x_1199_, 2, v_inst_1164_);
lean_closure_set(v___x_1199_, 3, v_inst_1165_);
lean_closure_set(v___x_1199_, 4, v_inst_1166_);
lean_closure_set(v___x_1199_, 5, lean_box(0));
lean_closure_set(v___x_1199_, 6, v_inst_1167_);
lean_closure_set(v___x_1199_, 7, v_inst_1168_);
lean_closure_set(v___x_1199_, 8, v_00_u03c3_1169_);
lean_closure_set(v___x_1199_, 9, v_M_1170_);
lean_closure_set(v___x_1199_, 10, v_J_1171_);
v___x_1200_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__14___boxed), 13, 11);
lean_closure_set(v___x_1200_, 0, lean_box(0));
lean_closure_set(v___x_1200_, 1, lean_box(0));
lean_closure_set(v___x_1200_, 2, v_inst_1164_);
lean_closure_set(v___x_1200_, 3, v_inst_1165_);
lean_closure_set(v___x_1200_, 4, v_inst_1166_);
lean_closure_set(v___x_1200_, 5, lean_box(0));
lean_closure_set(v___x_1200_, 6, v_inst_1167_);
lean_closure_set(v___x_1200_, 7, v_inst_1168_);
lean_closure_set(v___x_1200_, 8, v_00_u03c3_1169_);
lean_closure_set(v___x_1200_, 9, v_M_1170_);
lean_closure_set(v___x_1200_, 10, v_J_1171_);
v___x_1201_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__16___boxed), 13, 11);
lean_closure_set(v___x_1201_, 0, lean_box(0));
lean_closure_set(v___x_1201_, 1, lean_box(0));
lean_closure_set(v___x_1201_, 2, v_inst_1164_);
lean_closure_set(v___x_1201_, 3, v_inst_1165_);
lean_closure_set(v___x_1201_, 4, v_inst_1166_);
lean_closure_set(v___x_1201_, 5, lean_box(0));
lean_closure_set(v___x_1201_, 6, v_inst_1167_);
lean_closure_set(v___x_1201_, 7, v_inst_1168_);
lean_closure_set(v___x_1201_, 8, v_00_u03c3_1169_);
lean_closure_set(v___x_1201_, 9, v_M_1170_);
lean_closure_set(v___x_1201_, 10, v_J_1171_);
v___x_1202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1198_);
lean_ctor_set(v___x_1202_, 1, v___x_1199_);
lean_ctor_set(v___x_1202_, 2, v___x_1200_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
return v___x_1202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA(lean_object* v_F_1210_, lean_object* v_E_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_R_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_00_u03c3_1218_, lean_object* v_M_1219_, lean_object* v_J_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___redArg(v_inst_1212_, v_inst_1213_, v_inst_1214_, v_inst_1216_, v_inst_1217_, v_00_u03c3_1218_, v_M_1219_, v_J_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instTopologicalSpaceHA(lean_object* v_F_1222_, lean_object* v_E_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_R_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_00_u03c3_1230_, lean_object* v_M_1231_, lean_object* v_J_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_box(0);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instTopologicalSpaceHA___boxed(lean_object* v_F_1235_, lean_object* v_E_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_R_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_00_u03c3_1243_, lean_object* v_M_1244_, lean_object* v_J_1245_, lean_object* v_inst_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instTopologicalSpaceHA(v_F_1235_, v_E_1236_, v_inst_1237_, v_inst_1238_, v_inst_1239_, v_R_1240_, v_inst_1241_, v_inst_1242_, v_00_u03c3_1243_, v_M_1244_, v_J_1245_, v_inst_1246_);
lean_dec(v_J_1245_);
lean_dec(v_M_1244_);
lean_dec(v_00_u03c3_1243_);
lean_dec_ref(v_inst_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_inst_1238_);
lean_dec_ref(v_inst_1237_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMeasurableSpaceHAOfTopologicalSpace(lean_object* v_F_1248_, lean_object* v_E_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_R_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_00_u03c3_1256_, lean_object* v_M_1257_, lean_object* v_J_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMeasurableSpaceHAOfTopologicalSpace___boxed(lean_object* v_F_1261_, lean_object* v_E_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_R_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_00_u03c3_1269_, lean_object* v_M_1270_, lean_object* v_J_1271_, lean_object* v_inst_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMeasurableSpaceHAOfTopologicalSpace(v_F_1261_, v_E_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_R_1266_, v_inst_1267_, v_inst_1268_, v_00_u03c3_1269_, v_M_1270_, v_J_1271_, v_inst_1272_);
lean_dec(v_J_1271_);
lean_dec(v_M_1270_);
lean_dec(v_00_u03c3_1269_);
lean_dec_ref(v_inst_1268_);
lean_dec_ref(v_inst_1267_);
lean_dec_ref(v_inst_1265_);
lean_dec_ref(v_inst_1264_);
lean_dec_ref(v_inst_1263_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___redArg(lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_M_1279_, lean_object* v_m_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v_toCommSemiring_1283_; lean_object* v_toSemiring_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_toSemiring_1287_; lean_object* v___x_1288_; lean_object* v_val_1289_; lean_object* v_inv_1290_; lean_object* v_val_1291_; lean_object* v_inv_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1306_; 
v___x_1282_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1274_);
v_toCommSemiring_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_toCommSemiring_1283_);
lean_dec_ref(v___x_1282_);
v_toSemiring_1284_ = lean_ctor_get(v_inst_1277_, 0);
lean_inc_ref(v_toSemiring_1284_);
lean_dec_ref(v_inst_1277_);
v___x_1285_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1275_);
v___x_1286_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1285_);
v_toSemiring_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_toSemiring_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_1283_, v_toSemiring_1284_, v_inst_1278_, v_toSemiring_1287_, v_inst_1276_);
v_val_1289_ = lean_ctor_get(v_m_1280_, 0);
lean_inc(v_val_1289_);
v_inv_1290_ = lean_ctor_get(v_m_1280_, 1);
lean_inc(v_inv_1290_);
lean_dec_ref(v_m_1280_);
v_val_1291_ = lean_ctor_get(v_a_1281_, 0);
v_inv_1292_ = lean_ctor_get(v_a_1281_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1294_ = v_a_1281_;
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_inv_1292_);
lean_inc(v_val_1291_);
lean_dec(v_a_1281_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v_toAddCommMonoid_1297_; lean_object* v___x_1298_; lean_object* v_toMul_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___x_1304_; 
v___x_1296_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_1288_);
lean_dec_ref(v___x_1288_);
v_toAddCommMonoid_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref_n(v_toAddCommMonoid_1297_, 2);
v___x_1298_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_1296_);
v_toMul_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc_n(v_toMul_1299_, 2);
lean_dec_ref(v___x_1298_);
v___x_1300_ = l_List_finRange(v_M_1279_);
lean_inc(v___x_1300_);
v___f_1301_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_1301_, 0, v_inv_1290_);
lean_closure_set(v___f_1301_, 1, v_inv_1292_);
lean_closure_set(v___f_1301_, 2, v___x_1300_);
lean_closure_set(v___f_1301_, 3, v_toMul_1299_);
lean_closure_set(v___f_1301_, 4, v_toAddCommMonoid_1297_);
v___f_1302_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_1302_, 0, v_val_1291_);
lean_closure_set(v___f_1302_, 1, v_val_1289_);
lean_closure_set(v___f_1302_, 2, v___x_1300_);
lean_closure_set(v___f_1302_, 3, v_toMul_1299_);
lean_closure_set(v___f_1302_, 4, v_toAddCommMonoid_1297_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v___f_1301_);
lean_ctor_set(v___x_1294_, 0, v___f_1302_);
v___x_1304_ = v___x_1294_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___f_1302_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___f_1301_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___redArg___boxed(lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_M_1312_, lean_object* v_m_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___redArg(v_inst_1307_, v_inst_1308_, v_inst_1309_, v_inst_1310_, v_inst_1311_, v_M_1312_, v_m_1313_, v_a_1314_);
lean_dec_ref(v_inst_1308_);
lean_dec_ref(v_inst_1307_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1(lean_object* v_F_1316_, lean_object* v_E_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_R_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_00_u03c3_1324_, lean_object* v_M_1325_, lean_object* v_J_1326_, lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v_toCommSemiring_1330_; lean_object* v_toSemiring_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_toSemiring_1334_; lean_object* v___x_1335_; lean_object* v_val_1336_; lean_object* v_inv_1337_; lean_object* v_val_1338_; lean_object* v_inv_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1353_; 
v___x_1329_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1318_);
v_toCommSemiring_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_toCommSemiring_1330_);
lean_dec_ref(v___x_1329_);
v_toSemiring_1331_ = lean_ctor_get(v_inst_1322_, 0);
lean_inc_ref(v_toSemiring_1331_);
lean_dec_ref(v_inst_1322_);
v___x_1332_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1319_);
v___x_1333_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1332_);
v_toSemiring_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc_ref(v_toSemiring_1334_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = lp_mathlib_Algebra_TensorProduct_instSemiring___redArg(v_toCommSemiring_1330_, v_toSemiring_1331_, v_inst_1323_, v_toSemiring_1334_, v_inst_1320_);
v_val_1336_ = lean_ctor_get(v_m_1327_, 0);
lean_inc(v_val_1336_);
v_inv_1337_ = lean_ctor_get(v_m_1327_, 1);
lean_inc(v_inv_1337_);
lean_dec_ref(v_m_1327_);
v_val_1338_ = lean_ctor_get(v_a_1328_, 0);
v_inv_1339_ = lean_ctor_get(v_a_1328_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_a_1328_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1341_ = v_a_1328_;
v_isShared_1342_ = v_isSharedCheck_1353_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_inv_1339_);
lean_inc(v_val_1338_);
lean_dec(v_a_1328_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1353_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v_toAddCommMonoid_1344_; lean_object* v___x_1345_; lean_object* v_toMul_1346_; lean_object* v___x_1347_; lean_object* v___f_1348_; lean_object* v___f_1349_; lean_object* v___x_1351_; 
v___x_1343_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v___x_1335_);
lean_dec_ref(v___x_1335_);
v_toAddCommMonoid_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_ref_n(v_toAddCommMonoid_1344_, 2);
v___x_1345_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_1343_);
v_toMul_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_n(v_toMul_1346_, 2);
lean_dec_ref(v___x_1345_);
v___x_1347_ = l_List_finRange(v_M_1325_);
lean_inc(v___x_1347_);
v___f_1348_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_1348_, 0, v_inv_1337_);
lean_closure_set(v___f_1348_, 1, v_inv_1339_);
lean_closure_set(v___f_1348_, 2, v___x_1347_);
lean_closure_set(v___f_1348_, 3, v_toMul_1346_);
lean_closure_set(v___f_1348_, 4, v_toAddCommMonoid_1344_);
v___f_1349_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instGroupHA___aux__1___redArg___lam__5___boxed), 7, 5);
lean_closure_set(v___f_1349_, 0, v_val_1338_);
lean_closure_set(v___f_1349_, 1, v_val_1336_);
lean_closure_set(v___f_1349_, 2, v___x_1347_);
lean_closure_set(v___f_1349_, 3, v_toMul_1346_);
lean_closure_set(v___f_1349_, 4, v_toAddCommMonoid_1344_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___f_1348_);
lean_ctor_set(v___x_1341_, 0, v___f_1349_);
v___x_1351_ = v___x_1341_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___f_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___f_1348_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___boxed(lean_object* v_F_1354_, lean_object* v_E_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_R_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_00_u03c3_1362_, lean_object* v_M_1363_, lean_object* v_J_1364_, lean_object* v_m_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1(v_F_1354_, v_E_1355_, v_inst_1356_, v_inst_1357_, v_inst_1358_, v_R_1359_, v_inst_1360_, v_inst_1361_, v_00_u03c3_1362_, v_M_1363_, v_J_1364_, v_m_1365_, v_a_1366_);
lean_dec(v_J_1364_);
lean_dec(v_00_u03c3_1362_);
lean_dec_ref(v_inst_1357_);
lean_dec_ref(v_inst_1356_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___redArg(lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_inst_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_00_u03c3_1373_, lean_object* v_M_1374_, lean_object* v_J_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___boxed), 13, 11);
lean_closure_set(v___x_1376_, 0, lean_box(0));
lean_closure_set(v___x_1376_, 1, lean_box(0));
lean_closure_set(v___x_1376_, 2, v_inst_1368_);
lean_closure_set(v___x_1376_, 3, v_inst_1369_);
lean_closure_set(v___x_1376_, 4, v_inst_1370_);
lean_closure_set(v___x_1376_, 5, lean_box(0));
lean_closure_set(v___x_1376_, 6, v_inst_1371_);
lean_closure_set(v___x_1376_, 7, v_inst_1372_);
lean_closure_set(v___x_1376_, 8, v_00_u03c3_1373_);
lean_closure_set(v___x_1376_, 9, v_M_1374_);
lean_closure_set(v___x_1376_, 10, v_J_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA(lean_object* v_F_1377_, lean_object* v_E_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_R_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_00_u03c3_1385_, lean_object* v_M_1386_, lean_object* v_J_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionSubtypeGeneralLinearGroupFinTensorProductMemSubgroupHRHFinInHA___aux__1___boxed), 13, 11);
lean_closure_set(v___x_1388_, 0, lean_box(0));
lean_closure_set(v___x_1388_, 1, lean_box(0));
lean_closure_set(v___x_1388_, 2, v_inst_1379_);
lean_closure_set(v___x_1388_, 3, v_inst_1380_);
lean_closure_set(v___x_1388_, 4, v_inst_1381_);
lean_closure_set(v___x_1388_, 5, lean_box(0));
lean_closure_set(v___x_1388_, 6, v_inst_1383_);
lean_closure_set(v___x_1388_, 7, v_inst_1384_);
lean_closure_set(v___x_1388_, 8, v_00_u03c3_1385_);
lean_closure_set(v___x_1388_, 9, v_M_1386_);
lean_closure_set(v___x_1388_, 10, v_J_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___redArg(lean_object* v_h_1389_){
_start:
{
lean_inc_ref(v_h_1389_);
return v_h_1389_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___redArg___boxed(lean_object* v_h_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___redArg(v_h_1390_);
lean_dec_ref(v_h_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat(lean_object* v_F_1392_, lean_object* v_E_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_R_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_00_u03c3_1400_, lean_object* v_M_1401_, lean_object* v_J_1402_, lean_object* v_h_1403_){
_start:
{
lean_inc_ref(v_h_1403_);
return v_h_1403_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat___boxed(lean_object* v_F_1404_, lean_object* v_E_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_R_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_00_u03c3_1412_, lean_object* v_M_1413_, lean_object* v_J_1414_, lean_object* v_h_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HA_mat(v_F_1404_, v_E_1405_, v_inst_1406_, v_inst_1407_, v_inst_1408_, v_R_1409_, v_inst_1410_, v_inst_1411_, v_00_u03c3_1412_, v_M_1413_, v_J_1414_, v_h_1415_);
lean_dec_ref(v_h_1415_);
lean_dec(v_J_1414_);
lean_dec(v_M_1413_);
lean_dec(v_00_u03c3_1412_);
lean_dec_ref(v_inst_1411_);
lean_dec_ref(v_inst_1410_);
lean_dec_ref(v_inst_1408_);
lean_dec_ref(v_inst_1407_);
lean_dec_ref(v_inst_1406_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA___redArg(lean_object* v_x_1417_, lean_object* v_y_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_x_1417_);
lean_ctor_set(v___x_1419_, 1, v_y_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA(lean_object* v_F_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_x_1423_, lean_object* v_y_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_x_1423_);
lean_ctor_set(v___x_1425_, 1, v_y_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA___boxed(lean_object* v_F_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_x_1429_, lean_object* v_y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_pairA(v_F_1426_, v_inst_1427_, v_inst_1428_, v_x_1429_, v_y_1430_);
lean_dec_ref(v_inst_1427_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf___redArg(lean_object* v_inst_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_T_1437_){
_start:
{
lean_object* v___f_1438_; lean_object* v___x_1439_; 
v___f_1438_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_JR___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1438_, 0, v_inst_1432_);
lean_closure_set(v___f_1438_, 1, v_inst_1433_);
lean_closure_set(v___f_1438_, 2, v_inst_1434_);
lean_closure_set(v___f_1438_, 3, v_inst_1435_);
lean_closure_set(v___f_1438_, 4, v_inst_1436_);
v___x_1439_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_map), 8, 6);
lean_closure_set(v___x_1439_, 0, lean_box(0));
lean_closure_set(v___x_1439_, 1, lean_box(0));
lean_closure_set(v___x_1439_, 2, lean_box(0));
lean_closure_set(v___x_1439_, 3, lean_box(0));
lean_closure_set(v___x_1439_, 4, v_T_1437_);
lean_closure_set(v___x_1439_, 5, v___f_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf(lean_object* v_F_1440_, lean_object* v_E_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_R_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_00_u03c3_1448_, lean_object* v_n_1449_, lean_object* v_T_1450_, lean_object* v_hT_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf___redArg(v_inst_1442_, v_inst_1443_, v_inst_1444_, v_inst_1446_, v_inst_1447_, v_T_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf___boxed(lean_object* v_F_1453_, lean_object* v_E_1454_, lean_object* v_inst_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_R_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_00_u03c3_1461_, lean_object* v_n_1462_, lean_object* v_T_1463_, lean_object* v_hT_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_hermOf(v_F_1453_, v_E_1454_, v_inst_1455_, v_inst_1456_, v_inst_1457_, v_R_1458_, v_inst_1459_, v_inst_1460_, v_00_u03c3_1461_, v_n_1462_, v_T_1463_, v_hT_1464_);
lean_dec(v_n_1462_);
lean_dec(v_00_u03c3_1461_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_M_1471_, lean_object* v_h_1472_, lean_object* v_X_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_actTup___redArg(v_inst_1466_, v_inst_1467_, v_inst_1468_, v_inst_1469_, v_inst_1470_, v_M_1471_, v_h_1472_, v_X_1473_, v___y_1474_, v___y_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0___boxed(lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_M_1482_, lean_object* v_h_1483_, lean_object* v_X_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0(v_inst_1477_, v_inst_1478_, v_inst_1479_, v_inst_1480_, v_inst_1481_, v_M_1482_, v_h_1483_, v_X_1484_, v___y_1485_, v___y_1486_);
lean_dec_ref(v_inst_1480_);
lean_dec_ref(v_inst_1478_);
lean_dec_ref(v_inst_1477_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg(lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_M_1493_){
_start:
{
lean_object* v___f_1494_; 
v___f_1494_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0___boxed), 10, 6);
lean_closure_set(v___f_1494_, 0, v_inst_1488_);
lean_closure_set(v___f_1494_, 1, v_inst_1489_);
lean_closure_set(v___f_1494_, 2, v_inst_1490_);
lean_closure_set(v___f_1494_, 3, v_inst_1491_);
lean_closure_set(v___f_1494_, 4, v_inst_1492_);
lean_closure_set(v___f_1494_, 5, v_M_1493_);
return v___f_1494_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup(lean_object* v_F_1495_, lean_object* v_E_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_R_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_00_u03c3_1503_, lean_object* v_M_1504_, lean_object* v_J_1505_, lean_object* v_n_1506_){
_start:
{
lean_object* v___f_1507_; 
v___f_1507_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___redArg___lam__0___boxed), 10, 6);
lean_closure_set(v___f_1507_, 0, v_inst_1497_);
lean_closure_set(v___f_1507_, 1, v_inst_1498_);
lean_closure_set(v___f_1507_, 2, v_inst_1499_);
lean_closure_set(v___f_1507_, 3, v_inst_1501_);
lean_closure_set(v___f_1507_, 4, v_inst_1502_);
lean_closure_set(v___f_1507_, 5, v_M_1504_);
return v___f_1507_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup___boxed(lean_object* v_F_1508_, lean_object* v_E_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_R_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_00_u03c3_1516_, lean_object* v_M_1517_, lean_object* v_J_1518_, lean_object* v_n_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_instMulActionTup(v_F_1508_, v_E_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_R_1513_, v_inst_1514_, v_inst_1515_, v_00_u03c3_1516_, v_M_1517_, v_J_1518_, v_n_1519_);
lean_dec(v_n_1519_);
lean_dec(v_J_1518_);
lean_dec(v_00_u03c3_1516_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_Hstab(lean_object* v_F_1521_, lean_object* v_E_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_R_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_00_u03c3_1529_, lean_object* v_M_1530_, lean_object* v_J_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_Hstab___boxed(lean_object* v_F_1534_, lean_object* v_E_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_R_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_00_u03c3_1542_, lean_object* v_M_1543_, lean_object* v_J_1544_, lean_object* v_x_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_Hstab(v_F_1534_, v_E_1535_, v_inst_1536_, v_inst_1537_, v_inst_1538_, v_R_1539_, v_inst_1540_, v_inst_1541_, v_00_u03c3_1542_, v_M_1543_, v_J_1544_, v_x_1545_);
lean_dec(v_x_1545_);
lean_dec(v_J_1544_);
lean_dec(v_M_1543_);
lean_dec(v_00_u03c3_1542_);
lean_dec_ref(v_inst_1541_);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1538_);
lean_dec_ref(v_inst_1537_);
lean_dec_ref(v_inst_1536_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HstabFin(lean_object* v_F_1547_, lean_object* v_E_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_R_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_00_u03c3_1555_, lean_object* v_M_1556_, lean_object* v_J_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_box(0);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HstabFin___boxed(lean_object* v_F_1560_, lean_object* v_E_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v_R_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_00_u03c3_1568_, lean_object* v_M_1569_, lean_object* v_J_1570_, lean_object* v_x_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_HstabFin(v_F_1560_, v_E_1561_, v_inst_1562_, v_inst_1563_, v_inst_1564_, v_R_1565_, v_inst_1566_, v_inst_1567_, v_00_u03c3_1568_, v_M_1569_, v_J_1570_, v_x_1571_);
lean_dec(v_x_1571_);
lean_dec(v_J_1570_);
lean_dec(v_M_1569_);
lean_dec(v_00_u03c3_1568_);
lean_dec_ref(v_inst_1567_);
lean_dec_ref(v_inst_1566_);
lean_dec_ref(v_inst_1564_);
lean_dec_ref(v_inst_1563_);
lean_dec_ref(v_inst_1562_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measHerm(lean_object* v_F_1573_, lean_object* v_E_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_R_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_00_u03c3_1581_, lean_object* v_inst_1582_, lean_object* v_n_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_box(0);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measHerm___boxed(lean_object* v_F_1585_, lean_object* v_E_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_R_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_00_u03c3_1593_, lean_object* v_inst_1594_, lean_object* v_n_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_measHerm(v_F_1585_, v_E_1586_, v_inst_1587_, v_inst_1588_, v_inst_1589_, v_R_1590_, v_inst_1591_, v_inst_1592_, v_00_u03c3_1593_, v_inst_1594_, v_n_1595_);
lean_dec(v_n_1595_);
lean_dec(v_00_u03c3_1593_);
lean_dec_ref(v_inst_1592_);
lean_dec_ref(v_inst_1591_);
lean_dec_ref(v_inst_1589_);
lean_dec_ref(v_inst_1588_);
lean_dec_ref(v_inst_1587_);
return v_res_1596_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
