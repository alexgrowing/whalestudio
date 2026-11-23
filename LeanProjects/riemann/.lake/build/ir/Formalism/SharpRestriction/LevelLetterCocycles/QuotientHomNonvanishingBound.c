// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.LevelLetterCocycles.DataN public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc public import Formalism.WeaklyAdmissibleFiltrations.StatementTor public import Formalism.GaloisCohomology.Statement
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
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toLinAlgEquiv_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toMonoidWithZero___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_OreLocalization_liftExpand___at___00TensorProduct_SMul_aux___at___00Module_End_genEigenspace___at___00Formalism_BasicNotions_heckeEig___at___00Formalism_BasicNotions_NData_eigSum_spec__0_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toLin_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_TopologicalSpace_instCompleteLattice(lean_object*);
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_OreLocalization_oreSetComm(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OreLocalization_instAddGroupOreLocalization___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_WeaklyAdmissibleFiltrations_actD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* lp_mathlib_Matrix_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_mapMatrix___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0;
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Z1urD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Z1urD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw___boxed(lean_object**);
static const lean_closure_object lp_tree_Formalism_MainNotions_N_decS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_N_decS___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_N_decS___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_decS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_decS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___closed__0 = (const lean_object*)&lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiU___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_toK___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_toK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_toK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___closed__0 = (const lean_object*)&lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rhoO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rhoO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rhoO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_VS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_VS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtLow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtLow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_MainNotions_N_Eel_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_MainNotions_N_Eel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_MainNotions_N_Eel_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_MainNotions_N_Eel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_Ioc___at___00Formalism_MainNotions_N_del51_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_Ioc___at___00Formalism_MainNotions_N_del51_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___closed__0 = (const lean_object*)&lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_con___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_con___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_liftOn_x27___at___00AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_liftOn_x27___at___00AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLatG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLatG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOG___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Br_PD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Br_PD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Br_PD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___redArg___lam__0(lean_object* v_00_u03c1_1_, lean_object* v_toSemiring_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_g_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; lean_object* v_val_9_; lean_object* v___x_10_; lean_object* v_toLinearMap_11_; lean_object* v___x_12_; 
v___x_8_ = lean_apply_1(v_00_u03c1_1_, v_g_5_);
v_val_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_val_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lp_mathlib_Matrix_toLin_x27___redArg(v_toSemiring_2_, v_inst_3_, v_inst_4_);
v_toLinearMap_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_toLinearMap_11_);
lean_dec_ref(v___x_10_);
v___x_12_ = lean_apply_3(v_toLinearMap_11_, v_val_9_, v___y_6_, v___y_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___redArg(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_00_u03c1_16_){
_start:
{
lean_object* v_toSemiring_17_; lean_object* v___f_18_; 
v_toSemiring_17_ = lean_ctor_get(v_inst_13_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v_inst_13_);
v___f_18_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_glRep___redArg___lam__0), 7, 4);
lean_closure_set(v___f_18_, 0, v_00_u03c1_16_);
lean_closure_set(v___f_18_, 1, v_toSemiring_17_);
lean_closure_set(v___f_18_, 2, v_inst_15_);
lean_closure_set(v___f_18_, 3, v_inst_14_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep(lean_object* v_O_19_, lean_object* v_G_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_n_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_00_u03c1_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_MainNotions_N_glRep___redArg(v_inst_21_, v_inst_24_, v_inst_25_, v_00_u03c1_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___boxed(lean_object* v_O_28_, lean_object* v_G_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_n_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_00_u03c1_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_MainNotions_N_glRep(v_O_28_, v_G_29_, v_inst_30_, v_inst_31_, v_n_32_, v_inst_33_, v_inst_34_, v_00_u03c1_35_);
lean_dec_ref(v_inst_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___redArg___lam__0(lean_object* v_00_u03c7_37_, lean_object* v_00_u03c1_38_, lean_object* v_inst_39_, lean_object* v_g_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_42_; lean_object* v_val_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
lean_inc(v_g_40_);
v___x_42_ = lean_apply_1(v_00_u03c7_37_, v_g_40_);
v_val_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_val_43_);
lean_dec_ref(v___x_42_);
v___x_44_ = lean_apply_2(v_00_u03c1_38_, v_g_40_, v___y_41_);
v___x_45_ = lean_apply_2(v_inst_39_, v_val_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___redArg(lean_object* v_inst_46_, lean_object* v_00_u03c1_47_, lean_object* v_00_u03c7_48_){
_start:
{
lean_object* v___f_49_; 
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_twistRep___redArg___lam__0), 5, 3);
lean_closure_set(v___f_49_, 0, v_00_u03c7_48_);
lean_closure_set(v___f_49_, 1, v_00_u03c1_47_);
lean_closure_set(v___f_49_, 2, v_inst_46_);
return v___f_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep(lean_object* v_O_50_, lean_object* v_G_51_, lean_object* v_V_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_00_u03c1_57_, lean_object* v_00_u03c7_58_){
_start:
{
lean_object* v___f_59_; 
v___f_59_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_twistRep___redArg___lam__0), 5, 3);
lean_closure_set(v___f_59_, 0, v_00_u03c7_58_);
lean_closure_set(v___f_59_, 1, v_00_u03c1_57_);
lean_closure_set(v___f_59_, 2, v_inst_56_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___boxed(lean_object* v_O_60_, lean_object* v_G_61_, lean_object* v_V_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_00_u03c1_67_, lean_object* v_00_u03c7_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Formalism_MainNotions_N_twistRep(v_O_60_, v_G_61_, v_V_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_inst_66_, v_00_u03c1_67_, v_00_u03c7_68_);
lean_dec_ref(v_inst_65_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___redArg(lean_object* v_f_70_){
_start:
{
lean_inc_ref(v_f_70_);
return v_f_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___redArg___boxed(lean_object* v_f_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___redArg(v_f_71_);
lean_dec_ref(v_f_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1(lean_object* v_N_73_, lean_object* v_i_74_, lean_object* v___x_75_, lean_object* v_f_76_, lean_object* v_map__mul_77_){
_start:
{
lean_inc_ref(v_f_76_);
return v_f_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1___boxed(lean_object* v_N_78_, lean_object* v_i_79_, lean_object* v___x_80_, lean_object* v_f_81_, lean_object* v_map__mul_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_N_Glob_Wp_spec__1(v_N_78_, v_i_79_, v___x_80_, v_f_81_, v_map__mul_82_);
lean_dec_ref(v_f_81_);
lean_dec_ref(v___x_80_);
lean_dec(v_i_79_);
lean_dec_ref(v_N_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg___lam__0(lean_object* v_00_u03c7_84_, lean_object* v_toSemiring_85_, lean_object* v_00_u03c1_86_, lean_object* v_g_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_90_; lean_object* v_val_91_; lean_object* v_toMonoid_92_; lean_object* v___x_93_; lean_object* v_toMul_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
lean_inc_ref(v_g_87_);
v___x_90_ = lean_apply_1(v_00_u03c7_84_, v_g_87_);
v_val_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_val_91_);
lean_dec_ref(v___x_90_);
v_toMonoid_92_ = lean_ctor_get(v_toSemiring_85_, 1);
v___x_93_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_92_);
v_toMul_94_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_toMul_94_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_apply_3(v_00_u03c1_86_, v_g_87_, v___y_88_, v___y_89_);
v___x_96_ = lean_apply_2(v_toMul_94_, v_val_91_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg___lam__0___boxed(lean_object* v_00_u03c7_97_, lean_object* v_toSemiring_98_, lean_object* v_00_u03c1_99_, lean_object* v_g_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg___lam__0(v_00_u03c7_97_, v_toSemiring_98_, v_00_u03c1_99_, v_g_100_, v___y_101_, v___y_102_);
lean_dec_ref(v_toSemiring_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg(lean_object* v_N_104_, lean_object* v_i_105_, lean_object* v_00_u03c1_106_, lean_object* v_00_u03c7_107_){
_start:
{
lean_object* v_instO_108_; lean_object* v___x_109_; lean_object* v_toSemiring_110_; lean_object* v___f_111_; 
v_instO_108_ = lean_ctor_get(v_N_104_, 9);
lean_inc_ref(v_instO_108_);
lean_dec_ref(v_N_104_);
v___x_109_ = lean_apply_1(v_instO_108_, v_i_105_);
v_toSemiring_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_toSemiring_110_);
lean_dec_ref(v___x_109_);
v___f_111_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_111_, 0, v_00_u03c7_107_);
lean_closure_set(v___f_111_, 1, v_toSemiring_110_);
lean_closure_set(v___f_111_, 2, v_00_u03c1_106_);
return v___f_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2(lean_object* v_N_112_, lean_object* v_i_113_, lean_object* v___x_114_, lean_object* v_00_u03c1_115_, lean_object* v_00_u03c7_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg(v_N_112_, v_i_113_, v_00_u03c1_115_, v_00_u03c7_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___boxed(lean_object* v_N_118_, lean_object* v_i_119_, lean_object* v___x_120_, lean_object* v_00_u03c1_121_, lean_object* v_00_u03c7_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2(v_N_118_, v_i_119_, v___x_120_, v_00_u03c1_121_, v_00_u03c7_122_);
lean_dec_ref(v___x_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___lam__0(lean_object* v_chi_124_, lean_object* v_i_125_, lean_object* v___x_126_, lean_object* v_g_127_){
_start:
{
lean_object* v___x_128_; lean_object* v_val_129_; lean_object* v_inv_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v___x_128_ = lean_apply_3(v_chi_124_, v_i_125_, v___x_126_, v_g_127_);
v_val_129_ = lean_ctor_get(v___x_128_, 0);
v_inv_130_ = lean_ctor_get(v___x_128_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_128_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_inv_130_);
lean_inc(v_val_129_);
lean_dec(v___x_128_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_val_129_);
lean_ctor_set(v___x_132_, 0, v_inv_130_);
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_inv_130_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_val_129_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_invFun_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_3(v_invFun_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(lean_object* v_self_143_){
_start:
{
lean_object* v_toLinearMap_144_; lean_object* v_invFun_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_toLinearMap_144_ = lean_ctor_get(v_self_143_, 0);
v_invFun_145_ = lean_ctor_get(v_self_143_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_self_143_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v_self_143_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_invFun_145_);
lean_inc(v_toLinearMap_144_);
lean_dec(v_self_143_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_toLinearMap_144_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_invFun_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg(lean_object* v_N_153_, lean_object* v_i_154_, lean_object* v_00_u03c3_155_, lean_object* v_00_u03c3_x27_156_, lean_object* v_e_157_){
_start:
{
lean_object* v_invFun_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_invFun_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_invFun_158_ = lean_ctor_get(v_e_157_, 1);
lean_inc(v_invFun_158_);
v___x_159_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_e_157_);
v___x_160_ = lp_mathlib_Equiv_symm___redArg(v___x_159_);
v_invFun_161_ = lean_ctor_get(v___x_160_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v___x_160_, 0);
lean_dec(v_unused_170_);
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_invFun_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___f_165_; lean_object* v___x_167_; 
v___f_165_ = lean_alloc_closure((void*)(lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg___lam__0), 4, 1);
lean_closure_set(v___f_165_, 0, v_invFun_158_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___f_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___f_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_invFun_161_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_N_171_, lean_object* v_i_172_, lean_object* v_00_u03c3_173_, lean_object* v_00_u03c3_x27_174_, lean_object* v_e_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg(v_N_171_, v_i_172_, v_00_u03c3_173_, v_00_u03c3_x27_174_, v_e_175_);
lean_dec(v_00_u03c3_x27_174_);
lean_dec(v_00_u03c3_173_);
lean_dec(v_i_172_);
lean_dec_ref(v_N_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___lam__0(lean_object* v_toZero_177_, lean_object* v_x_178_){
_start:
{
lean_inc(v_toZero_177_);
return v_toZero_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_toZero_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___lam__0(v_toZero_179_, v_x_180_);
lean_dec(v_x_180_);
lean_dec(v_toZero_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_N_182_, lean_object* v_i_183_, lean_object* v_i_184_, lean_object* v_x_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_instO_187_; lean_object* v___x_188_; lean_object* v_toSemiring_189_; lean_object* v___x_190_; lean_object* v_toZero_191_; lean_object* v___f_192_; lean_object* v___x_193_; 
v_instO_187_ = lean_ctor_get(v_N_182_, 9);
lean_inc_ref(v_instO_187_);
lean_dec_ref(v_N_182_);
v___x_188_ = lean_apply_1(v_instO_187_, v_i_183_);
v_toSemiring_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc_ref(v_toSemiring_189_);
lean_dec_ref(v___x_188_);
v___x_190_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_189_);
v_toZero_191_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_toZero_191_);
lean_dec_ref(v___x_190_);
v___f_192_ = lean_alloc_closure((void*)(lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_192_, 0, v_toZero_191_);
v___x_193_ = lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(v___f_192_, v_i_184_, v_x_185_, v_a_186_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_N_194_, lean_object* v_i_195_, lean_object* v_i_196_, lean_object* v_x_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg(v_N_194_, v_i_195_, v_i_196_, v_x_197_, v_a_198_);
lean_dec(v_x_197_);
lean_dec(v_i_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__1(lean_object* v_N_200_, lean_object* v_i_201_, lean_object* v_j_202_, lean_object* v_toOne_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg(v_N_200_, v_i_201_, v_j_202_, v_toOne_203_, v___y_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__1___boxed(lean_object* v_N_206_, lean_object* v_i_207_, lean_object* v_j_208_, lean_object* v_toOne_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__1(v_N_206_, v_i_207_, v_j_208_, v_toOne_209_, v___y_210_);
lean_dec(v_toOne_209_);
lean_dec(v_j_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v_N_212_, lean_object* v_i_213_, lean_object* v_toOne_214_, lean_object* v_f_215_, lean_object* v_i_216_, lean_object* v_j_217_){
_start:
{
lean_object* v___f_218_; lean_object* v___x_219_; 
v___f_218_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_218_, 0, v_N_212_);
lean_closure_set(v___f_218_, 1, v_i_213_);
lean_closure_set(v___f_218_, 2, v_j_217_);
lean_closure_set(v___f_218_, 3, v_toOne_214_);
v___x_219_ = lean_apply_2(v_f_215_, v___f_218_, v_i_216_);
return v___x_219_;
}
}
static lean_object* _init_lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3(lean_object* v_N_221_, lean_object* v_i_222_, lean_object* v_toOne_223_, lean_object* v_f_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_227_; lean_object* v_toFun_228_; lean_object* v___f_229_; lean_object* v___x_230_; 
v___x_227_ = lean_obj_once(&lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0, &lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0_once, _init_lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0);
v_toFun_228_ = lean_ctor_get(v___x_227_, 0);
v___f_229_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__2), 6, 4);
lean_closure_set(v___f_229_, 0, v_N_221_);
lean_closure_set(v___f_229_, 1, v_i_222_);
lean_closure_set(v___f_229_, 2, v_toOne_223_);
lean_closure_set(v___f_229_, 3, v_f_224_);
lean_inc(v_toFun_228_);
v___x_230_ = lean_apply_3(v_toFun_228_, v___f_229_, v___y_225_, v___y_226_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13___lam__0(lean_object* v_toAdd_231_, lean_object* v_x1_232_, lean_object* v_x2_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_apply_2(v_toAdd_231_, v_x1_232_, v_x2_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13(lean_object* v_N_235_, lean_object* v_i_236_, lean_object* v_s_237_){
_start:
{
lean_object* v_instO_238_; lean_object* v___x_239_; lean_object* v_toSemiring_240_; lean_object* v___x_241_; lean_object* v_toNonUnitalNonAssocSemiring_242_; lean_object* v_toAddCommMonoid_243_; lean_object* v___x_244_; lean_object* v_toZero_245_; lean_object* v_toAdd_246_; lean_object* v___f_247_; lean_object* v___x_248_; 
v_instO_238_ = lean_ctor_get(v_N_235_, 9);
lean_inc_ref(v_instO_238_);
lean_dec_ref(v_N_235_);
v___x_239_ = lean_apply_1(v_instO_238_, v_i_236_);
v_toSemiring_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_toSemiring_240_);
lean_dec_ref(v___x_239_);
v___x_241_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_240_);
v_toNonUnitalNonAssocSemiring_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_toNonUnitalNonAssocSemiring_242_);
lean_dec_ref(v___x_241_);
v_toAddCommMonoid_243_ = lean_ctor_get(v_toNonUnitalNonAssocSemiring_242_, 0);
lean_inc_ref(v_toAddCommMonoid_243_);
lean_dec_ref(v_toNonUnitalNonAssocSemiring_242_);
v___x_244_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_243_);
lean_dec_ref(v_toAddCommMonoid_243_);
v_toZero_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_toZero_245_);
v_toAdd_246_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_toAdd_246_);
lean_dec_ref(v___x_244_);
v___f_247_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13___lam__0), 3, 1);
lean_closure_set(v___f_247_, 0, v_toAdd_246_);
v___x_248_ = l_List_foldrTR___redArg(v___f_247_, v_toZero_245_, v_s_237_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object* v_N_249_, lean_object* v_i_250_, lean_object* v_s_251_, lean_object* v_f_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lp_mathlib_Multiset_map___redArg(v_f_252_, v_s_251_);
v___x_254_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13(v_N_249_, v_i_250_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9___lam__0(lean_object* v_v_255_, lean_object* v_w_256_, lean_object* v_toMul_257_, lean_object* v_i_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc(v_i_258_);
v___x_259_ = lean_apply_1(v_v_255_, v_i_258_);
v___x_260_ = lean_apply_1(v_w_256_, v_i_258_);
v___x_261_ = lean_apply_2(v_toMul_257_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9(lean_object* v___x_262_, lean_object* v_N_263_, lean_object* v_i_264_, lean_object* v_v_265_, lean_object* v_w_266_){
_start:
{
lean_object* v_instO_267_; lean_object* v___x_268_; lean_object* v_toSemiring_269_; lean_object* v___x_270_; lean_object* v_toNonUnitalNonAssocSemiring_271_; lean_object* v___x_272_; lean_object* v_toMul_273_; lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_instO_267_ = lean_ctor_get(v_N_263_, 9);
lean_inc_ref(v_instO_267_);
lean_inc(v_i_264_);
v___x_268_ = lean_apply_1(v_instO_267_, v_i_264_);
v_toSemiring_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref(v_toSemiring_269_);
lean_dec_ref(v___x_268_);
v___x_270_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_269_);
v_toNonUnitalNonAssocSemiring_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_toNonUnitalNonAssocSemiring_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v_toNonUnitalNonAssocSemiring_271_);
v_toMul_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_toMul_273_);
lean_dec_ref(v___x_272_);
v___f_274_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9___lam__0), 4, 3);
lean_closure_set(v___f_274_, 0, v_v_265_);
lean_closure_set(v___f_274_, 1, v_w_266_);
lean_closure_set(v___f_274_, 2, v_toMul_273_);
v___x_275_ = l_List_finRange(v___x_262_);
v___x_276_ = lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_N_263_, v_i_264_, v___x_275_, v___f_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg___lam__0(lean_object* v_M_277_, lean_object* v_x_278_, lean_object* v_j_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_apply_2(v_M_277_, v_x_278_, v_j_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg(lean_object* v_N_281_, lean_object* v_i_282_, lean_object* v___x_283_, lean_object* v_M_284_, lean_object* v_v_285_, lean_object* v_x_286_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_287_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg___lam__0), 3, 2);
lean_closure_set(v___f_287_, 0, v_M_284_);
lean_closure_set(v___f_287_, 1, v_x_286_);
v___x_288_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9(v___x_283_, v_N_281_, v_i_282_, v___f_287_, v_v_285_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5___redArg___lam__0(lean_object* v_N_289_, lean_object* v_i_290_, lean_object* v___x_291_, lean_object* v_M_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg(v_N_289_, v_i_290_, v___x_291_, v_M_292_, v___y_293_, v___y_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5___redArg(lean_object* v_N_296_, lean_object* v_i_297_, lean_object* v___x_298_){
_start:
{
lean_object* v___f_299_; 
v___f_299_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5___redArg___lam__0), 6, 3);
lean_closure_set(v___f_299_, 0, v_N_296_);
lean_closure_set(v___f_299_, 1, v_i_297_);
lean_closure_set(v___f_299_, 2, v___x_298_);
return v___f_299_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_N_300_, lean_object* v_i_301_, lean_object* v___x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg(v_N_300_, v_i_301_, v___x_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg(lean_object* v_N_307_, lean_object* v_i_308_, lean_object* v___x_309_){
_start:
{
lean_object* v_instO_310_; lean_object* v___x_311_; lean_object* v_toSemiring_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_toOne_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v_instO_310_ = lean_ctor_get(v_N_307_, 9);
lean_inc_ref(v_instO_310_);
lean_inc_n(v_i_308_, 2);
v___x_311_ = lean_apply_1(v_instO_310_, v_i_308_);
v_toSemiring_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_toSemiring_312_);
lean_dec_ref(v___x_311_);
v___x_313_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_312_);
v___x_314_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_313_);
v_toOne_315_ = lean_ctor_get(v___x_314_, 2);
lean_inc(v_toOne_315_);
lean_dec_ref(v___x_314_);
lean_inc_ref(v_N_307_);
v___f_316_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__0), 6, 3);
lean_closure_set(v___f_316_, 0, v_N_307_);
lean_closure_set(v___f_316_, 1, v_i_308_);
lean_closure_set(v___f_316_, 2, v___x_309_);
v___f_317_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3), 6, 3);
lean_closure_set(v___f_317_, 0, v_N_307_);
lean_closure_set(v___f_317_, 1, v_i_308_);
lean_closure_set(v___f_317_, 2, v_toOne_315_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___f_317_);
lean_ctor_set(v___x_318_, 1, v___f_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg(lean_object* v_N_320_, lean_object* v_i_321_, lean_object* v___x_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___f_323_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
lean_inc(v_i_321_);
lean_inc_ref(v_N_320_);
v___x_324_ = lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg(v_N_320_, v_i_321_, v___x_322_);
v___x_325_ = lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg(v_N_320_, v_i_321_, v___f_323_, v___f_323_, v___x_324_);
lean_dec(v_i_321_);
lean_dec_ref(v_N_320_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg___lam__0(lean_object* v_00_u03c1_326_, lean_object* v_N_327_, lean_object* v_i_328_, lean_object* v___x_329_, lean_object* v_g_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_333_; lean_object* v_val_334_; lean_object* v___x_335_; lean_object* v_toLinearMap_336_; lean_object* v___x_337_; 
v___x_333_ = lean_apply_1(v_00_u03c1_326_, v_g_330_);
v_val_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref(v___x_333_);
v___x_335_ = lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg(v_N_327_, v_i_328_, v___x_329_);
v_toLinearMap_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_toLinearMap_336_);
lean_dec_ref(v___x_335_);
v___x_337_ = lean_apply_3(v_toLinearMap_336_, v_val_334_, v___y_331_, v___y_332_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg(lean_object* v_N_338_, lean_object* v_i_339_, lean_object* v___x_340_, lean_object* v_00_u03c1_341_){
_start:
{
lean_object* v___f_342_; 
v___f_342_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg___lam__0), 7, 4);
lean_closure_set(v___f_342_, 0, v_00_u03c1_341_);
lean_closure_set(v___f_342_, 1, v_N_338_);
lean_closure_set(v___f_342_, 2, v_i_339_);
lean_closure_set(v___f_342_, 3, v___x_340_);
return v___f_342_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg(lean_object* v_R_343_, lean_object* v_H_344_, lean_object* v_N_345_, lean_object* v_i_346_, lean_object* v_00_u03c1_347_){
_start:
{
lean_object* v_chi_348_; lean_object* v___x_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___f_352_; lean_object* v___x_353_; 
v_chi_348_ = lean_ctor_get(v_N_345_, 19);
v___x_349_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_343_);
lean_inc_n(v_i_346_, 2);
lean_inc_ref(v_N_345_);
v___f_350_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg___lam__0), 7, 4);
lean_closure_set(v___f_350_, 0, v_00_u03c1_347_);
lean_closure_set(v___f_350_, 1, v_N_345_);
lean_closure_set(v___f_350_, 2, v_i_346_);
lean_closure_set(v___f_350_, 3, v___x_349_);
v___x_351_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_chi_348_);
v___f_352_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_352_, 0, v_chi_348_);
lean_closure_set(v___f_352_, 1, v_i_346_);
lean_closure_set(v___f_352_, 2, v___x_351_);
v___x_353_ = lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg(v_N_345_, v_i_346_, v___f_350_, v___f_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___boxed(lean_object* v_R_354_, lean_object* v_H_355_, lean_object* v_N_356_, lean_object* v_i_357_, lean_object* v_00_u03c1_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg(v_R_354_, v_H_355_, v_N_356_, v_i_357_, v_00_u03c1_358_);
lean_dec_ref(v_H_355_);
lean_dec_ref(v_R_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp(lean_object* v_R_360_, lean_object* v_H_361_, lean_object* v_what_u2082_362_, lean_object* v_N_363_, lean_object* v_i_364_, lean_object* v_00_u03c1_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg(v_R_360_, v_H_361_, v_N_363_, v_i_364_, v_00_u03c1_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_Wp___boxed(lean_object* v_R_367_, lean_object* v_H_368_, lean_object* v_what_u2082_369_, lean_object* v_N_370_, lean_object* v_i_371_, lean_object* v_00_u03c1_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = lp_tree_Formalism_MainNotions_N_Glob_Wp(v_R_367_, v_H_368_, v_what_u2082_369_, v_N_370_, v_i_371_, v_00_u03c1_372_);
lean_dec_ref(v_what_u2082_369_);
lean_dec_ref(v_H_368_);
lean_dec_ref(v_R_367_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0(lean_object* v_N_374_, lean_object* v_i_375_, lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v_00_u03c1_378_){
_start:
{
lean_object* v___f_379_; 
v___f_379_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg___lam__0), 7, 4);
lean_closure_set(v___f_379_, 0, v_00_u03c1_378_);
lean_closure_set(v___f_379_, 1, v_N_374_);
lean_closure_set(v___f_379_, 2, v_i_375_);
lean_closure_set(v___f_379_, 3, v___x_377_);
return v___f_379_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___boxed(lean_object* v_N_380_, lean_object* v_i_381_, lean_object* v___x_382_, lean_object* v___x_383_, lean_object* v_00_u03c1_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0(v_N_380_, v_i_381_, v___x_382_, v___x_383_, v_00_u03c1_384_);
lean_dec_ref(v___x_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0(lean_object* v_N_386_, lean_object* v_i_387_, lean_object* v___x_388_, lean_object* v_m_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg(v_N_386_, v_i_387_, v___x_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3(lean_object* v_N_391_, lean_object* v_i_392_, lean_object* v___x_393_, lean_object* v_m_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg(v_N_391_, v_i_392_, v___x_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_g_396_){
_start:
{
lean_inc(v_g_396_);
return v_g_396_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_g_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___redArg(v_g_397_);
lean_dec(v_g_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7(lean_object* v_m_399_, lean_object* v_N_400_, lean_object* v_i_401_, lean_object* v_00_u03c3_402_, lean_object* v_00_u03c3_x27_403_, lean_object* v_inst_404_, lean_object* v_f_405_, lean_object* v_g_406_, lean_object* v_h_u2081_407_, lean_object* v_h_u2082_408_){
_start:
{
lean_inc(v_g_406_);
return v_g_406_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_m_409_, lean_object* v_N_410_, lean_object* v_i_411_, lean_object* v_00_u03c3_412_, lean_object* v_00_u03c3_x27_413_, lean_object* v_inst_414_, lean_object* v_f_415_, lean_object* v_g_416_, lean_object* v_h_u2081_417_, lean_object* v_h_u2082_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__7(v_m_409_, v_N_410_, v_i_411_, v_00_u03c3_412_, v_00_u03c3_x27_413_, v_inst_414_, v_f_415_, v_g_416_, v_h_u2081_417_, v_h_u2082_418_);
lean_dec(v_g_416_);
lean_dec(v_f_415_);
lean_dec(v_00_u03c3_x27_413_);
lean_dec(v_00_u03c3_412_);
lean_dec(v_i_411_);
lean_dec_ref(v_N_410_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4(lean_object* v_m_420_, lean_object* v_N_421_, lean_object* v_i_422_, lean_object* v_00_u03c3_423_, lean_object* v_00_u03c3_x27_424_, lean_object* v_re_u2081_425_, lean_object* v_re_u2082_426_, lean_object* v_e_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___redArg(v_N_421_, v_i_422_, v_00_u03c3_423_, v_00_u03c3_x27_424_, v_e_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4___boxed(lean_object* v_m_429_, lean_object* v_N_430_, lean_object* v_i_431_, lean_object* v_00_u03c3_432_, lean_object* v_00_u03c3_x27_433_, lean_object* v_re_u2081_434_, lean_object* v_re_u2082_435_, lean_object* v_e_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = lp_tree_LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4(v_m_429_, v_N_430_, v_i_431_, v_00_u03c3_432_, v_00_u03c3_x27_433_, v_re_u2081_434_, v_re_u2082_435_, v_e_436_);
lean_dec(v_00_u03c3_x27_433_);
lean_dec(v_00_u03c3_432_);
lean_dec(v_i_431_);
lean_dec_ref(v_N_430_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4(lean_object* v_N_438_, lean_object* v_i_439_, lean_object* v___x_440_, lean_object* v_i_441_, lean_object* v_x_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___redArg(v_N_438_, v_i_439_, v_i_441_, v_x_442_, v_a_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_N_445_, lean_object* v_i_446_, lean_object* v___x_447_, lean_object* v_i_448_, lean_object* v_x_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__4(v_N_445_, v_i_446_, v___x_447_, v_i_448_, v_x_449_, v_a_450_);
lean_dec(v_x_449_);
lean_dec(v_i_448_);
lean_dec(v___x_447_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5(lean_object* v_N_452_, lean_object* v_i_453_, lean_object* v___x_454_, lean_object* v_m_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v___f_459_; 
v___f_459_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5___redArg___lam__0), 6, 3);
lean_closure_set(v___f_459_, 0, v_N_452_);
lean_closure_set(v___f_459_, 1, v_i_453_);
lean_closure_set(v___f_459_, 2, v___x_454_);
return v___f_459_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10(lean_object* v_N_460_, lean_object* v_i_461_, lean_object* v_m_462_, lean_object* v_00_u03c3_463_, lean_object* v_00_u03c3_x27_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_self_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_self_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___boxed(lean_object* v_N_469_, lean_object* v_i_470_, lean_object* v_m_471_, lean_object* v_00_u03c3_472_, lean_object* v_00_u03c3_x27_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_self_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10(v_N_469_, v_i_470_, v_m_471_, v_00_u03c3_472_, v_00_u03c3_x27_473_, v_inst_474_, v_inst_475_, v_self_476_);
lean_dec(v_00_u03c3_x27_473_);
lean_dec(v_00_u03c3_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_N_469_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_N_478_, lean_object* v_i_479_, lean_object* v_00_u03c3_480_, lean_object* v_00_u03c3_x27_481_, lean_object* v_e_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_e_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_N_484_, lean_object* v_i_485_, lean_object* v_00_u03c3_486_, lean_object* v_00_u03c3_x27_487_, lean_object* v_e_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___redArg(v_N_484_, v_i_485_, v_00_u03c3_486_, v_00_u03c3_x27_487_, v_e_488_);
lean_dec(v_00_u03c3_x27_487_);
lean_dec(v_00_u03c3_486_);
lean_dec(v_i_485_);
lean_dec_ref(v_N_484_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8(lean_object* v_m_490_, lean_object* v_N_491_, lean_object* v_i_492_, lean_object* v_00_u03c3_493_, lean_object* v_00_u03c3_x27_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_e_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_e_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8___boxed(lean_object* v_m_499_, lean_object* v_N_500_, lean_object* v_i_501_, lean_object* v_00_u03c3_502_, lean_object* v_00_u03c3_x27_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_e_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__4_spec__8(v_m_499_, v_N_500_, v_i_501_, v_00_u03c3_502_, v_00_u03c3_x27_503_, v_inst_504_, v_inst_505_, v_e_506_);
lean_dec(v_00_u03c3_x27_503_);
lean_dec(v_00_u03c3_502_);
lean_dec(v_i_501_);
lean_dec_ref(v_N_500_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6(lean_object* v_N_508_, lean_object* v_i_509_, lean_object* v___x_510_, lean_object* v_m_511_, lean_object* v_M_512_, lean_object* v_v_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg(v_N_508_, v_i_509_, v___x_510_, v_M_512_, v_v_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object* v_N_516_, lean_object* v_i_517_, lean_object* v_00_u03b9_518_, lean_object* v_s_519_, lean_object* v_f_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_N_516_, v_i_517_, v_s_519_, v_f_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv___redArg(lean_object* v_R_522_, lean_object* v_N_523_, lean_object* v_i_524_, lean_object* v_r_525_){
_start:
{
lean_object* v_chi_526_; lean_object* v___x_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v_chi_526_ = lean_ctor_get(v_N_523_, 19);
v___x_527_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_522_);
lean_inc_n(v_i_524_, 2);
lean_inc_ref(v_N_523_);
v___f_528_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0___redArg___lam__0), 7, 4);
lean_closure_set(v___f_528_, 0, v_r_525_);
lean_closure_set(v___f_528_, 1, v_N_523_);
lean_closure_set(v___f_528_, 2, v_i_524_);
lean_closure_set(v___f_528_, 3, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_chi_526_);
v___f_530_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_530_, 0, v_chi_526_);
lean_closure_set(v___f_530_, 1, v_i_524_);
lean_closure_set(v___f_530_, 2, v___x_529_);
v___x_531_ = lp_tree_Formalism_MainNotions_N_twistRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__2___redArg(v_N_523_, v_i_524_, v___f_528_, v___f_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv___redArg___boxed(lean_object* v_R_532_, lean_object* v_N_533_, lean_object* v_i_534_, lean_object* v_r_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = lp_tree_Formalism_MainNotions_N_Glob_rChiInv___redArg(v_R_532_, v_N_533_, v_i_534_, v_r_535_);
lean_dec_ref(v_R_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv(lean_object* v_R_537_, lean_object* v_H_538_, lean_object* v_what_u2082_539_, lean_object* v_N_540_, lean_object* v_i_541_, lean_object* v_r_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lp_tree_Formalism_MainNotions_N_Glob_rChiInv___redArg(v_R_537_, v_N_540_, v_i_541_, v_r_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Glob_rChiInv___boxed(lean_object* v_R_544_, lean_object* v_H_545_, lean_object* v_what_u2082_546_, lean_object* v_N_547_, lean_object* v_i_548_, lean_object* v_r_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = lp_tree_Formalism_MainNotions_N_Glob_rChiInv(v_R_544_, v_H_545_, v_what_u2082_546_, v_N_547_, v_i_548_, v_r_549_);
lean_dec_ref(v_what_u2082_546_);
lean_dec_ref(v_H_545_);
lean_dec_ref(v_R_544_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___redArg(lean_object* v_inst_551_, lean_object* v_k_552_, lean_object* v_M_553_){
_start:
{
lean_object* v_toSemiring_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_toFun_558_; lean_object* v___f_559_; 
v_toSemiring_554_ = lean_ctor_get(v_inst_551_, 0);
lean_inc_ref(v_toSemiring_554_);
lean_dec_ref(v_inst_551_);
lean_inc(v_k_552_);
v___x_555_ = l_List_finRange(v_k_552_);
v___x_556_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_556_, 0, v_k_552_);
v___x_557_ = lp_mathlib_Matrix_toLinAlgEquiv_x27___redArg(v_toSemiring_554_, v___x_556_, v___x_555_);
v_toFun_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_toFun_558_);
lean_dec_ref(v___x_557_);
v___f_559_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_559_, 0, v_M_553_);
lean_closure_set(v___f_559_, 1, v_toFun_558_);
return v___f_559_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep(lean_object* v_Kf_560_, lean_object* v_inst_561_, lean_object* v_00_u0393_562_, lean_object* v_inst_563_, lean_object* v_k_564_, lean_object* v_M_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lp_tree_Formalism_MainNotions_N_matRep___redArg(v_inst_561_, v_k_564_, v_M_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___boxed(lean_object* v_Kf_567_, lean_object* v_inst_568_, lean_object* v_00_u0393_569_, lean_object* v_inst_570_, lean_object* v_k_571_, lean_object* v_M_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = lp_tree_Formalism_MainNotions_N_matRep(v_Kf_567_, v_inst_568_, v_00_u0393_569_, v_inst_570_, v_k_571_, v_M_572_);
lean_dec_ref(v_inst_570_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___redArg___lam__0(lean_object* v_00_u03c7_574_, lean_object* v_M_575_, lean_object* v_toMul_576_, lean_object* v_g_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_580_; lean_object* v_val_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc(v_g_577_);
v___x_580_ = lean_apply_1(v_00_u03c7_574_, v_g_577_);
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v___x_580_);
v___x_582_ = lean_apply_3(v_M_575_, v_g_577_, v___y_578_, v___y_579_);
v___x_583_ = lean_apply_2(v_toMul_576_, v_val_581_, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___redArg(lean_object* v_inst_584_, lean_object* v_M_585_, lean_object* v_00_u03c7_586_){
_start:
{
lean_object* v_toSemiring_587_; lean_object* v___x_588_; lean_object* v_toMul_589_; lean_object* v___f_590_; 
v_toSemiring_587_ = lean_ctor_get(v_inst_584_, 0);
lean_inc_ref(v_toSemiring_587_);
lean_dec_ref(v_inst_584_);
v___x_588_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_587_);
v_toMul_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_toMul_589_);
lean_dec_ref(v___x_588_);
v___f_590_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_twistM___redArg___lam__0), 6, 3);
lean_closure_set(v___f_590_, 0, v_00_u03c7_586_);
lean_closure_set(v___f_590_, 1, v_M_585_);
lean_closure_set(v___f_590_, 2, v_toMul_589_);
return v___f_590_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM(lean_object* v_Kf_591_, lean_object* v_inst_592_, lean_object* v_00_u0393_593_, lean_object* v_inst_594_, lean_object* v_k_595_, lean_object* v_M_596_, lean_object* v_00_u03c7_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lp_tree_Formalism_MainNotions_N_twistM___redArg(v_inst_592_, v_M_596_, v_00_u03c7_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___boxed(lean_object* v_Kf_599_, lean_object* v_inst_600_, lean_object* v_00_u0393_601_, lean_object* v_inst_602_, lean_object* v_k_603_, lean_object* v_M_604_, lean_object* v_00_u03c7_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = lp_tree_Formalism_MainNotions_N_twistM(v_Kf_599_, v_inst_600_, v_00_u0393_601_, v_inst_602_, v_k_603_, v_M_604_, v_00_u03c7_605_);
lean_dec(v_k_603_);
lean_dec_ref(v_inst_602_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___redArg(lean_object* v_f_607_, lean_object* v_M_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___f_610_; 
v___x_609_ = lp_mathlib_RingHom_mapMatrix___redArg(v_f_607_);
v___f_610_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_610_, 0, v_M_608_);
lean_closure_set(v___f_610_, 1, v___x_609_);
return v___f_610_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM(lean_object* v_Kf_611_, lean_object* v_inst_612_, lean_object* v_00_u0393_613_, lean_object* v_inst_614_, lean_object* v_k_615_, lean_object* v_S_616_, lean_object* v_inst_617_, lean_object* v_f_618_, lean_object* v_M_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lp_tree_Formalism_MainNotions_N_mapM___redArg(v_f_618_, v_M_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___boxed(lean_object* v_Kf_621_, lean_object* v_inst_622_, lean_object* v_00_u0393_623_, lean_object* v_inst_624_, lean_object* v_k_625_, lean_object* v_S_626_, lean_object* v_inst_627_, lean_object* v_f_628_, lean_object* v_M_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = lp_tree_Formalism_MainNotions_N_mapM(v_Kf_621_, v_inst_622_, v_00_u0393_623_, v_inst_624_, v_k_625_, v_S_626_, v_inst_627_, v_f_628_, v_M_629_);
lean_dec_ref(v_inst_627_);
lean_dec(v_k_625_);
lean_dec_ref(v_inst_624_);
lean_dec_ref(v_inst_622_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___redArg___lam__0(lean_object* v_toInv_631_, lean_object* v_M_632_, lean_object* v_g_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_apply_1(v_toInv_631_, v_g_633_);
v___x_637_ = lean_apply_1(v_M_632_, v___x_636_);
v___x_638_ = lp_mathlib_Matrix_transpose___redArg(v___x_637_, v___y_634_, v___y_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___redArg(lean_object* v_inst_639_, lean_object* v_M_640_){
_start:
{
lean_object* v___x_641_; lean_object* v_toInv_642_; lean_object* v___f_643_; 
v___x_641_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_639_);
v_toInv_642_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_toInv_642_);
lean_dec_ref(v___x_641_);
v___f_643_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_dualM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_643_, 0, v_toInv_642_);
lean_closure_set(v___f_643_, 1, v_M_640_);
return v___f_643_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___redArg___boxed(lean_object* v_inst_644_, lean_object* v_M_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = lp_tree_Formalism_MainNotions_N_dualM___redArg(v_inst_644_, v_M_645_);
lean_dec_ref(v_inst_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM(lean_object* v_Kf_647_, lean_object* v_inst_648_, lean_object* v_00_u0393_649_, lean_object* v_inst_650_, lean_object* v_k_651_, lean_object* v_M_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = lp_tree_Formalism_MainNotions_N_dualM___redArg(v_inst_650_, v_M_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_dualM___boxed(lean_object* v_Kf_654_, lean_object* v_inst_655_, lean_object* v_00_u0393_656_, lean_object* v_inst_657_, lean_object* v_k_658_, lean_object* v_M_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = lp_tree_Formalism_MainNotions_N_dualM(v_Kf_654_, v_inst_655_, v_00_u0393_656_, v_inst_657_, v_k_658_, v_M_659_);
lean_dec(v_k_658_);
lean_dec_ref(v_inst_657_);
lean_dec_ref(v_inst_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Z1urD(lean_object* v_G_661_, lean_object* v_inst_662_, lean_object* v_LL_663_, lean_object* v_inst_664_, lean_object* v_O_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_V_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_00_u03c1_673_, lean_object* v_L_674_, lean_object* v_I_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Z1urD___boxed(lean_object* v_G_677_, lean_object* v_inst_678_, lean_object* v_LL_679_, lean_object* v_inst_680_, lean_object* v_O_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_V_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_00_u03c1_689_, lean_object* v_L_690_, lean_object* v_I_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = lp_tree_Formalism_MainNotions_N_Z1urD(v_G_677_, v_inst_678_, v_LL_679_, v_inst_680_, v_O_681_, v_inst_682_, v_inst_683_, v_V_684_, v_inst_685_, v_inst_686_, v_inst_687_, v_inst_688_, v_00_u03c1_689_, v_L_690_, v_I_691_);
lean_dec(v_00_u03c1_689_);
lean_dec(v_inst_687_);
lean_dec(v_inst_686_);
lean_dec_ref(v_inst_685_);
lean_dec_ref(v_inst_683_);
lean_dec_ref(v_inst_682_);
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_678_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw___redArg(lean_object* v_PD_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_e_696_, lean_object* v_g_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_toSemiring_700_; lean_object* v_toMonoid_701_; lean_object* v_toNPow_702_; lean_object* v_algebraMap_703_; lean_object* v_00_u03c7_704_; lean_object* v___x_705_; lean_object* v_inv_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_698_ = lp_mathlib_Field_toSemifield___redArg(v_inst_694_);
v___x_699_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_698_);
v_toSemiring_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_toSemiring_700_);
lean_dec_ref(v___x_699_);
v_toMonoid_701_ = lean_ctor_get(v_toSemiring_700_, 1);
lean_inc_ref(v_toMonoid_701_);
lean_dec_ref(v_toSemiring_700_);
v_toNPow_702_ = lean_ctor_get(v_toMonoid_701_, 2);
lean_inc(v_toNPow_702_);
lean_dec_ref(v_toMonoid_701_);
v_algebraMap_703_ = lean_ctor_get(v_inst_695_, 1);
lean_inc(v_algebraMap_703_);
lean_dec_ref(v_inst_695_);
v_00_u03c7_704_ = lean_ctor_get(v_PD_693_, 7);
lean_inc_ref(v_00_u03c7_704_);
lean_dec_ref(v_PD_693_);
v___x_705_ = lean_apply_1(v_00_u03c7_704_, v_g_697_);
v_inv_706_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_inv_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = lean_apply_1(v_algebraMap_703_, v_inv_706_);
v___x_708_ = lean_apply_2(v_toNPow_702_, v_e_696_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw___redArg___boxed(lean_object* v_PD_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_e_712_, lean_object* v_g_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = lp_tree_Formalism_MainNotions_N_epsTw___redArg(v_PD_709_, v_inst_710_, v_inst_711_, v_e_712_, v_g_713_);
lean_dec_ref(v_inst_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw(lean_object* v_G_715_, lean_object* v_inst_716_, lean_object* v_Qp_717_, lean_object* v_K_u2080_718_, lean_object* v_K_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_B_727_, lean_object* v_BdR_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_PD_740_, lean_object* v_LL_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_e_744_, lean_object* v_g_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lp_tree_Formalism_MainNotions_N_epsTw___redArg(v_PD_740_, v_inst_742_, v_inst_743_, v_e_744_, v_g_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_epsTw___boxed(lean_object** _args){
lean_object* v_G_749_ = _args[0];
lean_object* v_inst_750_ = _args[1];
lean_object* v_Qp_751_ = _args[2];
lean_object* v_K_u2080_752_ = _args[3];
lean_object* v_K_753_ = _args[4];
lean_object* v_inst_754_ = _args[5];
lean_object* v_inst_755_ = _args[6];
lean_object* v_inst_756_ = _args[7];
lean_object* v_inst_757_ = _args[8];
lean_object* v_inst_758_ = _args[9];
lean_object* v_inst_759_ = _args[10];
lean_object* v_inst_760_ = _args[11];
lean_object* v_B_761_ = _args[12];
lean_object* v_BdR_762_ = _args[13];
lean_object* v_inst_763_ = _args[14];
lean_object* v_inst_764_ = _args[15];
lean_object* v_inst_765_ = _args[16];
lean_object* v_inst_766_ = _args[17];
lean_object* v_inst_767_ = _args[18];
lean_object* v_inst_768_ = _args[19];
lean_object* v_inst_769_ = _args[20];
lean_object* v_inst_770_ = _args[21];
lean_object* v_inst_771_ = _args[22];
lean_object* v_inst_772_ = _args[23];
lean_object* v_inst_773_ = _args[24];
lean_object* v_PD_774_ = _args[25];
lean_object* v_LL_775_ = _args[26];
lean_object* v_inst_776_ = _args[27];
lean_object* v_inst_777_ = _args[28];
lean_object* v_e_778_ = _args[29];
lean_object* v_g_779_ = _args[30];
lean_object* v_x_780_ = _args[31];
lean_object* v_x_781_ = _args[32];
_start:
{
lean_object* v_res_782_; 
v_res_782_ = lp_tree_Formalism_MainNotions_N_epsTw(v_G_749_, v_inst_750_, v_Qp_751_, v_K_u2080_752_, v_K_753_, v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v_inst_758_, v_inst_759_, v_inst_760_, v_B_761_, v_BdR_762_, v_inst_763_, v_inst_764_, v_inst_765_, v_inst_766_, v_inst_767_, v_inst_768_, v_inst_769_, v_inst_770_, v_inst_771_, v_inst_772_, v_inst_773_, v_PD_774_, v_LL_775_, v_inst_776_, v_inst_777_, v_e_778_, v_g_779_, v_x_780_, v_x_781_);
lean_dec(v_x_781_);
lean_dec(v_x_780_);
lean_dec_ref(v_inst_776_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_769_);
lean_dec_ref(v_inst_768_);
lean_dec_ref(v_inst_766_);
lean_dec_ref(v_inst_765_);
lean_dec_ref(v_inst_764_);
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_759_);
lean_dec_ref(v_inst_758_);
lean_dec_ref(v_inst_757_);
lean_dec_ref(v_inst_756_);
lean_dec_ref(v_inst_755_);
lean_dec_ref(v_inst_754_);
lean_dec_ref(v_inst_750_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_decS(lean_object* v_R_784_, lean_object* v_H_785_, lean_object* v_what_u2082_786_, lean_object* v_N_787_, lean_object* v_w_788_){
_start:
{
lean_object* v___f_789_; 
v___f_789_ = ((lean_object*)(lp_tree_Formalism_MainNotions_N_decS___closed__0));
return v___f_789_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_decS___boxed(lean_object* v_R_790_, lean_object* v_H_791_, lean_object* v_what_u2082_792_, lean_object* v_N_793_, lean_object* v_w_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = lp_tree_Formalism_MainNotions_N_decS(v_R_790_, v_H_791_, v_what_u2082_792_, v_N_793_, v_w_794_);
lean_dec_ref(v_N_793_);
lean_dec_ref(v_what_u2082_792_);
lean_dec_ref(v_H_791_);
lean_dec_ref(v_R_790_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___lam__0(lean_object* v_self_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_apply_1(v_self_796_, v___y_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1(lean_object* v_N_800_, lean_object* v_i_801_, lean_object* v_S_802_){
_start:
{
lean_object* v___f_803_; 
v___f_803_ = ((lean_object*)(lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___closed__0));
return v___f_803_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___boxed(lean_object* v_N_804_, lean_object* v_i_805_, lean_object* v_S_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1(v_N_804_, v_i_805_, v_S_806_);
lean_dec(v_i_805_);
lean_dec_ref(v_N_804_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg___lam__0(lean_object* v_i_808_, lean_object* v_g_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = lean_apply_1(v_g_809_, v_i_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg(lean_object* v_i_811_){
_start:
{
lean_object* v___f_812_; 
v___f_812_ = lean_alloc_closure((void*)(lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_812_, 0, v_i_811_);
return v___f_812_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0(lean_object* v_N_813_, lean_object* v_i_814_, lean_object* v_i_815_){
_start:
{
lean_object* v___f_816_; 
v___f_816_ = lean_alloc_closure((void*)(lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_816_, 0, v_i_815_);
return v___f_816_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0___boxed(lean_object* v_N_817_, lean_object* v_i_818_, lean_object* v_i_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = lp_tree_Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0(v_N_817_, v_i_818_, v_i_819_);
lean_dec(v_i_818_);
lean_dec_ref(v_N_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT___redArg(lean_object* v_N_821_, lean_object* v_i_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___f_826_; 
v___f_824_ = lean_alloc_closure((void*)(lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_824_, 0, v_x_823_);
v___f_825_ = ((lean_object*)(lp_tree_Subalgebra_val___at___00Formalism_MainNotions_N_evT_spec__1___closed__0));
v___f_826_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_826_, 0, v___f_825_);
lean_closure_set(v___f_826_, 1, v___f_824_);
return v___f_826_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT___redArg___boxed(lean_object* v_N_827_, lean_object* v_i_828_, lean_object* v_x_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = lp_tree_Formalism_MainNotions_N_evT___redArg(v_N_827_, v_i_828_, v_x_829_);
lean_dec(v_i_828_);
lean_dec_ref(v_N_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT(lean_object* v_R_831_, lean_object* v_H_832_, lean_object* v_what_u2082_833_, lean_object* v_N_834_, lean_object* v_i_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lp_tree_Formalism_MainNotions_N_evT___redArg(v_N_834_, v_i_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_evT___boxed(lean_object* v_R_838_, lean_object* v_H_839_, lean_object* v_what_u2082_840_, lean_object* v_N_841_, lean_object* v_i_842_, lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = lp_tree_Formalism_MainNotions_N_evT(v_R_838_, v_H_839_, v_what_u2082_840_, v_N_841_, v_i_842_, v_x_843_);
lean_dec(v_i_842_);
lean_dec_ref(v_N_841_);
lean_dec_ref(v_what_u2082_840_);
lean_dec_ref(v_H_839_);
lean_dec_ref(v_R_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0(lean_object* v_N_845_, lean_object* v_i_846_, lean_object* v_i_847_){
_start:
{
lean_object* v___f_848_; 
v___f_848_ = lean_alloc_closure((void*)(lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_848_, 0, v_i_847_);
return v___f_848_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0___boxed(lean_object* v_N_849_, lean_object* v_i_850_, lean_object* v_i_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = lp_tree_Pi_evalMonoidHom___at___00Pi_evalRingHom___at___00Formalism_MainNotions_N_evT_spec__0_spec__0(v_N_849_, v_i_850_, v_i_851_);
lean_dec(v_i_850_);
lean_dec_ref(v_N_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___redArg___lam__0(lean_object* v_f_853_, lean_object* v_h_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_apply_1(v_h_854_, v___y_855_);
v___x_857_ = lean_apply_1(v_f_853_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___redArg(lean_object* v_f_858_){
_start:
{
lean_object* v___f_859_; 
v___f_859_ = lean_alloc_closure((void*)(lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_859_, 0, v_f_858_);
return v___f_859_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1(lean_object* v_N_860_, lean_object* v_i_861_, lean_object* v___x_862_, lean_object* v_f_863_, lean_object* v_I_864_){
_start:
{
lean_object* v___f_865_; 
v___f_865_ = lean_alloc_closure((void*)(lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_865_, 0, v_f_863_);
return v___f_865_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1___boxed(lean_object* v_N_866_, lean_object* v_i_867_, lean_object* v___x_868_, lean_object* v_f_869_, lean_object* v_I_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = lp_tree_LinearMap_compLeft___at___00Formalism_MainNotions_N_stdO_spec__1(v_N_866_, v_i_867_, v___x_868_, v_f_869_, v_I_870_);
lean_dec(v_i_867_);
lean_dec_ref(v_N_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__2(lean_object* v_N_872_, lean_object* v_i_873_, lean_object* v___x_874_, lean_object* v_00_u03c3_u2081_u2082_875_, lean_object* v_inst_876_, lean_object* v_f_877_, lean_object* v_p_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = lean_box(0);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__2___boxed(lean_object* v_N_880_, lean_object* v_i_881_, lean_object* v___x_882_, lean_object* v_00_u03c3_u2081_u2082_883_, lean_object* v_inst_884_, lean_object* v_f_885_, lean_object* v_p_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__2(v_N_880_, v_i_881_, v___x_882_, v_00_u03c3_u2081_u2082_883_, v_inst_884_, v_f_885_, v_p_886_);
lean_dec(v_f_885_);
lean_dec(v_00_u03c3_u2081_u2082_883_);
lean_dec(v_i_881_);
lean_dec_ref(v_N_880_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__3(lean_object* v_N_888_, lean_object* v_i_889_, lean_object* v___x_890_, lean_object* v_p_891_, lean_object* v_s_892_, lean_object* v_hs_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__3___boxed(lean_object* v_N_895_, lean_object* v_i_896_, lean_object* v___x_897_, lean_object* v_p_898_, lean_object* v_s_899_, lean_object* v_hs_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2_spec__3(v_N_895_, v_i_896_, v___x_897_, v_p_898_, v_s_899_, v_hs_900_);
lean_dec(v_i_896_);
lean_dec_ref(v_N_895_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___redArg(lean_object* v_N_902_, lean_object* v_i_903_, lean_object* v___x_904_, lean_object* v_00_u03c4_u2081_u2082_905_, lean_object* v_f_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_box(0);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___redArg___boxed(lean_object* v_N_908_, lean_object* v_i_909_, lean_object* v___x_910_, lean_object* v_00_u03c4_u2081_u2082_911_, lean_object* v_f_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___redArg(v_N_908_, v_i_909_, v___x_910_, v_00_u03c4_u2081_u2082_911_, v_f_912_);
lean_dec(v_f_912_);
lean_dec(v_00_u03c4_u2081_u2082_911_);
lean_dec(v_i_909_);
lean_dec_ref(v_N_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0(lean_object* v_toOne_914_, lean_object* v_r_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_r_915_);
lean_ctor_set(v___x_916_, 1, v_toOne_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg(lean_object* v_N_917_, lean_object* v_i_918_){
_start:
{
lean_object* v_instO_919_; lean_object* v___x_920_; lean_object* v_toSemiring_921_; lean_object* v_toMonoid_922_; lean_object* v___x_923_; lean_object* v_toOne_924_; lean_object* v___f_925_; lean_object* v___f_926_; lean_object* v___f_927_; 
v_instO_919_ = lean_ctor_get(v_N_917_, 9);
lean_inc_ref(v_instO_919_);
lean_dec_ref(v_N_917_);
v___x_920_ = lean_apply_1(v_instO_919_, v_i_918_);
v_toSemiring_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_toSemiring_921_);
lean_dec_ref(v___x_920_);
v_toMonoid_922_ = lean_ctor_get(v_toSemiring_921_, 1);
lean_inc_ref(v_toMonoid_922_);
lean_dec_ref(v_toSemiring_921_);
v___x_923_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_922_);
lean_dec_ref(v_toMonoid_922_);
v_toOne_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_toOne_924_);
lean_dec_ref(v___x_923_);
v___f_925_ = lean_alloc_closure((void*)(lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_925_, 0, v_toOne_924_);
v___f_926_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
v___f_927_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_927_, 0, v___f_926_);
lean_closure_set(v___f_927_, 1, v___f_925_);
return v___f_927_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO___redArg(lean_object* v_N_928_, lean_object* v_i_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_box(0);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO___redArg___boxed(lean_object* v_N_931_, lean_object* v_i_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = lp_tree_Formalism_MainNotions_N_stdO___redArg(v_N_931_, v_i_932_);
lean_dec(v_i_932_);
lean_dec_ref(v_N_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO(lean_object* v_R_934_, lean_object* v_H_935_, lean_object* v_what_u2082_936_, lean_object* v_N_937_, lean_object* v_i_938_, lean_object* v_k_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdO___boxed(lean_object* v_R_941_, lean_object* v_H_942_, lean_object* v_what_u2082_943_, lean_object* v_N_944_, lean_object* v_i_945_, lean_object* v_k_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = lp_tree_Formalism_MainNotions_N_stdO(v_R_941_, v_H_942_, v_what_u2082_943_, v_N_944_, v_i_945_, v_k_946_);
lean_dec(v_k_946_);
lean_dec(v_i_945_);
lean_dec_ref(v_N_944_);
lean_dec_ref(v_what_u2082_943_);
lean_dec_ref(v_H_942_);
lean_dec_ref(v_R_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0(lean_object* v_N_948_, lean_object* v_i_949_, lean_object* v___x_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg(v_N_948_, v_i_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2(lean_object* v_N_952_, lean_object* v_i_953_, lean_object* v___x_954_, lean_object* v_00_u03c4_u2081_u2082_955_, lean_object* v_inst_956_, lean_object* v_f_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_box(0);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2___boxed(lean_object* v_N_959_, lean_object* v_i_960_, lean_object* v___x_961_, lean_object* v_00_u03c4_u2081_u2082_962_, lean_object* v_inst_963_, lean_object* v_f_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_stdO_spec__2(v_N_959_, v_i_960_, v___x_961_, v_00_u03c4_u2081_u2082_962_, v_inst_963_, v_f_964_);
lean_dec(v_f_964_);
lean_dec(v_00_u03c4_u2081_u2082_962_);
lean_dec(v_i_960_);
lean_dec_ref(v_N_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiU___redArg(lean_object* v_N_966_, lean_object* v_i_967_, lean_object* v_c_968_){
_start:
{
lean_object* v_chi_969_; lean_object* v___x_970_; 
v_chi_969_ = lean_ctor_get(v_N_966_, 19);
lean_inc_ref(v_chi_969_);
lean_dec_ref(v_N_966_);
v___x_970_ = lean_apply_2(v_chi_969_, v_i_967_, v_c_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiU(lean_object* v_R_971_, lean_object* v_H_972_, lean_object* v_what_u2082_973_, lean_object* v_N_974_, lean_object* v_i_975_, lean_object* v_c_976_){
_start:
{
lean_object* v_chi_977_; lean_object* v___x_978_; 
v_chi_977_ = lean_ctor_get(v_N_974_, 19);
lean_inc_ref(v_chi_977_);
lean_dec_ref(v_N_974_);
v___x_978_ = lean_apply_2(v_chi_977_, v_i_975_, v_c_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiU___boxed(lean_object* v_R_979_, lean_object* v_H_980_, lean_object* v_what_u2082_981_, lean_object* v_N_982_, lean_object* v_i_983_, lean_object* v_c_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = lp_tree_Formalism_MainNotions_N_chiU(v_R_979_, v_H_980_, v_what_u2082_981_, v_N_982_, v_i_983_, v_c_984_);
lean_dec_ref(v_what_u2082_981_);
lean_dec_ref(v_H_980_);
lean_dec_ref(v_R_979_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_toK___redArg(lean_object* v_N_986_, lean_object* v_i_987_){
_start:
{
lean_object* v_instO_988_; lean_object* v___x_989_; lean_object* v_toSemiring_990_; lean_object* v_toMonoid_991_; lean_object* v___x_992_; lean_object* v_toOne_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; 
v_instO_988_ = lean_ctor_get(v_N_986_, 9);
lean_inc_ref(v_instO_988_);
lean_dec_ref(v_N_986_);
v___x_989_ = lean_apply_1(v_instO_988_, v_i_987_);
v_toSemiring_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc_ref(v_toSemiring_990_);
lean_dec_ref(v___x_989_);
v_toMonoid_991_ = lean_ctor_get(v_toSemiring_990_, 1);
lean_inc_ref(v_toMonoid_991_);
lean_dec_ref(v_toSemiring_990_);
v___x_992_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_991_);
lean_dec_ref(v_toMonoid_991_);
v_toOne_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_toOne_993_);
lean_dec_ref(v___x_992_);
v___f_994_ = lean_alloc_closure((void*)(lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_994_, 0, v_toOne_993_);
v___f_995_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
v___f_996_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_996_, 0, v___f_995_);
lean_closure_set(v___f_996_, 1, v___f_994_);
return v___f_996_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_toK(lean_object* v_R_997_, lean_object* v_H_998_, lean_object* v_what_u2082_999_, lean_object* v_N_1000_, lean_object* v_i_1001_){
_start:
{
lean_object* v_instO_1002_; lean_object* v___x_1003_; lean_object* v_toSemiring_1004_; lean_object* v_toMonoid_1005_; lean_object* v___x_1006_; lean_object* v_toOne_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; 
v_instO_1002_ = lean_ctor_get(v_N_1000_, 9);
lean_inc_ref(v_instO_1002_);
lean_dec_ref(v_N_1000_);
v___x_1003_ = lean_apply_1(v_instO_1002_, v_i_1001_);
v_toSemiring_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_toSemiring_1004_);
lean_dec_ref(v___x_1003_);
v_toMonoid_1005_ = lean_ctor_get(v_toSemiring_1004_, 1);
lean_inc_ref(v_toMonoid_1005_);
lean_dec_ref(v_toSemiring_1004_);
v___x_1006_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1005_);
lean_dec_ref(v_toMonoid_1005_);
v_toOne_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_toOne_1007_);
lean_dec_ref(v___x_1006_);
v___f_1008_ = lean_alloc_closure((void*)(lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1008_, 0, v_toOne_1007_);
v___f_1009_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
v___f_1010_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1010_, 0, v___f_1009_);
lean_closure_set(v___f_1010_, 1, v___f_1008_);
return v___f_1010_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_toK___boxed(lean_object* v_R_1011_, lean_object* v_H_1012_, lean_object* v_what_u2082_1013_, lean_object* v_N_1014_, lean_object* v_i_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = lp_tree_Formalism_MainNotions_N_toK(v_R_1011_, v_H_1012_, v_what_u2082_1013_, v_N_1014_, v_i_1015_);
lean_dec_ref(v_what_u2082_1013_);
lean_dec_ref(v_H_1012_);
lean_dec_ref(v_R_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___lam__0(lean_object* v_self_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_val_1020_; lean_object* v___x_1021_; 
v_val_1020_ = lean_ctor_get(v_self_1017_, 0);
lean_inc(v_val_1020_);
lean_dec_ref(v_self_1017_);
v___x_1021_ = lean_apply_2(v_val_1020_, v___y_1018_, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0(lean_object* v_N_1023_, lean_object* v_i_1024_, lean_object* v___x_1025_){
_start:
{
lean_object* v___f_1026_; 
v___f_1026_ = ((lean_object*)(lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___closed__0));
return v___f_1026_;
}
}
LEAN_EXPORT lean_object* lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___boxed(lean_object* v_N_1027_, lean_object* v_i_1028_, lean_object* v___x_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0(v_N_1027_, v_i_1028_, v___x_1029_);
lean_dec(v___x_1029_);
lean_dec(v_i_1028_);
lean_dec_ref(v_N_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO___redArg(lean_object* v_R_1031_, lean_object* v_N_1032_, lean_object* v_i_1033_, lean_object* v_r_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___f_1038_; 
v___f_1036_ = ((lean_object*)(lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___closed__0));
v___x_1037_ = lean_apply_1(v_r_1034_, v_x_1035_);
v___f_1038_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1038_, 0, v___x_1037_);
lean_closure_set(v___f_1038_, 1, v___f_1036_);
return v___f_1038_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO___redArg___boxed(lean_object* v_R_1039_, lean_object* v_N_1040_, lean_object* v_i_1041_, lean_object* v_r_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = lp_tree_Formalism_MainNotions_N_rO___redArg(v_R_1039_, v_N_1040_, v_i_1041_, v_r_1042_, v_x_1043_);
lean_dec(v_i_1041_);
lean_dec_ref(v_N_1040_);
lean_dec_ref(v_R_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO(lean_object* v_R_1045_, lean_object* v_H_1046_, lean_object* v_what_u2082_1047_, lean_object* v_N_1048_, lean_object* v_i_1049_, lean_object* v_r_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = lp_tree_Formalism_MainNotions_N_rO___redArg(v_R_1045_, v_N_1048_, v_i_1049_, v_r_1050_, v_x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rO___boxed(lean_object* v_R_1053_, lean_object* v_H_1054_, lean_object* v_what_u2082_1055_, lean_object* v_N_1056_, lean_object* v_i_1057_, lean_object* v_r_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = lp_tree_Formalism_MainNotions_N_rO(v_R_1053_, v_H_1054_, v_what_u2082_1055_, v_N_1056_, v_i_1057_, v_r_1058_, v_x_1059_);
lean_dec(v_i_1057_);
lean_dec_ref(v_N_1056_);
lean_dec_ref(v_what_u2082_1055_);
lean_dec_ref(v_H_1054_);
lean_dec_ref(v_R_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rhoO___redArg(lean_object* v_00_u03c1_1061_, lean_object* v_00_u03c0_1062_){
_start:
{
lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; 
v___f_1063_ = ((lean_object*)(lp_tree_Units_coeHom___at___00Formalism_MainNotions_N_rO_spec__0___closed__0));
v___x_1064_ = lean_apply_1(v_00_u03c1_1061_, v_00_u03c0_1062_);
v___f_1065_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1065_, 0, v___x_1064_);
lean_closure_set(v___f_1065_, 1, v___f_1063_);
return v___f_1065_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rhoO(lean_object* v_R_1066_, lean_object* v_H_1067_, lean_object* v_what_u2082_1068_, lean_object* v_N_1069_, lean_object* v_i_1070_, lean_object* v_00_u03c1_1071_, lean_object* v_00_u03c0_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = lp_tree_Formalism_MainNotions_N_rhoO___redArg(v_00_u03c1_1071_, v_00_u03c0_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rhoO___boxed(lean_object* v_R_1074_, lean_object* v_H_1075_, lean_object* v_what_u2082_1076_, lean_object* v_N_1077_, lean_object* v_i_1078_, lean_object* v_00_u03c1_1079_, lean_object* v_00_u03c0_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = lp_tree_Formalism_MainNotions_N_rhoO(v_R_1074_, v_H_1075_, v_what_u2082_1076_, v_N_1077_, v_i_1078_, v_00_u03c1_1079_, v_00_u03c0_1080_);
lean_dec(v_i_1078_);
lean_dec_ref(v_N_1077_);
lean_dec_ref(v_what_u2082_1076_);
lean_dec_ref(v_H_1075_);
lean_dec_ref(v_R_1074_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg___lam__0(lean_object* v_00_u03c7_1082_, lean_object* v_M_1083_, lean_object* v_toMul_1084_, lean_object* v_g_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v_val_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_inc_ref(v_g_1085_);
v___x_1088_ = lean_apply_1(v_00_u03c7_1082_, v_g_1085_);
v_val_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_val_1089_);
lean_dec_ref(v___x_1088_);
v___x_1090_ = lean_apply_3(v_M_1083_, v_g_1085_, v___y_1086_, v___y_1087_);
v___x_1091_ = lean_apply_2(v_toMul_1084_, v_val_1089_, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg(lean_object* v_N_1092_, lean_object* v_i_1093_, lean_object* v_M_1094_, lean_object* v_00_u03c7_1095_){
_start:
{
lean_object* v_instO_1096_; lean_object* v___x_1097_; lean_object* v_toSemiring_1098_; lean_object* v___x_1099_; lean_object* v_toMul_1100_; lean_object* v___f_1101_; 
v_instO_1096_ = lean_ctor_get(v_N_1092_, 9);
lean_inc_ref(v_instO_1096_);
lean_dec_ref(v_N_1092_);
v___x_1097_ = lean_apply_1(v_instO_1096_, v_i_1093_);
v_toSemiring_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_toSemiring_1098_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_1098_);
v_toMul_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_toMul_1100_);
lean_dec_ref(v___x_1099_);
v___f_1101_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1101_, 0, v_00_u03c7_1095_);
lean_closure_set(v___f_1101_, 1, v_M_1094_);
lean_closure_set(v___f_1101_, 2, v_toMul_1100_);
return v___f_1101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0(lean_object* v_N_1102_, lean_object* v_i_1103_, lean_object* v___x_1104_, lean_object* v_k_1105_, lean_object* v_M_1106_, lean_object* v_00_u03c7_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg(v_N_1102_, v_i_1103_, v_M_1106_, v_00_u03c7_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___boxed(lean_object* v_N_1109_, lean_object* v_i_1110_, lean_object* v___x_1111_, lean_object* v_k_1112_, lean_object* v_M_1113_, lean_object* v_00_u03c7_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0(v_N_1109_, v_i_1110_, v___x_1111_, v_k_1112_, v_M_1113_, v_00_u03c7_1114_);
lean_dec(v_k_1112_);
lean_dec_ref(v___x_1111_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO___redArg(lean_object* v_R_1116_, lean_object* v_H_1117_, lean_object* v_N_1118_, lean_object* v_i_1119_, lean_object* v_00_u03c1_1120_, lean_object* v_00_u03c0_1121_){
_start:
{
lean_object* v_chi_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; 
v_chi_1122_ = lean_ctor_get(v_N_1118_, 19);
v___x_1123_ = lp_tree_Formalism_MainNotions_N_rhoO___redArg(v_00_u03c1_1120_, v_00_u03c0_1121_);
v___x_1124_ = lean_unsigned_to_nat(1u);
lean_inc(v_i_1119_);
lean_inc_ref(v_chi_1122_);
v___f_1125_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1125_, 0, v_chi_1122_);
lean_closure_set(v___f_1125_, 1, v_i_1119_);
lean_closure_set(v___f_1125_, 2, v___x_1124_);
v___x_1126_ = lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg(v_N_1118_, v_i_1119_, v___x_1123_, v___f_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO___redArg___boxed(lean_object* v_R_1127_, lean_object* v_H_1128_, lean_object* v_N_1129_, lean_object* v_i_1130_, lean_object* v_00_u03c1_1131_, lean_object* v_00_u03c0_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = lp_tree_Formalism_MainNotions_N_WpO___redArg(v_R_1127_, v_H_1128_, v_N_1129_, v_i_1130_, v_00_u03c1_1131_, v_00_u03c0_1132_);
lean_dec_ref(v_H_1128_);
lean_dec_ref(v_R_1127_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO(lean_object* v_R_1134_, lean_object* v_H_1135_, lean_object* v_what_u2082_1136_, lean_object* v_N_1137_, lean_object* v_i_1138_, lean_object* v_00_u03c1_1139_, lean_object* v_00_u03c0_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = lp_tree_Formalism_MainNotions_N_WpO___redArg(v_R_1134_, v_H_1135_, v_N_1137_, v_i_1138_, v_00_u03c1_1139_, v_00_u03c0_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_WpO___boxed(lean_object* v_R_1142_, lean_object* v_H_1143_, lean_object* v_what_u2082_1144_, lean_object* v_N_1145_, lean_object* v_i_1146_, lean_object* v_00_u03c1_1147_, lean_object* v_00_u03c0_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = lp_tree_Formalism_MainNotions_N_WpO(v_R_1142_, v_H_1143_, v_what_u2082_1144_, v_N_1145_, v_i_1146_, v_00_u03c1_1147_, v_00_u03c0_1148_);
lean_dec_ref(v_what_u2082_1144_);
lean_dec_ref(v_H_1143_);
lean_dec_ref(v_R_1142_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO___redArg(lean_object* v_R_1150_, lean_object* v_N_1151_, lean_object* v_i_1152_, lean_object* v_r_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v_chi_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; 
v_chi_1155_ = lean_ctor_get(v_N_1151_, 19);
v___x_1156_ = lp_tree_Formalism_MainNotions_N_rO___redArg(v_R_1150_, v_N_1151_, v_i_1152_, v_r_1153_, v_x_1154_);
v___x_1157_ = lean_unsigned_to_nat(1u);
lean_inc(v_i_1152_);
lean_inc_ref(v_chi_1155_);
v___f_1158_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_Glob_Wp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1158_, 0, v_chi_1155_);
lean_closure_set(v___f_1158_, 1, v_i_1152_);
lean_closure_set(v___f_1158_, 2, v___x_1157_);
v___x_1159_ = lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg(v_N_1151_, v_i_1152_, v___x_1156_, v___f_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO___redArg___boxed(lean_object* v_R_1160_, lean_object* v_N_1161_, lean_object* v_i_1162_, lean_object* v_r_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = lp_tree_Formalism_MainNotions_N_rTwO___redArg(v_R_1160_, v_N_1161_, v_i_1162_, v_r_1163_, v_x_1164_);
lean_dec_ref(v_R_1160_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO(lean_object* v_R_1166_, lean_object* v_H_1167_, lean_object* v_what_u2082_1168_, lean_object* v_N_1169_, lean_object* v_i_1170_, lean_object* v_r_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = lp_tree_Formalism_MainNotions_N_rTwO___redArg(v_R_1166_, v_N_1169_, v_i_1170_, v_r_1171_, v_x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_rTwO___boxed(lean_object* v_R_1174_, lean_object* v_H_1175_, lean_object* v_what_u2082_1176_, lean_object* v_N_1177_, lean_object* v_i_1178_, lean_object* v_r_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = lp_tree_Formalism_MainNotions_N_rTwO(v_R_1174_, v_H_1175_, v_what_u2082_1176_, v_N_1177_, v_i_1178_, v_r_1179_, v_x_1180_);
lean_dec_ref(v_what_u2082_1176_);
lean_dec_ref(v_H_1175_);
lean_dec_ref(v_R_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0(lean_object* v_toZero_1182_, lean_object* v_d_1183_, lean_object* v_i_1184_, lean_object* v_j_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_eq(v_i_1184_, v_j_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_i_1184_);
lean_dec(v_d_1183_);
lean_inc(v_toZero_1182_);
return v_toZero_1182_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_apply_1(v_d_1183_, v_i_1184_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0___boxed(lean_object* v_toZero_1188_, lean_object* v_d_1189_, lean_object* v_i_1190_, lean_object* v_j_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0(v_toZero_1188_, v_d_1189_, v_i_1190_, v_j_1191_);
lean_dec(v_j_1191_);
lean_dec(v_toZero_1188_);
return v_res_1192_;
}
}
static lean_object* _init_lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0(lean_object* v_N_1194_, lean_object* v_i_1195_, lean_object* v_d_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_instO_1199_; lean_object* v___x_1200_; lean_object* v_toSemiring_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_toAddMonoid_1204_; lean_object* v___x_1205_; lean_object* v_toZero_1206_; lean_object* v___x_1207_; lean_object* v_toFun_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; 
v_instO_1199_ = lean_ctor_get(v_N_1194_, 9);
lean_inc_ref(v_instO_1199_);
lean_dec_ref(v_N_1194_);
v___x_1200_ = lean_apply_1(v_instO_1199_, v_i_1195_);
v_toSemiring_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_toSemiring_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_1201_);
v___x_1203_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_1202_);
v_toAddMonoid_1204_ = lean_ctor_get(v___x_1203_, 1);
lean_inc_ref(v_toAddMonoid_1204_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_1204_);
lean_dec_ref(v_toAddMonoid_1204_);
v_toZero_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_toZero_1206_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = lean_obj_once(&lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0, &lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0_once, _init_lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0);
v_toFun_1208_ = lean_ctor_get(v___x_1207_, 0);
v___f_1209_ = lean_alloc_closure((void*)(lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1209_, 0, v_toZero_1206_);
lean_closure_set(v___f_1209_, 1, v_d_1196_);
lean_inc(v_toFun_1208_);
v___x_1210_ = lean_apply_3(v_toFun_1208_, v___f_1209_, v_a_1197_, v_a_1198_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0(lean_object* v_toOne_1211_, lean_object* v_x_1212_){
_start:
{
lean_inc(v_toOne_1211_);
return v_toOne_1211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0___boxed(lean_object* v_toOne_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0(v_toOne_1213_, v_x_1214_);
lean_dec(v_x_1214_);
lean_dec(v_toOne_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__1(lean_object* v_toSemiring_1216_, lean_object* v_N_1217_, lean_object* v_i_1218_, lean_object* v_x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_toOne_1224_; lean_object* v___f_1225_; lean_object* v___x_1226_; 
v___x_1222_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_1216_);
v___x_1223_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_1222_);
v_toOne_1224_ = lean_ctor_get(v___x_1223_, 2);
lean_inc(v_toOne_1224_);
lean_dec_ref(v___x_1223_);
v___f_1225_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1225_, 0, v_toOne_1224_);
v___x_1226_ = lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0(v_N_1217_, v_i_1218_, v___f_1225_, v___y_1220_, v___y_1221_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__1___boxed(lean_object* v_toSemiring_1227_, lean_object* v_N_1228_, lean_object* v_i_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__1(v_toSemiring_1227_, v_N_1228_, v_i_1229_, v_x_1230_, v___y_1231_, v___y_1232_);
lean_dec_ref(v_x_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__2(lean_object* v_chi_1234_, lean_object* v_i_1235_, lean_object* v_c_1236_, lean_object* v___x_1237_, lean_object* v___x_1238_, lean_object* v_m_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_val_1242_; lean_object* v_inv_1243_; lean_object* v___x_1244_; lean_object* v_toMul_1245_; lean_object* v_val_1246_; lean_object* v_inv_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
lean_inc_ref(v_chi_1234_);
lean_inc_ref(v_m_1239_);
lean_inc(v_i_1235_);
v___x_1240_ = lean_apply_3(v_chi_1234_, v_i_1235_, v_c_1236_, v_m_1239_);
v___x_1241_ = lean_apply_3(v_chi_1234_, v_i_1235_, v___x_1237_, v_m_1239_);
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1242_);
v_inv_1243_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_inv_1243_);
lean_dec_ref(v___x_1241_);
v___x_1244_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_1238_);
v_toMul_1245_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_toMul_1245_);
lean_dec_ref(v___x_1244_);
v_val_1246_ = lean_ctor_get(v___x_1240_, 0);
v_inv_1247_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v___x_1240_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_inv_1247_);
lean_inc(v_val_1246_);
lean_dec(v___x_1240_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_inc(v_toMul_1245_);
v___x_1251_ = lean_apply_2(v_toMul_1245_, v_val_1246_, v_inv_1243_);
v___x_1252_ = lean_apply_2(v_toMul_1245_, v_val_1242_, v_inv_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1252_);
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__2___boxed(lean_object* v_chi_1257_, lean_object* v_i_1258_, lean_object* v_c_1259_, lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v_m_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__2(v_chi_1257_, v_i_1258_, v_c_1259_, v___x_1260_, v___x_1261_, v_m_1262_);
lean_dec_ref(v___x_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___redArg(lean_object* v_N_1264_, lean_object* v_i_1265_, lean_object* v_c_1266_){
_start:
{
lean_object* v_instO_1267_; lean_object* v_chi_1268_; lean_object* v___x_1269_; lean_object* v_toSemiring_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; 
v_instO_1267_ = lean_ctor_get(v_N_1264_, 9);
v_chi_1268_ = lean_ctor_get(v_N_1264_, 19);
lean_inc_ref(v_instO_1267_);
lean_inc_n(v_i_1265_, 3);
v___x_1269_ = lean_apply_1(v_instO_1267_, v_i_1265_);
v_toSemiring_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_ref(v_toSemiring_1270_);
v___x_1271_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_N_1264_);
v___f_1272_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1272_, 0, v_toSemiring_1270_);
lean_closure_set(v___f_1272_, 1, v_N_1264_);
lean_closure_set(v___f_1272_, 2, v_i_1265_);
v___x_1273_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_1269_);
lean_dec_ref(v___x_1269_);
lean_inc_ref(v_chi_1268_);
v___f_1274_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1274_, 0, v_chi_1268_);
lean_closure_set(v___f_1274_, 1, v_i_1265_);
lean_closure_set(v___f_1274_, 2, v_c_1266_);
lean_closure_set(v___f_1274_, 3, v___x_1271_);
lean_closure_set(v___f_1274_, 4, v___x_1273_);
v___x_1275_ = lp_tree_Formalism_MainNotions_N_twistM___at___00Formalism_MainNotions_N_WpO_spec__0___redArg(v_N_1264_, v_i_1265_, v___f_1272_, v___f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO(lean_object* v_R_1276_, lean_object* v_H_1277_, lean_object* v_what_u2082_1278_, lean_object* v_N_1279_, lean_object* v_i_1280_, lean_object* v_c_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = lp_tree_Formalism_MainNotions_N_chiRatO___redArg(v_N_1279_, v_i_1280_, v_c_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_chiRatO___boxed(lean_object* v_R_1283_, lean_object* v_H_1284_, lean_object* v_what_u2082_1285_, lean_object* v_N_1286_, lean_object* v_i_1287_, lean_object* v_c_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = lp_tree_Formalism_MainNotions_N_chiRatO(v_R_1283_, v_H_1284_, v_what_u2082_1285_, v_N_1286_, v_i_1287_, v_c_1288_);
lean_dec_ref(v_what_u2082_1285_);
lean_dec_ref(v_H_1284_);
lean_dec_ref(v_R_1283_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9(lean_object* v_N_1290_, lean_object* v_i_1291_, lean_object* v___x_1292_, lean_object* v_k_1293_, lean_object* v_e_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = lp_mathlib_Equiv_symm___redArg(v_e_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_N_1296_, lean_object* v_i_1297_, lean_object* v___x_1298_, lean_object* v_k_1299_, lean_object* v_e_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = lp_tree_RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9(v_N_1296_, v_i_1297_, v___x_1298_, v_k_1299_, v_e_1300_);
lean_dec(v_k_1299_);
lean_dec(v_i_1297_);
lean_dec_ref(v_N_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4(lean_object* v_N_1302_, lean_object* v_i_1303_, lean_object* v___x_1304_, lean_object* v_k_1305_, lean_object* v_e_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = lp_mathlib_Equiv_symm___redArg(v_e_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4___boxed(lean_object* v_N_1308_, lean_object* v_i_1309_, lean_object* v___x_1310_, lean_object* v_k_1311_, lean_object* v_e_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = lp_tree_AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4(v_N_1308_, v_i_1309_, v___x_1310_, v_k_1311_, v_e_1312_);
lean_dec(v_k_1311_);
lean_dec(v_i_1309_);
lean_dec_ref(v_N_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg___lam__0(lean_object* v_invFun_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_apply_3(v_invFun_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___redArg(lean_object* v_self_1319_){
_start:
{
lean_object* v_toLinearMap_1320_; lean_object* v_invFun_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_toLinearMap_1320_ = lean_ctor_get(v_self_1319_, 0);
v_invFun_1321_ = lean_ctor_get(v_self_1319_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_self_1319_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v_self_1319_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_invFun_1321_);
lean_inc(v_toLinearMap_1320_);
lean_dec(v_self_1319_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_toLinearMap_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_invFun_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg(lean_object* v_N_1329_, lean_object* v_i_1330_, lean_object* v___x_1331_, lean_object* v_k_1332_, lean_object* v_00_u03c3_1333_, lean_object* v_00_u03c3_x27_1334_, lean_object* v_e_1335_){
_start:
{
lean_object* v_invFun_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_invFun_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_invFun_1336_ = lean_ctor_get(v_e_1335_, 1);
lean_inc(v_invFun_1336_);
v___x_1337_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___redArg(v_e_1335_);
v___x_1338_ = lp_mathlib_Equiv_symm___redArg(v___x_1337_);
v_invFun_1339_ = lean_ctor_get(v___x_1338_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1338_, 0);
lean_dec(v_unused_1348_);
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_invFun_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___f_1343_; lean_object* v___x_1345_; 
v___f_1343_ = lean_alloc_closure((void*)(lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1343_, 0, v_invFun_1336_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___f_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___f_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_invFun_1339_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_N_1349_, lean_object* v_i_1350_, lean_object* v___x_1351_, lean_object* v_k_1352_, lean_object* v_00_u03c3_1353_, lean_object* v_00_u03c3_x27_1354_, lean_object* v_e_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg(v_N_1349_, v_i_1350_, v___x_1351_, v_k_1352_, v_00_u03c3_1353_, v_00_u03c3_x27_1354_, v_e_1355_);
lean_dec(v_00_u03c3_x27_1354_);
lean_dec(v_00_u03c3_1353_);
lean_dec(v_k_1352_);
lean_dec(v_i_1350_);
lean_dec_ref(v_N_1349_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___lam__1(lean_object* v___x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_toLinearMap_1361_; lean_object* v___x_1362_; 
v_toLinearMap_1361_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_toLinearMap_1361_);
lean_dec_ref(v___x_1357_);
v___x_1362_ = lean_apply_3(v_toLinearMap_1361_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_l_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_toLinearMap_1367_; lean_object* v___x_1368_; 
v_toLinearMap_1367_ = lean_ctor_get(v_l_1363_, 0);
lean_inc(v_toLinearMap_1367_);
lean_dec_ref(v_l_1363_);
v___x_1368_ = lean_apply_3(v_toLinearMap_1367_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_N_1369_, lean_object* v_i_1370_, lean_object* v___x_1371_, lean_object* v_k_1372_, lean_object* v_l_1373_){
_start:
{
lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; 
lean_inc_ref(v_l_1373_);
v___f_1374_ = lean_alloc_closure((void*)(lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1374_, 0, v_l_1373_);
v___f_1375_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
v___x_1376_ = lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg(v_N_1369_, v_i_1370_, v___x_1371_, v_k_1372_, v___f_1375_, v___f_1375_, v_l_1373_);
v___f_1377_ = lean_alloc_closure((void*)(lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1377_, 0, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___f_1374_);
lean_ctor_set(v___x_1378_, 1, v___f_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_N_1379_, lean_object* v_i_1380_, lean_object* v___x_1381_, lean_object* v_k_1382_, lean_object* v_l_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg(v_N_1379_, v_i_1380_, v___x_1381_, v_k_1382_, v_l_1383_);
lean_dec(v_k_1382_);
lean_dec(v_i_1380_);
lean_dec_ref(v_N_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30(lean_object* v_N_1385_, lean_object* v_i_1386_, lean_object* v___x_1387_, lean_object* v_S_1388_, lean_object* v_r_u2081_1389_, lean_object* v_s_u2081_1390_, lean_object* v_r_u2082_1391_, lean_object* v_s_u2082_1392_){
_start:
{
lean_object* v_instO_1393_; lean_object* v___x_1394_; lean_object* v_toSemiring_1395_; lean_object* v_toAddCommMonoid_1396_; lean_object* v_toMonoid_1397_; lean_object* v_toAddSemigroup_1398_; lean_object* v___x_1399_; lean_object* v_toMul_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1411_; 
v_instO_1393_ = lean_ctor_get(v_N_1385_, 9);
lean_inc_ref(v_instO_1393_);
lean_dec_ref(v_N_1385_);
v___x_1394_ = lean_apply_1(v_instO_1393_, v_i_1386_);
v_toSemiring_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_toSemiring_1395_);
lean_dec_ref(v___x_1394_);
v_toAddCommMonoid_1396_ = lean_ctor_get(v_toSemiring_1395_, 0);
lean_inc_ref(v_toAddCommMonoid_1396_);
v_toMonoid_1397_ = lean_ctor_get(v_toSemiring_1395_, 1);
lean_inc_ref(v_toMonoid_1397_);
lean_dec_ref(v_toSemiring_1395_);
v_toAddSemigroup_1398_ = lean_ctor_get(v_toAddCommMonoid_1396_, 0);
lean_inc(v_toAddSemigroup_1398_);
lean_dec_ref(v_toAddCommMonoid_1396_);
v___x_1399_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1397_);
lean_dec_ref(v_toMonoid_1397_);
v_toMul_1400_ = lean_ctor_get(v___x_1399_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1399_, 0);
lean_dec(v_unused_1412_);
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1411_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_toMul_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1411_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_inc_n(v_toMul_1400_, 2);
lean_inc(v_s_u2082_1392_);
v___x_1404_ = lean_apply_2(v_toMul_1400_, v_s_u2082_1392_, v_r_u2081_1389_);
lean_inc(v_s_u2081_1390_);
v___x_1405_ = lean_apply_2(v_toMul_1400_, v_s_u2081_1390_, v_r_u2082_1391_);
v___x_1406_ = lean_apply_2(v_toAddSemigroup_1398_, v___x_1404_, v___x_1405_);
v___x_1407_ = lean_apply_2(v_toMul_1400_, v_s_u2082_1392_, v_s_u2081_1390_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1407_);
lean_ctor_set(v___x_1402_, 0, v___x_1406_);
v___x_1409_ = v___x_1402_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29(lean_object* v_N_1413_, lean_object* v_i_1414_, lean_object* v___x_1415_, lean_object* v_S_1416_, lean_object* v_r_u2082_1417_, lean_object* v_s_u2082_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; 
v_fst_1420_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_fst_1420_);
v_snd_1421_ = lean_ctor_get(v_a_1419_, 1);
lean_inc(v_snd_1421_);
lean_dec(v_a_1419_);
v___x_1422_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30(v_N_1413_, v_i_1414_, v___x_1415_, v_S_1416_, v_fst_1420_, v_snd_1421_, v_r_u2082_1417_, v_s_u2082_1418_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28(lean_object* v_N_1423_, lean_object* v_i_1424_, lean_object* v___x_1425_, lean_object* v_S_1426_, lean_object* v_x_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1431_; 
v_fst_1429_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_fst_1429_);
v_snd_1430_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_snd_1430_);
lean_dec(v_a_1428_);
v___x_1431_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29(v_N_1423_, v_i_1424_, v___x_1425_, v_S_1426_, v_fst_1429_, v_snd_1430_, v_x_1427_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27___lam__0(lean_object* v_N_1432_, lean_object* v_i_1433_, lean_object* v___x_1434_, lean_object* v_x1_1435_, lean_object* v_x2_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28(v_N_1432_, v_i_1433_, v___x_1434_, v___x_1434_, v_x1_1435_, v_x2_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7_spec__11(lean_object* v_N_1438_, lean_object* v_i_1439_, lean_object* v___x_1440_, lean_object* v_S_1441_){
_start:
{
lean_object* v_instO_1442_; lean_object* v___x_1443_; lean_object* v_toSemiring_1444_; lean_object* v___x_1445_; lean_object* v_toMonoid_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_toZero_1449_; lean_object* v___x_1450_; lean_object* v_toOne_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_instO_1442_ = lean_ctor_get(v_N_1438_, 9);
lean_inc_ref(v_instO_1442_);
lean_dec_ref(v_N_1438_);
v___x_1443_ = lean_apply_1(v_instO_1442_, v_i_1439_);
v_toSemiring_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_ref(v_toSemiring_1444_);
lean_dec_ref(v___x_1443_);
v___x_1445_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_1444_);
lean_dec_ref(v_toSemiring_1444_);
v_toMonoid_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc_ref(v_toMonoid_1446_);
v___x_1447_ = lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(v___x_1445_);
v___x_1448_ = lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(v___x_1447_);
v_toZero_1449_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_toZero_1449_);
lean_dec_ref(v___x_1448_);
v___x_1450_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1446_);
lean_dec_ref(v_toMonoid_1446_);
v_toOne_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1450_, 1);
lean_dec(v_unused_1459_);
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_toOne_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_toOne_1451_);
lean_ctor_set(v___x_1453_, 0, v_toZero_1449_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_toZero_1449_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_toOne_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27(lean_object* v_N_1460_, lean_object* v_i_1461_, lean_object* v___x_1462_, lean_object* v_s_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_inc(v_i_1461_);
lean_inc_ref(v_N_1460_);
v___f_1464_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27___lam__0), 5, 3);
lean_closure_set(v___f_1464_, 0, v_N_1460_);
lean_closure_set(v___f_1464_, 1, v_i_1461_);
lean_closure_set(v___f_1464_, 2, v___x_1462_);
v___x_1465_ = lp_tree_OreLocalization_zero___at___00Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7_spec__11(v_N_1460_, v_i_1461_, v___x_1462_, v___x_1462_);
v___x_1466_ = l_List_foldrTR___redArg(v___f_1464_, v___x_1465_, v_s_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24___redArg(lean_object* v_N_1467_, lean_object* v_i_1468_, lean_object* v___x_1469_, lean_object* v_s_1470_, lean_object* v_f_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lp_mathlib_Multiset_map___redArg(v_f_1471_, v_s_1470_);
v___x_1473_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27(v_N_1467_, v_i_1468_, v___x_1469_, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___redArg(lean_object* v_P_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_fst_1476_; lean_object* v_snd_1477_; lean_object* v___x_1478_; 
v_fst_1476_ = lean_ctor_get(v_a_1475_, 0);
lean_inc(v_fst_1476_);
v_snd_1477_ = lean_ctor_get(v_a_1475_, 1);
lean_inc(v_snd_1477_);
lean_dec(v_a_1475_);
v___x_1478_ = lean_apply_2(v_P_1474_, v_fst_1476_, v_snd_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__0(lean_object* v_toMonoid_1479_, lean_object* v_x1_1480_, lean_object* v_x2_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v_toMul_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1494_; 
v___x_1484_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1479_);
v_toMul_1485_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v___x_1484_, 0);
lean_dec(v_unused_1495_);
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_toMul_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_inc(v_toMul_1485_);
v___x_1489_ = lean_apply_2(v_toMul_1485_, v_x1_1480_, v___y_1482_);
v___x_1490_ = lean_apply_2(v_toMul_1485_, v___y_1483_, v_x2_1481_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1490_);
lean_ctor_set(v___x_1487_, 0, v___x_1489_);
v___x_1492_ = v___x_1487_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__0___boxed(lean_object* v_toMonoid_1496_, lean_object* v_x1_1497_, lean_object* v_x2_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__0(v_toMonoid_1496_, v_x1_1497_, v_x2_1498_, v___y_1499_, v___y_1500_);
lean_dec_ref(v_toMonoid_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__1(lean_object* v_toMonoid_1502_, lean_object* v___x_1503_, lean_object* v_x1_1504_, lean_object* v_x2_1505_){
_start:
{
lean_object* v___f_1506_; lean_object* v___x_1507_; 
v___f_1506_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1506_, 0, v_toMonoid_1502_);
lean_closure_set(v___f_1506_, 1, v_x1_1504_);
lean_closure_set(v___f_1506_, 2, v_x2_1505_);
v___x_1507_ = lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___redArg(v___f_1506_, v___x_1503_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__2(lean_object* v___x_1508_, lean_object* v_v_1509_, lean_object* v_w_1510_, lean_object* v_i_1511_){
_start:
{
lean_object* v_toSemiring_1512_; lean_object* v___x_1513_; lean_object* v_toMonoid_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; 
v_toSemiring_1512_ = lean_ctor_get(v___x_1508_, 0);
v___x_1513_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_1512_);
v_toMonoid_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc_ref(v_toMonoid_1514_);
lean_dec_ref(v___x_1513_);
lean_inc(v_i_1511_);
v___x_1515_ = lean_apply_1(v_v_1509_, v_i_1511_);
v___x_1516_ = lean_apply_1(v_w_1510_, v_i_1511_);
v___f_1517_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__1), 4, 2);
lean_closure_set(v___f_1517_, 0, v_toMonoid_1514_);
lean_closure_set(v___f_1517_, 1, v___x_1516_);
v___x_1518_ = lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___redArg(v___f_1517_, v___x_1515_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__2___boxed(lean_object* v___x_1519_, lean_object* v_v_1520_, lean_object* v_w_1521_, lean_object* v_i_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__2(v___x_1519_, v_v_1520_, v_w_1521_, v_i_1522_);
lean_dec_ref(v___x_1519_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object* v_k_1524_, lean_object* v_N_1525_, lean_object* v_i_1526_, lean_object* v___x_1527_, lean_object* v_v_1528_, lean_object* v_w_1529_){
_start:
{
lean_object* v_instO_1530_; lean_object* v___x_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_instO_1530_ = lean_ctor_get(v_N_1525_, 9);
lean_inc_ref(v_instO_1530_);
lean_inc(v_i_1526_);
v___x_1531_ = lean_apply_1(v_instO_1530_, v_i_1526_);
v___f_1532_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1532_, 0, v___x_1531_);
lean_closure_set(v___f_1532_, 1, v_v_1528_);
lean_closure_set(v___f_1532_, 2, v_w_1529_);
v___x_1533_ = l_List_finRange(v_k_1524_);
v___x_1534_ = lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24___redArg(v_N_1525_, v_i_1526_, v___x_1527_, v___x_1533_, v___f_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_N_1535_, lean_object* v_i_1536_, lean_object* v___x_1537_, lean_object* v_k_1538_, lean_object* v_M_1539_, lean_object* v_v_1540_, lean_object* v_x_1541_){
_start:
{
lean_object* v___f_1542_; lean_object* v___x_1543_; 
v___f_1542_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1542_, 0, v_M_1539_);
lean_closure_set(v___f_1542_, 1, v_x_1541_);
v___x_1543_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18(v_k_1538_, v_N_1535_, v_i_1536_, v___x_1537_, v___f_1542_, v_v_1540_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8___redArg___lam__0(lean_object* v_N_1544_, lean_object* v_i_1545_, lean_object* v___x_1546_, lean_object* v_k_1547_, lean_object* v_M_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13___redArg(v_N_1544_, v_i_1545_, v___x_1546_, v_k_1547_, v_M_1548_, v___y_1549_, v___y_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_N_1552_, lean_object* v_i_1553_, lean_object* v___x_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v___f_1556_; 
v___f_1556_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8___redArg___lam__0), 7, 4);
lean_closure_set(v___f_1556_, 0, v_N_1552_);
lean_closure_set(v___f_1556_, 1, v_i_1553_);
lean_closure_set(v___f_1556_, 2, v___x_1554_);
lean_closure_set(v___f_1556_, 3, v_k_1555_);
return v___f_1556_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__3(lean_object* v_N_1557_, lean_object* v_i_1558_, lean_object* v___x_1559_, lean_object* v_k_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13___redArg(v_N_1557_, v_i_1558_, v___x_1559_, v_k_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_N_1565_, lean_object* v_i_1566_, lean_object* v___x_1567_, lean_object* v_S_1568_){
_start:
{
lean_object* v_instO_1569_; lean_object* v___x_1570_; lean_object* v_toSemiring_1571_; lean_object* v___x_1572_; lean_object* v_toMonoid_1573_; lean_object* v___x_1574_; lean_object* v_toOne_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_instO_1569_ = lean_ctor_get(v_N_1565_, 9);
lean_inc_ref(v_instO_1569_);
lean_dec_ref(v_N_1565_);
v___x_1570_ = lean_apply_1(v_instO_1569_, v_i_1566_);
v_toSemiring_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_toSemiring_1571_);
lean_dec_ref(v___x_1570_);
v___x_1572_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_1571_);
lean_dec_ref(v_toSemiring_1571_);
v_toMonoid_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_toMonoid_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1573_);
lean_dec_ref(v_toMonoid_1573_);
v_toOne_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1574_, 1);
lean_dec(v_unused_1583_);
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_toOne_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
lean_inc(v_toOne_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v_toOne_1575_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_toOne_1575_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_toOne_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___lam__0(lean_object* v_N_1584_, lean_object* v_i_1585_, lean_object* v___x_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = lp_tree_OreLocalization_zero___at___00Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7_spec__11(v_N_1584_, v_i_1585_, v___x_1586_, v___x_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_N_1589_, lean_object* v_i_1590_, lean_object* v___x_1591_, lean_object* v_x_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___lam__0(v_N_1589_, v_i_1590_, v___x_1591_, v_x_1592_);
lean_dec(v_x_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_N_1594_, lean_object* v_i_1595_, lean_object* v___x_1596_, lean_object* v_i_1597_, lean_object* v_x_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; 
v___f_1600_ = lean_alloc_closure((void*)(lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1600_, 0, v_N_1594_);
lean_closure_set(v___f_1600_, 1, v_i_1595_);
lean_closure_set(v___f_1600_, 2, v___x_1596_);
v___x_1601_ = lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(v___f_1600_, v_i_1597_, v_x_1598_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_N_1602_, lean_object* v_i_1603_, lean_object* v___x_1604_, lean_object* v_i_1605_, lean_object* v_x_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_N_1602_, v_i_1603_, v___x_1604_, v_i_1605_, v_x_1606_, v_a_1607_);
lean_dec(v_x_1606_);
lean_dec(v_i_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__0(lean_object* v_N_1609_, lean_object* v_i_1610_, lean_object* v___x_1611_, lean_object* v_j_1612_, lean_object* v___x_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_N_1609_, v_i_1610_, v___x_1611_, v_j_1612_, v___x_1613_, v___y_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_N_1616_, lean_object* v_i_1617_, lean_object* v___x_1618_, lean_object* v_j_1619_, lean_object* v___x_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__0(v_N_1616_, v_i_1617_, v___x_1618_, v_j_1619_, v___x_1620_, v___y_1621_);
lean_dec(v___x_1620_);
lean_dec(v_j_1619_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__1(lean_object* v_N_1623_, lean_object* v_i_1624_, lean_object* v___x_1625_, lean_object* v_f_1626_, lean_object* v_i_1627_, lean_object* v_j_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; 
lean_inc(v_i_1624_);
lean_inc_ref(v_N_1623_);
v___x_1629_ = lp_tree_OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6(v_N_1623_, v_i_1624_, v___x_1625_, v___x_1625_);
v___f_1630_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1630_, 0, v_N_1623_);
lean_closure_set(v___f_1630_, 1, v_i_1624_);
lean_closure_set(v___f_1630_, 2, v___x_1625_);
lean_closure_set(v___f_1630_, 3, v_j_1628_);
lean_closure_set(v___f_1630_, 4, v___x_1629_);
v___x_1631_ = lean_apply_2(v_f_1626_, v___f_1630_, v_i_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__2(lean_object* v_N_1632_, lean_object* v_i_1633_, lean_object* v___x_1634_, lean_object* v_f_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v_toFun_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_obj_once(&lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0, &lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0_once, _init_lp_tree_LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3___redArg___lam__3___closed__0);
v_toFun_1639_ = lean_ctor_get(v___x_1638_, 0);
v___f_1640_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__1), 6, 4);
lean_closure_set(v___f_1640_, 0, v_N_1632_);
lean_closure_set(v___f_1640_, 1, v_i_1633_);
lean_closure_set(v___f_1640_, 2, v___x_1634_);
lean_closure_set(v___f_1640_, 3, v_f_1635_);
lean_inc(v_toFun_1639_);
v___x_1641_ = lean_apply_3(v_toFun_1639_, v___f_1640_, v___y_1636_, v___y_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_N_1642_, lean_object* v_i_1643_, lean_object* v___x_1644_, lean_object* v_k_1645_){
_start:
{
lean_object* v___f_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; 
lean_inc(v_i_1643_);
lean_inc_ref(v_N_1642_);
v___f_1646_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1646_, 0, v_N_1642_);
lean_closure_set(v___f_1646_, 1, v_i_1643_);
lean_closure_set(v___f_1646_, 2, v___x_1644_);
v___f_1647_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg___lam__3), 7, 4);
lean_closure_set(v___f_1647_, 0, v_N_1642_);
lean_closure_set(v___f_1647_, 1, v_i_1643_);
lean_closure_set(v___f_1647_, 2, v___x_1644_);
lean_closure_set(v___f_1647_, 3, v_k_1645_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___f_1646_);
lean_ctor_set(v___x_1648_, 1, v___f_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3(lean_object* v_N_1649_, lean_object* v_i_1650_, lean_object* v___x_1651_, lean_object* v_k_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_inc(v_k_1652_);
lean_inc(v_i_1650_);
lean_inc_ref(v_N_1649_);
v___x_1653_ = lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg(v_N_1649_, v_i_1650_, v___x_1651_, v_k_1652_);
v___x_1654_ = lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg(v_N_1649_, v_i_1650_, v___x_1651_, v_k_1652_, v___x_1653_);
lean_dec(v_k_1652_);
lean_dec(v_i_1650_);
lean_dec_ref(v_N_1649_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2(lean_object* v_N_1655_, lean_object* v_i_1656_, lean_object* v___x_1657_, lean_object* v_k_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lp_tree_LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3(v_N_1655_, v_i_1656_, v___x_1657_, v_k_1658_);
v___x_1660_ = lp_mathlib_Equiv_symm___redArg(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1___redArg(lean_object* v_N_1661_, lean_object* v_i_1662_, lean_object* v___x_1663_, lean_object* v_k_1664_, lean_object* v_M_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v_toFun_1667_; lean_object* v___f_1668_; 
v___x_1666_ = lp_tree_Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2(v_N_1661_, v_i_1662_, v___x_1663_, v_k_1664_);
v_toFun_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_toFun_1667_);
lean_dec_ref(v___x_1666_);
v___f_1668_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1668_, 0, v_M_1665_);
lean_closure_set(v___f_1668_, 1, v_toFun_1667_);
return v___f_1668_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg___lam__1(lean_object* v___f_1669_, lean_object* v_M_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lp_mathlib_Matrix_map___redArg(v_M_1670_, v___f_1669_, v___y_1671_, v___y_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_apply_1(v_f_1674_, v___y_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg(lean_object* v_f_1677_){
_start:
{
lean_object* v___f_1678_; lean_object* v___f_1679_; 
v___f_1678_ = lean_alloc_closure((void*)(lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1678_, 0, v_f_1677_);
v___f_1679_ = lean_alloc_closure((void*)(lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg___lam__1), 4, 1);
lean_closure_set(v___f_1679_, 0, v___f_1678_);
return v___f_1679_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg(lean_object* v_N_1680_, lean_object* v_i_1681_, lean_object* v___x_1682_, lean_object* v_k_1683_, lean_object* v_f_1684_, lean_object* v_M_1685_){
_start:
{
lean_object* v___x_1686_; lean_object* v___f_1687_; 
v___x_1686_ = lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg(v_f_1684_);
v___f_1687_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1687_, 0, v_M_1685_);
lean_closure_set(v___f_1687_, 1, v___x_1686_);
return v___f_1687_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg___boxed(lean_object* v_N_1688_, lean_object* v_i_1689_, lean_object* v___x_1690_, lean_object* v_k_1691_, lean_object* v_f_1692_, lean_object* v_M_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg(v_N_1688_, v_i_1689_, v___x_1690_, v_k_1691_, v_f_1692_, v_M_1693_);
lean_dec(v_k_1691_);
lean_dec(v_i_1689_);
lean_dec_ref(v_N_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK___redArg(lean_object* v_R_1695_, lean_object* v_H_1696_, lean_object* v_N_1697_, lean_object* v_i_1698_, lean_object* v_r_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v_instO_1701_; lean_object* v___x_1702_; lean_object* v_toSemiring_1703_; lean_object* v_toMonoid_1704_; lean_object* v___x_1705_; lean_object* v_toOne_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_instO_1701_ = lean_ctor_get(v_N_1697_, 9);
lean_inc_ref(v_instO_1701_);
lean_inc(v_i_1698_);
v___x_1702_ = lean_apply_1(v_instO_1701_, v_i_1698_);
v_toSemiring_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_toSemiring_1703_);
lean_dec_ref(v___x_1702_);
v_toMonoid_1704_ = lean_ctor_get(v_toSemiring_1703_, 1);
lean_inc_ref(v_toMonoid_1704_);
lean_dec_ref(v_toSemiring_1703_);
v___x_1705_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1704_);
lean_dec_ref(v_toMonoid_1704_);
v_toOne_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_toOne_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_1695_);
v___f_1709_ = lean_alloc_closure((void*)(lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1709_, 0, v_toOne_1706_);
v___f_1710_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
v___f_1711_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1711_, 0, v___f_1710_);
lean_closure_set(v___f_1711_, 1, v___f_1709_);
v___x_1712_ = lp_tree_Formalism_MainNotions_N_rO___redArg(v_R_1695_, v_N_1697_, v_i_1698_, v_r_1699_, v_x_1700_);
v___x_1713_ = lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg(v_N_1697_, v_i_1698_, v___x_1707_, v___x_1708_, v___f_1711_, v___x_1712_);
v___x_1714_ = lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1___redArg(v_N_1697_, v_i_1698_, v___x_1707_, v___x_1708_, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK___redArg___boxed(lean_object* v_R_1715_, lean_object* v_H_1716_, lean_object* v_N_1717_, lean_object* v_i_1718_, lean_object* v_r_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = lp_tree_Formalism_MainNotions_N_repK___redArg(v_R_1715_, v_H_1716_, v_N_1717_, v_i_1718_, v_r_1719_, v_x_1720_);
lean_dec_ref(v_H_1716_);
lean_dec_ref(v_R_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK(lean_object* v_R_1722_, lean_object* v_H_1723_, lean_object* v_what_u2082_1724_, lean_object* v_N_1725_, lean_object* v_i_1726_, lean_object* v_r_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = lp_tree_Formalism_MainNotions_N_repK___redArg(v_R_1722_, v_H_1723_, v_N_1725_, v_i_1726_, v_r_1727_, v_x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_repK___boxed(lean_object* v_R_1730_, lean_object* v_H_1731_, lean_object* v_what_u2082_1732_, lean_object* v_N_1733_, lean_object* v_i_1734_, lean_object* v_r_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = lp_tree_Formalism_MainNotions_N_repK(v_R_1730_, v_H_1731_, v_what_u2082_1732_, v_N_1733_, v_i_1734_, v_r_1735_, v_x_1736_);
lean_dec_ref(v_what_u2082_1732_);
lean_dec_ref(v_H_1731_);
lean_dec_ref(v_R_1730_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0(lean_object* v_k_1738_, lean_object* v_N_1739_, lean_object* v_i_1740_, lean_object* v___x_1741_, lean_object* v_f_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___redArg(v_f_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0___boxed(lean_object* v_k_1744_, lean_object* v_N_1745_, lean_object* v_i_1746_, lean_object* v___x_1747_, lean_object* v_f_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = lp_tree_RingHom_mapMatrix___at___00Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0_spec__0(v_k_1744_, v_N_1745_, v_i_1746_, v___x_1747_, v_f_1748_);
lean_dec(v_i_1746_);
lean_dec_ref(v_N_1745_);
lean_dec(v_k_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0(lean_object* v_N_1750_, lean_object* v_i_1751_, lean_object* v___x_1752_, lean_object* v___x_1753_, lean_object* v_k_1754_, lean_object* v_f_1755_, lean_object* v_M_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___redArg(v_N_1750_, v_i_1751_, v___x_1753_, v_k_1754_, v_f_1755_, v_M_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0___boxed(lean_object* v_N_1758_, lean_object* v_i_1759_, lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v_k_1762_, lean_object* v_f_1763_, lean_object* v_M_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = lp_tree_Formalism_MainNotions_N_mapM___at___00Formalism_MainNotions_N_repK_spec__0(v_N_1758_, v_i_1759_, v___x_1760_, v___x_1761_, v_k_1762_, v_f_1763_, v_M_1764_);
lean_dec(v_k_1762_);
lean_dec_ref(v___x_1760_);
lean_dec(v_i_1759_);
lean_dec_ref(v_N_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___redArg(lean_object* v_e_1766_){
_start:
{
lean_object* v_toFun_1767_; 
v_toFun_1767_ = lean_ctor_get(v_e_1766_, 0);
lean_inc(v_toFun_1767_);
return v_toFun_1767_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___redArg___boxed(lean_object* v_e_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___redArg(v_e_1768_);
lean_dec_ref(v_e_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3(lean_object* v_N_1770_, lean_object* v_i_1771_, lean_object* v___x_1772_, lean_object* v_k_1773_, lean_object* v_e_1774_){
_start:
{
lean_object* v_toFun_1775_; 
v_toFun_1775_ = lean_ctor_get(v_e_1774_, 0);
lean_inc(v_toFun_1775_);
return v_toFun_1775_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3___boxed(lean_object* v_N_1776_, lean_object* v_i_1777_, lean_object* v___x_1778_, lean_object* v_k_1779_, lean_object* v_e_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = lp_tree_AlgEquiv_toAlgHom___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__3(v_N_1776_, v_i_1777_, v___x_1778_, v_k_1779_, v_e_1780_);
lean_dec_ref(v_e_1780_);
lean_dec(v_k_1779_);
lean_dec(v_i_1777_);
lean_dec_ref(v_N_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1(lean_object* v_N_1782_, lean_object* v_i_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_k_1786_, lean_object* v_M_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1___redArg(v_N_1782_, v_i_1783_, v___x_1784_, v_k_1786_, v_M_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1___boxed(lean_object* v_N_1789_, lean_object* v_i_1790_, lean_object* v___x_1791_, lean_object* v___x_1792_, lean_object* v_k_1793_, lean_object* v_M_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = lp_tree_Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1(v_N_1789_, v_i_1790_, v___x_1791_, v___x_1792_, v_k_1793_, v_M_1794_);
lean_dec_ref(v___x_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_self_1796_){
_start:
{
lean_inc_ref(v_self_1796_);
return v_self_1796_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_self_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___redArg(v_self_1797_);
lean_dec_ref(v_self_1797_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8(lean_object* v_N_1799_, lean_object* v_i_1800_, lean_object* v___x_1801_, lean_object* v_k_1802_, lean_object* v_self_1803_){
_start:
{
lean_inc_ref(v_self_1803_);
return v_self_1803_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_N_1804_, lean_object* v_i_1805_, lean_object* v___x_1806_, lean_object* v_k_1807_, lean_object* v_self_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = lp_tree_AlgEquiv_toRingEquiv___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__8(v_N_1804_, v_i_1805_, v___x_1806_, v_k_1807_, v_self_1808_);
lean_dec_ref(v_self_1808_);
lean_dec(v_k_1807_);
lean_dec(v_i_1805_);
lean_dec_ref(v_N_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5(lean_object* v_N_1810_, lean_object* v_i_1811_, lean_object* v___x_1812_, lean_object* v_k_1813_, lean_object* v_m_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = lp_tree_LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5___redArg(v_N_1810_, v_i_1811_, v___x_1812_, v_k_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6(lean_object* v_N_1816_, lean_object* v_i_1817_, lean_object* v___x_1818_, lean_object* v_k_1819_, lean_object* v_l_1820_, lean_object* v_map__one_1821_, lean_object* v_map__mul_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___redArg(v_N_1816_, v_i_1817_, v___x_1818_, v_k_1819_, v_l_1820_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_N_1824_, lean_object* v_i_1825_, lean_object* v___x_1826_, lean_object* v_k_1827_, lean_object* v_l_1828_, lean_object* v_map__one_1829_, lean_object* v_map__mul_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = lp_tree_AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6(v_N_1824_, v_i_1825_, v___x_1826_, v_k_1827_, v_l_1828_, v_map__one_1829_, v_map__mul_1830_);
lean_dec(v_k_1827_);
lean_dec(v_i_1825_);
lean_dec_ref(v_N_1824_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___redArg(lean_object* v_self_1832_){
_start:
{
lean_inc_ref(v_self_1832_);
return v_self_1832_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object* v_self_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___redArg(v_self_1833_);
lean_dec_ref(v_self_1833_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14(lean_object* v_N_1835_, lean_object* v_i_1836_, lean_object* v___x_1837_, lean_object* v_k_1838_, lean_object* v_self_1839_){
_start:
{
lean_inc_ref(v_self_1839_);
return v_self_1839_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14___boxed(lean_object* v_N_1840_, lean_object* v_i_1841_, lean_object* v___x_1842_, lean_object* v_k_1843_, lean_object* v_self_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = lp_tree_RingEquiv_toMulEquiv___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__14(v_N_1840_, v_i_1841_, v___x_1842_, v_k_1843_, v_self_1844_);
lean_dec_ref(v_self_1844_);
lean_dec(v_k_1843_);
lean_dec(v_i_1841_);
lean_dec_ref(v_N_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object* v_h_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = lp_mathlib_Equiv_symm___redArg(v_h_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object* v_N_1848_, lean_object* v_i_1849_, lean_object* v___x_1850_, lean_object* v_k_1851_, lean_object* v_h_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lp_mathlib_Equiv_symm___redArg(v_h_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object* v_N_1854_, lean_object* v_i_1855_, lean_object* v___x_1856_, lean_object* v_k_1857_, lean_object* v_h_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = lp_tree_MulEquiv_symm___at___00RingEquiv_symm___at___00AlgEquiv_symm___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__4_spec__9_spec__15(v_N_1854_, v_i_1855_, v___x_1856_, v_k_1857_, v_h_1858_);
lean_dec(v_k_1857_);
lean_dec(v_i_1855_);
lean_dec_ref(v_N_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_r_1860_, lean_object* v_s_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v_r_1860_);
lean_ctor_set(v___x_1862_, 1, v_s_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9(lean_object* v_N_1863_, lean_object* v_i_1864_, lean_object* v___x_1865_, lean_object* v_S_1866_, lean_object* v_r_1867_, lean_object* v_s_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_r_1867_);
lean_ctor_set(v___x_1869_, 1, v_s_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_N_1870_, lean_object* v_i_1871_, lean_object* v___x_1872_, lean_object* v_S_1873_, lean_object* v_r_1874_, lean_object* v_s_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = lp_tree_OreLocalization_oreDiv___at___00OreLocalization_one___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__6_spec__9(v_N_1870_, v_i_1871_, v___x_1872_, v_S_1873_, v_r_1874_, v_s_1875_);
lean_dec(v_i_1871_);
lean_dec_ref(v_N_1870_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_N_1877_, lean_object* v_i_1878_, lean_object* v___x_1879_, lean_object* v_k_1880_, lean_object* v_i_1881_, lean_object* v_x_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_N_1877_, v_i_1878_, v___x_1879_, v_i_1881_, v_x_1882_, v_a_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_N_1885_, lean_object* v_i_1886_, lean_object* v___x_1887_, lean_object* v_k_1888_, lean_object* v_i_1889_, lean_object* v_x_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = lp_tree_Pi_single___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__7(v_N_1885_, v_i_1886_, v___x_1887_, v_k_1888_, v_i_1889_, v_x_1890_, v_a_1891_);
lean_dec(v_x_1890_);
lean_dec(v_i_1889_);
lean_dec(v_k_1888_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8(lean_object* v_N_1893_, lean_object* v_i_1894_, lean_object* v___x_1895_, lean_object* v_k_1896_, lean_object* v_m_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_){
_start:
{
lean_object* v___f_1901_; 
v___f_1901_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8___redArg___lam__0), 7, 4);
lean_closure_set(v___f_1901_, 0, v_N_1893_);
lean_closure_set(v___f_1901_, 1, v_i_1894_);
lean_closure_set(v___f_1901_, 2, v___x_1895_);
lean_closure_set(v___f_1901_, 3, v_k_1896_);
return v___f_1901_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___redArg(lean_object* v_g_1902_){
_start:
{
lean_inc(v_g_1902_);
return v_g_1902_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___redArg___boxed(lean_object* v_g_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___redArg(v_g_1903_);
lean_dec(v_g_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16(lean_object* v_N_1905_, lean_object* v_i_1906_, lean_object* v___x_1907_, lean_object* v_k_1908_, lean_object* v_00_u03c3_1909_, lean_object* v_00_u03c3_x27_1910_, lean_object* v_inst_1911_, lean_object* v_f_1912_, lean_object* v_g_1913_, lean_object* v_h_u2081_1914_, lean_object* v_h_u2082_1915_){
_start:
{
lean_inc(v_g_1913_);
return v_g_1913_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16___boxed(lean_object* v_N_1916_, lean_object* v_i_1917_, lean_object* v___x_1918_, lean_object* v_k_1919_, lean_object* v_00_u03c3_1920_, lean_object* v_00_u03c3_x27_1921_, lean_object* v_inst_1922_, lean_object* v_f_1923_, lean_object* v_g_1924_, lean_object* v_h_u2081_1925_, lean_object* v_h_u2082_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = lp_tree_LinearMap_inverse___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__16(v_N_1916_, v_i_1917_, v___x_1918_, v_k_1919_, v_00_u03c3_1920_, v_00_u03c3_x27_1921_, v_inst_1922_, v_f_1923_, v_g_1924_, v_h_u2081_1925_, v_h_u2082_1926_);
lean_dec(v_g_1924_);
lean_dec(v_f_1923_);
lean_dec(v_00_u03c3_x27_1921_);
lean_dec(v_00_u03c3_1920_);
lean_dec(v_k_1919_);
lean_dec(v_i_1917_);
lean_dec_ref(v_N_1916_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10(lean_object* v_N_1928_, lean_object* v_i_1929_, lean_object* v___x_1930_, lean_object* v_k_1931_, lean_object* v_00_u03c3_1932_, lean_object* v_00_u03c3_x27_1933_, lean_object* v_re_u2081_1934_, lean_object* v_re_u2082_1935_, lean_object* v_e_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___redArg(v_N_1928_, v_i_1929_, v___x_1930_, v_k_1931_, v_00_u03c3_1932_, v_00_u03c3_x27_1933_, v_e_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_N_1938_, lean_object* v_i_1939_, lean_object* v___x_1940_, lean_object* v_k_1941_, lean_object* v_00_u03c3_1942_, lean_object* v_00_u03c3_x27_1943_, lean_object* v_re_u2081_1944_, lean_object* v_re_u2082_1945_, lean_object* v_e_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = lp_tree_LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10(v_N_1938_, v_i_1939_, v___x_1940_, v_k_1941_, v_00_u03c3_1942_, v_00_u03c3_x27_1943_, v_re_u2081_1944_, v_re_u2082_1945_, v_e_1946_);
lean_dec(v_00_u03c3_x27_1943_);
lean_dec(v_00_u03c3_1942_);
lean_dec(v_k_1941_);
lean_dec(v_i_1939_);
lean_dec_ref(v_N_1938_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13(lean_object* v_N_1948_, lean_object* v_i_1949_, lean_object* v___x_1950_, lean_object* v_k_1951_, lean_object* v_m_1952_, lean_object* v_M_1953_, lean_object* v_v_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13___redArg(v_N_1948_, v_i_1949_, v___x_1950_, v_k_1951_, v_M_1953_, v_v_1954_, v_x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22(lean_object* v_N_1957_, lean_object* v_i_1958_, lean_object* v___x_1959_, lean_object* v_k_1960_, lean_object* v_00_u03c3_1961_, lean_object* v_00_u03c3_x27_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_self_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___redArg(v_self_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___boxed(lean_object* v_N_1967_, lean_object* v_i_1968_, lean_object* v___x_1969_, lean_object* v_k_1970_, lean_object* v_00_u03c3_1971_, lean_object* v_00_u03c3_x27_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_self_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22(v_N_1967_, v_i_1968_, v___x_1969_, v_k_1970_, v_00_u03c3_1971_, v_00_u03c3_x27_1972_, v_inst_1973_, v_inst_1974_, v_self_1975_);
lean_dec(v_00_u03c3_x27_1972_);
lean_dec(v_00_u03c3_1971_);
lean_dec(v_k_1970_);
lean_dec(v_i_1968_);
lean_dec_ref(v_N_1967_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___redArg(lean_object* v_N_1977_, lean_object* v_i_1978_, lean_object* v___x_1979_, lean_object* v_k_1980_, lean_object* v_00_u03c3_1981_, lean_object* v_00_u03c3_x27_1982_, lean_object* v_e_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___redArg(v_e_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___redArg___boxed(lean_object* v_N_1985_, lean_object* v_i_1986_, lean_object* v___x_1987_, lean_object* v_k_1988_, lean_object* v_00_u03c3_1989_, lean_object* v_00_u03c3_x27_1990_, lean_object* v_e_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___redArg(v_N_1985_, v_i_1986_, v___x_1987_, v_k_1988_, v_00_u03c3_1989_, v_00_u03c3_x27_1990_, v_e_1991_);
lean_dec(v_00_u03c3_x27_1990_);
lean_dec(v_00_u03c3_1989_);
lean_dec(v_k_1988_);
lean_dec(v_i_1986_);
lean_dec_ref(v_N_1985_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17(lean_object* v_N_1993_, lean_object* v_i_1994_, lean_object* v___x_1995_, lean_object* v_k_1996_, lean_object* v_00_u03c3_1997_, lean_object* v_00_u03c3_x27_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_e_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = lp_tree_LinearEquiv_toAddEquiv___at___00LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17_spec__22___redArg(v_e_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17___boxed(lean_object* v_N_2003_, lean_object* v_i_2004_, lean_object* v___x_2005_, lean_object* v_k_2006_, lean_object* v_00_u03c3_2007_, lean_object* v_00_u03c3_x27_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_e_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = lp_tree_LinearEquiv_toEquiv___at___00LinearEquiv_symm___at___00AlgEquiv_ofLinearEquiv___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__6_spec__10_spec__17(v_N_2003_, v_i_2004_, v___x_2005_, v_k_2006_, v_00_u03c3_2007_, v_00_u03c3_x27_2008_, v_inst_2009_, v_inst_2010_, v_e_2011_);
lean_dec(v_00_u03c3_x27_2008_);
lean_dec(v_00_u03c3_2007_);
lean_dec(v_k_2006_);
lean_dec(v_i_2004_);
lean_dec_ref(v_N_2003_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___redArg(lean_object* v_r_2013_){
_start:
{
lean_inc(v_r_2013_);
return v_r_2013_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_r_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___redArg(v_r_2014_);
lean_dec(v_r_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21(lean_object* v_N_2016_, lean_object* v_i_2017_, lean_object* v___x_2018_, lean_object* v_S_2019_, lean_object* v_r_2020_, lean_object* v_s_2021_){
_start:
{
lean_inc(v_r_2020_);
return v_r_2020_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21___boxed(lean_object* v_N_2022_, lean_object* v_i_2023_, lean_object* v___x_2024_, lean_object* v_S_2025_, lean_object* v_r_2026_, lean_object* v_s_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = lp_tree_OreLocalization_oreNum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__21(v_N_2022_, v_i_2023_, v___x_2024_, v_S_2025_, v_r_2026_, v_s_2027_);
lean_dec(v_s_2027_);
lean_dec(v_r_2026_);
lean_dec(v_i_2023_);
lean_dec_ref(v_N_2022_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___redArg(lean_object* v_s_2029_){
_start:
{
lean_inc(v_s_2029_);
return v_s_2029_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___redArg___boxed(lean_object* v_s_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___redArg(v_s_2030_);
lean_dec(v_s_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22(lean_object* v_N_2032_, lean_object* v_i_2033_, lean_object* v___x_2034_, lean_object* v_S_2035_, lean_object* v_r_2036_, lean_object* v_s_2037_){
_start:
{
lean_inc(v_s_2037_);
return v_s_2037_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22___boxed(lean_object* v_N_2038_, lean_object* v_i_2039_, lean_object* v___x_2040_, lean_object* v_S_2041_, lean_object* v_r_2042_, lean_object* v_s_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = lp_tree_OreLocalization_oreDenom___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__22(v_N_2038_, v_i_2039_, v___x_2040_, v_S_2041_, v_r_2042_, v_s_2043_);
lean_dec(v_s_2043_);
lean_dec(v_r_2042_);
lean_dec(v_i_2039_);
lean_dec_ref(v_N_2038_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23(lean_object* v_N_2045_, lean_object* v_i_2046_, lean_object* v___x_2047_, lean_object* v_S_2048_, lean_object* v_C_2049_, lean_object* v_P_2050_, lean_object* v_hP_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___redArg(v_P_2050_, v_a_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23___boxed(lean_object* v_N_2054_, lean_object* v_i_2055_, lean_object* v___x_2056_, lean_object* v_S_2057_, lean_object* v_C_2058_, lean_object* v_P_2059_, lean_object* v_hP_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = lp_tree_OreLocalization_liftExpand___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__23(v_N_2054_, v_i_2055_, v___x_2056_, v_S_2057_, v_C_2058_, v_P_2059_, v_hP_2060_, v_a_2061_);
lean_dec(v_i_2055_);
lean_dec_ref(v_N_2054_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24(lean_object* v_N_2063_, lean_object* v_i_2064_, lean_object* v___x_2065_, lean_object* v_00_u03b9_2066_, lean_object* v_s_2067_, lean_object* v_f_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24___redArg(v_N_2063_, v_i_2064_, v___x_2065_, v_s_2067_, v_f_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___redArg(lean_object* v_s_2070_){
_start:
{
lean_inc(v_s_2070_);
return v_s_2070_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_s_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___redArg(v_s_2071_);
lean_dec(v_s_2071_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31(lean_object* v_N_2073_, lean_object* v_i_2074_, lean_object* v___x_2075_, lean_object* v_S_2076_, lean_object* v_r_2077_, lean_object* v_s_2078_){
_start:
{
lean_inc(v_s_2078_);
return v_s_2078_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31___boxed(lean_object* v_N_2079_, lean_object* v_i_2080_, lean_object* v___x_2081_, lean_object* v_S_2082_, lean_object* v_r_2083_, lean_object* v_s_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__31(v_N_2079_, v_i_2080_, v___x_2081_, v_S_2082_, v_r_2083_, v_s_2084_);
lean_dec(v_s_2084_);
lean_dec(v_r_2083_);
lean_dec(v_i_2080_);
lean_dec_ref(v_N_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___redArg(lean_object* v_r_2086_){
_start:
{
lean_inc(v_r_2086_);
return v_r_2086_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___redArg___boxed(lean_object* v_r_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___redArg(v_r_2087_);
lean_dec(v_r_2087_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32(lean_object* v_N_2089_, lean_object* v_i_2090_, lean_object* v___x_2091_, lean_object* v_S_2092_, lean_object* v_r_2093_, lean_object* v_s_2094_){
_start:
{
lean_inc(v_r_2093_);
return v_r_2093_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32___boxed(lean_object* v_N_2095_, lean_object* v_i_2096_, lean_object* v___x_2097_, lean_object* v_S_2098_, lean_object* v_r_2099_, lean_object* v_s_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__32(v_N_2095_, v_i_2096_, v___x_2097_, v_S_2098_, v_r_2099_, v_s_2100_);
lean_dec(v_s_2100_);
lean_dec(v_r_2099_);
lean_dec(v_i_2096_);
lean_dec_ref(v_N_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33___redArg(lean_object* v_r_2102_, lean_object* v_s_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v_r_2102_);
lean_ctor_set(v___x_2104_, 1, v_s_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33(lean_object* v_N_2105_, lean_object* v_i_2106_, lean_object* v___x_2107_, lean_object* v_S_2108_, lean_object* v_r_2109_, lean_object* v_s_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_r_2109_);
lean_ctor_set(v___x_2111_, 1, v_s_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33___boxed(lean_object* v_N_2112_, lean_object* v_i_2113_, lean_object* v___x_2114_, lean_object* v_S_2115_, lean_object* v_r_2116_, lean_object* v_s_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00LinearMap_toMatrixAlgEquiv_x27___at___00Matrix_toLinAlgEquiv_x27___at___00Formalism_MainNotions_N_matRep___at___00Formalism_MainNotions_N_repK_spec__1_spec__2_spec__3_spec__5_spec__8_spec__13_spec__18_spec__24_spec__27_spec__28_spec__29_spec__30_spec__33(v_N_2112_, v_i_2113_, v___x_2114_, v_S_2115_, v_r_2116_, v_s_2117_);
lean_dec(v_i_2113_);
lean_dec_ref(v_N_2112_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_VS(lean_object* v_R_2119_, lean_object* v_H_2120_, lean_object* v_what_u2082_2121_, lean_object* v_N_2122_, lean_object* v_i_2123_, lean_object* v_Y_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_box(0);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_VS___boxed(lean_object* v_R_2126_, lean_object* v_H_2127_, lean_object* v_what_u2082_2128_, lean_object* v_N_2129_, lean_object* v_i_2130_, lean_object* v_Y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = lp_tree_Formalism_MainNotions_N_VS(v_R_2126_, v_H_2127_, v_what_u2082_2128_, v_N_2129_, v_i_2130_, v_Y_2131_);
lean_dec(v_i_2130_);
lean_dec_ref(v_N_2129_);
lean_dec_ref(v_what_u2082_2128_);
lean_dec_ref(v_H_2127_);
lean_dec_ref(v_R_2126_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtIn(lean_object* v_R_2133_, lean_object* v_H_2134_, lean_object* v_what_u2082_2135_, lean_object* v_N_2136_, lean_object* v_i_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtIn___boxed(lean_object* v_R_2139_, lean_object* v_H_2140_, lean_object* v_what_u2082_2141_, lean_object* v_N_2142_, lean_object* v_i_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = lp_tree_Formalism_MainNotions_N_MtIn(v_R_2139_, v_H_2140_, v_what_u2082_2141_, v_N_2142_, v_i_2143_);
lean_dec(v_i_2143_);
lean_dec_ref(v_N_2142_);
lean_dec_ref(v_what_u2082_2141_);
lean_dec_ref(v_H_2140_);
lean_dec_ref(v_R_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtUp(lean_object* v_R_2145_, lean_object* v_H_2146_, lean_object* v_what_u2082_2147_, lean_object* v_N_2148_, lean_object* v_i_2149_, lean_object* v_Z_x27_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = lean_box(0);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtUp___boxed(lean_object* v_R_2152_, lean_object* v_H_2153_, lean_object* v_what_u2082_2154_, lean_object* v_N_2155_, lean_object* v_i_2156_, lean_object* v_Z_x27_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = lp_tree_Formalism_MainNotions_N_MtUp(v_R_2152_, v_H_2153_, v_what_u2082_2154_, v_N_2155_, v_i_2156_, v_Z_x27_2157_);
lean_dec(v_Z_x27_2157_);
lean_dec(v_i_2156_);
lean_dec_ref(v_N_2155_);
lean_dec_ref(v_what_u2082_2154_);
lean_dec_ref(v_H_2153_);
lean_dec_ref(v_R_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtLow(lean_object* v_R_2159_, lean_object* v_H_2160_, lean_object* v_what_u2082_2161_, lean_object* v_N_2162_, lean_object* v_i_2163_, lean_object* v_Z_x27_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_box(0);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_MtLow___boxed(lean_object* v_R_2166_, lean_object* v_H_2167_, lean_object* v_what_u2082_2168_, lean_object* v_N_2169_, lean_object* v_i_2170_, lean_object* v_Z_x27_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = lp_tree_Formalism_MainNotions_N_MtLow(v_R_2166_, v_H_2167_, v_what_u2082_2168_, v_N_2169_, v_i_2170_, v_Z_x27_2171_);
lean_dec(v_Z_x27_2171_);
lean_dec(v_i_2170_);
lean_dec_ref(v_N_2169_);
lean_dec_ref(v_what_u2082_2168_);
lean_dec_ref(v_H_2167_);
lean_dec_ref(v_R_2166_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLat(lean_object* v_R_2173_, lean_object* v_H_2174_, lean_object* v_what_u2082_2175_, lean_object* v_N_2176_, lean_object* v_i_2177_, lean_object* v_00_u0393_2178_, lean_object* v_inst_2179_, lean_object* v_k_2180_, lean_object* v_M_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_box(0);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLat___boxed(lean_object* v_R_2183_, lean_object* v_H_2184_, lean_object* v_what_u2082_2185_, lean_object* v_N_2186_, lean_object* v_i_2187_, lean_object* v_00_u0393_2188_, lean_object* v_inst_2189_, lean_object* v_k_2190_, lean_object* v_M_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = lp_tree_Formalism_MainNotions_N_stdLat(v_R_2183_, v_H_2184_, v_what_u2082_2185_, v_N_2186_, v_i_2187_, v_00_u0393_2188_, v_inst_2189_, v_k_2190_, v_M_2191_);
lean_dec(v_M_2191_);
lean_dec(v_k_2190_);
lean_dec_ref(v_inst_2189_);
lean_dec(v_i_2187_);
lean_dec_ref(v_N_2186_);
lean_dec_ref(v_what_u2082_2185_);
lean_dec_ref(v_H_2184_);
lean_dec_ref(v_R_2183_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep___redArg___lam__0(lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_inst_2195_, lean_object* v_00_u03c1_2196_, lean_object* v_L_2197_, lean_object* v_g_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_52__overap_2200_; lean_object* v___x_2201_; 
v___x_52__overap_2200_ = lp_tree_Formalism_WeaklyAdmissibleFiltrations_actD___redArg(v_inst_2193_, v_inst_2194_, v_inst_2195_, v_00_u03c1_2196_, v_L_2197_, v_g_2198_);
v___x_2201_ = lean_apply_1(v___x_52__overap_2200_, v___y_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep___redArg(lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_00_u03c1_2205_, lean_object* v_L_2206_){
_start:
{
lean_object* v___f_2207_; 
v___f_2207_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_actRep___redArg___lam__0), 7, 5);
lean_closure_set(v___f_2207_, 0, v_inst_2202_);
lean_closure_set(v___f_2207_, 1, v_inst_2203_);
lean_closure_set(v___f_2207_, 2, v_inst_2204_);
lean_closure_set(v___f_2207_, 3, v_00_u03c1_2205_);
lean_closure_set(v___f_2207_, 4, v_L_2206_);
return v___f_2207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep(lean_object* v_O_2208_, lean_object* v_LL_2209_, lean_object* v_G_2210_, lean_object* v_V_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_00_u03c1_2220_, lean_object* v_L_2221_){
_start:
{
lean_object* v___f_2222_; 
v___f_2222_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_actRep___redArg___lam__0), 7, 5);
lean_closure_set(v___f_2222_, 0, v_inst_2212_);
lean_closure_set(v___f_2222_, 1, v_inst_2216_);
lean_closure_set(v___f_2222_, 2, v_inst_2218_);
lean_closure_set(v___f_2222_, 3, v_00_u03c1_2220_);
lean_closure_set(v___f_2222_, 4, v_L_2221_);
return v___f_2222_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_actRep___boxed(lean_object* v_O_2223_, lean_object* v_LL_2224_, lean_object* v_G_2225_, lean_object* v_V_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_00_u03c1_2235_, lean_object* v_L_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = lp_tree_Formalism_MainNotions_N_actRep(v_O_2223_, v_LL_2224_, v_G_2225_, v_V_2226_, v_inst_2227_, v_inst_2228_, v_inst_2229_, v_inst_2230_, v_inst_2231_, v_inst_2232_, v_inst_2233_, v_inst_2234_, v_00_u03c1_2235_, v_L_2236_);
lean_dec(v_inst_2232_);
lean_dec_ref(v_inst_2230_);
lean_dec_ref(v_inst_2229_);
lean_dec_ref(v_inst_2228_);
return v_res_2237_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__0(void){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = lp_mathlib_TopologicalSpace_instCompleteLattice(lean_box(0));
return v___x_2238_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_obj_once(&lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__0, &lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__0_once, _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__0);
v___x_2240_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr(lean_object* v_R_2241_, lean_object* v_H_2242_, lean_object* v_what_u2082_2243_, lean_object* v_N_2244_, lean_object* v_i_2245_){
_start:
{
lean_object* v___x_2246_; lean_object* v_toOrderBot_2247_; 
v___x_2246_ = lean_obj_once(&lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1, &lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1_once, _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1);
v_toOrderBot_2247_ = lean_ctor_get(v___x_2246_, 2);
lean_inc(v_toOrderBot_2247_);
return v_toOrderBot_2247_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___boxed(lean_object* v_R_2248_, lean_object* v_H_2249_, lean_object* v_what_u2082_2250_, lean_object* v_N_2251_, lean_object* v_i_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr(v_R_2248_, v_H_2249_, v_what_u2082_2250_, v_N_2251_, v_i_2252_);
lean_dec(v_i_2252_);
lean_dec_ref(v_N_2251_);
lean_dec_ref(v_what_u2082_2250_);
lean_dec_ref(v_H_2249_);
lean_dec_ref(v_R_2248_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2_spec__4(lean_object* v_N_2254_, lean_object* v_i_2255_, lean_object* v_s_2256_){
_start:
{
lean_object* v_instO_2257_; lean_object* v___x_2258_; lean_object* v_toSemiring_2259_; lean_object* v_toAddCommMonoid_2260_; lean_object* v___x_2261_; lean_object* v_toZero_2262_; lean_object* v_toAdd_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; 
v_instO_2257_ = lean_ctor_get(v_N_2254_, 9);
lean_inc_ref(v_instO_2257_);
lean_dec_ref(v_N_2254_);
v___x_2258_ = lean_apply_1(v_instO_2257_, v_i_2255_);
v_toSemiring_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc_ref(v_toSemiring_2259_);
lean_dec_ref(v___x_2258_);
v_toAddCommMonoid_2260_ = lean_ctor_get(v_toSemiring_2259_, 0);
lean_inc_ref(v_toAddCommMonoid_2260_);
lean_dec_ref(v_toSemiring_2259_);
v___x_2261_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_2260_);
lean_dec_ref(v_toAddCommMonoid_2260_);
v_toZero_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_toZero_2262_);
v_toAdd_2263_ = lean_ctor_get(v___x_2261_, 1);
lean_inc(v_toAdd_2263_);
lean_dec_ref(v___x_2261_);
v___f_2264_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9_spec__12_spec__13___lam__0), 3, 1);
lean_closure_set(v___f_2264_, 0, v_toAdd_2263_);
v___x_2265_ = l_List_foldrTR___redArg(v___f_2264_, v_toZero_2262_, v_s_2256_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2___redArg(lean_object* v_N_2266_, lean_object* v_i_2267_, lean_object* v_s_2268_, lean_object* v_f_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lp_mathlib_Multiset_map___redArg(v_f_2269_, v_s_2268_);
v___x_2271_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2_spec__4(v_N_2266_, v_i_2267_, v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1(lean_object* v___x_2272_, lean_object* v_N_2273_, lean_object* v_i_2274_, lean_object* v_v_2275_, lean_object* v_w_2276_){
_start:
{
lean_object* v_instO_2277_; lean_object* v___x_2278_; lean_object* v_toSemiring_2279_; lean_object* v___x_2280_; lean_object* v_toMul_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_instO_2277_ = lean_ctor_get(v_N_2273_, 9);
lean_inc_ref(v_instO_2277_);
lean_inc(v_i_2274_);
v___x_2278_ = lean_apply_1(v_instO_2277_, v_i_2274_);
v_toSemiring_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref(v_toSemiring_2279_);
lean_dec_ref(v___x_2278_);
v___x_2280_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_2279_);
v_toMul_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_toMul_2281_);
lean_dec_ref(v___x_2280_);
v___f_2282_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6_spec__9___lam__0), 4, 3);
lean_closure_set(v___f_2282_, 0, v_v_2275_);
lean_closure_set(v___f_2282_, 1, v_w_2276_);
lean_closure_set(v___f_2282_, 2, v_toMul_2281_);
v___x_2283_ = l_List_finRange(v___x_2272_);
v___x_2284_ = lp_tree_Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2___redArg(v_N_2273_, v_i_2274_, v___x_2283_, v___f_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3___lam__1(lean_object* v_head_2285_, lean_object* v___y_2286_, lean_object* v_j_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_apply_2(v_head_2285_, v___y_2286_, v_j_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3(lean_object* v___x_2289_, lean_object* v_N_2290_, lean_object* v_i_2291_, lean_object* v_init_2292_, lean_object* v_x_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
if (lean_obj_tag(v_x_2293_) == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_i_2291_);
lean_dec_ref(v_N_2290_);
lean_dec(v___x_2289_);
v___x_2296_ = lean_apply_2(v_init_2292_, v___y_2294_, v___y_2295_);
return v___x_2296_;
}
else
{
lean_object* v_head_2297_; lean_object* v_tail_2298_; lean_object* v___f_2299_; lean_object* v___f_2300_; lean_object* v___x_2301_; 
v_head_2297_ = lean_ctor_get(v_x_2293_, 0);
lean_inc(v_head_2297_);
v_tail_2298_ = lean_ctor_get(v_x_2293_, 1);
lean_inc(v_tail_2298_);
lean_dec_ref_known(v_x_2293_, 2);
lean_inc(v_i_2291_);
lean_inc_ref(v_N_2290_);
lean_inc(v___x_2289_);
v___f_2299_ = lean_alloc_closure((void*)(lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3___lam__0), 7, 6);
lean_closure_set(v___f_2299_, 0, v___x_2289_);
lean_closure_set(v___f_2299_, 1, v_N_2290_);
lean_closure_set(v___f_2299_, 2, v_i_2291_);
lean_closure_set(v___f_2299_, 3, v_init_2292_);
lean_closure_set(v___f_2299_, 4, v_tail_2298_);
lean_closure_set(v___f_2299_, 5, v___y_2295_);
v___f_2300_ = lean_alloc_closure((void*)(lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3___lam__1), 3, 2);
lean_closure_set(v___f_2300_, 0, v_head_2297_);
lean_closure_set(v___f_2300_, 1, v___y_2294_);
v___x_2301_ = lp_tree_dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1(v___x_2289_, v_N_2290_, v_i_2291_, v___f_2300_, v___f_2299_);
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3___lam__0(lean_object* v___x_2302_, lean_object* v_N_2303_, lean_object* v_i_2304_, lean_object* v_init_2305_, lean_object* v_tail_2306_, lean_object* v___y_2307_, lean_object* v_j_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3(v___x_2302_, v_N_2303_, v_i_2304_, v_init_2305_, v_tail_2306_, v_j_2308_, v___y_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2___redArg(lean_object* v_N_2310_, lean_object* v_i_2311_, lean_object* v_d_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_instO_2315_; lean_object* v___x_2316_; lean_object* v_toSemiring_2317_; lean_object* v___x_2318_; lean_object* v_toZero_2319_; lean_object* v___x_2320_; lean_object* v_toFun_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
v_instO_2315_ = lean_ctor_get(v_N_2310_, 9);
lean_inc_ref(v_instO_2315_);
lean_dec_ref(v_N_2310_);
v___x_2316_ = lean_apply_1(v_instO_2315_, v_i_2311_);
v_toSemiring_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_ref(v_toSemiring_2317_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_2317_);
v_toZero_2319_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_toZero_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = lean_obj_once(&lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0, &lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0_once, _init_lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___closed__0);
v_toFun_2321_ = lean_ctor_get(v___x_2320_, 0);
v___f_2322_ = lean_alloc_closure((void*)(lp_tree_Matrix_diagonal___at___00Formalism_MainNotions_N_chiRatO_spec__0___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2322_, 0, v_toZero_2319_);
lean_closure_set(v___f_2322_, 1, v_d_2312_);
lean_inc(v_toFun_2321_);
v___x_2323_ = lean_apply_3(v_toFun_2321_, v___f_2322_, v_a_2313_, v_a_2314_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_MainNotions_N_Eel_spec__1___lam__1(lean_object* v_N_2324_, lean_object* v_i_2325_, lean_object* v___f_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2___redArg(v_N_2324_, v_i_2325_, v___f_2326_, v___y_2327_, v___y_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_MainNotions_N_Eel_spec__1(lean_object* v___x_2330_, lean_object* v_N_2331_, lean_object* v_i_2332_, lean_object* v_l_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_instO_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v_toAddMonoidWithOne_2339_; lean_object* v_toOne_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; 
v_instO_2336_ = lean_ctor_get(v_N_2331_, 9);
lean_inc_ref(v_instO_2336_);
lean_inc_n(v_i_2332_, 2);
v___x_2337_ = lean_apply_1(v_instO_2336_, v_i_2332_);
v___x_2338_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_2337_);
v_toAddMonoidWithOne_2339_ = lean_ctor_get(v___x_2338_, 1);
lean_inc_ref(v_toAddMonoidWithOne_2339_);
lean_dec_ref(v___x_2338_);
v_toOne_2340_ = lean_ctor_get(v_toAddMonoidWithOne_2339_, 2);
lean_inc(v_toOne_2340_);
lean_dec_ref(v_toAddMonoidWithOne_2339_);
v___f_2341_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_chiRatO___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2341_, 0, v_toOne_2340_);
lean_inc_ref(v_N_2331_);
v___f_2342_ = lean_alloc_closure((void*)(lp_tree_List_prod___at___00Formalism_MainNotions_N_Eel_spec__1___lam__1), 5, 3);
lean_closure_set(v___f_2342_, 0, v_N_2331_);
lean_closure_set(v___f_2342_, 1, v_i_2332_);
lean_closure_set(v___f_2342_, 2, v___f_2341_);
v___x_2343_ = lp_tree_List_foldr___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__3(v___x_2330_, v_N_2331_, v_i_2332_, v___f_2342_, v_l_2333_, v___y_2334_, v___y_2335_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_MainNotions_N_Eel_spec__0___lam__0(lean_object* v_S_2344_, lean_object* v_x_x27_2345_, lean_object* v_head_2346_, lean_object* v_toMul_2347_, lean_object* v_toSub_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_eB_2351_; lean_object* v_X0_2352_; lean_object* v_p_2353_; lean_object* v_rr_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_eB_2351_ = lean_ctor_get(v_S_2344_, 0);
lean_inc(v_eB_2351_);
v_X0_2352_ = lean_ctor_get(v_S_2344_, 3);
lean_inc(v_X0_2352_);
v_p_2353_ = lean_ctor_get(v_S_2344_, 6);
lean_inc(v_p_2353_);
v_rr_2354_ = lean_ctor_get(v_S_2344_, 8);
lean_inc(v_rr_2354_);
lean_dec_ref(v_S_2344_);
lean_inc(v_x_x27_2345_);
v___x_2355_ = lean_apply_1(v_p_2353_, v_x_x27_2345_);
v___x_2356_ = lean_apply_2(v_rr_2354_, v_head_2346_, v_x_x27_2345_);
lean_inc(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc(v___x_2355_);
v___x_2357_ = lean_apply_3(v_X0_2352_, v___x_2355_, v___y_2349_, v___y_2350_);
v___x_2358_ = lean_apply_3(v_eB_2351_, v___x_2355_, v___y_2349_, v___y_2350_);
v___x_2359_ = lean_apply_2(v_toMul_2347_, v___x_2356_, v___x_2358_);
v___x_2360_ = lean_apply_2(v_toSub_2348_, v___x_2357_, v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_MainNotions_N_Eel_spec__0(lean_object* v_S_2361_, lean_object* v_x_x27_2362_, lean_object* v_N_2363_, lean_object* v_i_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_instO_2367_; lean_object* v___x_2368_; lean_object* v_toSemiring_2369_; lean_object* v___x_2370_; lean_object* v_toMul_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_instO_2367_ = lean_ctor_get(v_N_2363_, 9);
lean_inc_ref(v_instO_2367_);
lean_inc(v_i_2364_);
v___x_2368_ = lean_apply_1(v_instO_2367_, v_i_2364_);
v_toSemiring_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_ref(v_toSemiring_2369_);
v___x_2370_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_2369_);
v_toMul_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_toMul_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_2368_);
v___x_2373_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_2372_);
lean_dec_ref(v___x_2372_);
if (lean_obj_tag(v_a_2365_) == 0)
{
lean_object* v___x_2374_; 
lean_dec_ref(v___x_2373_);
lean_dec(v_toMul_2371_);
lean_dec(v_i_2364_);
lean_dec_ref(v_N_2363_);
lean_dec(v_x_x27_2362_);
lean_dec_ref(v_S_2361_);
v___x_2374_ = l_List_reverse___redArg(v_a_2366_);
return v___x_2374_;
}
else
{
lean_object* v_toSub_2375_; lean_object* v_head_2376_; lean_object* v_tail_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2386_; 
v_toSub_2375_ = lean_ctor_get(v___x_2373_, 2);
lean_inc(v_toSub_2375_);
lean_dec_ref(v___x_2373_);
v_head_2376_ = lean_ctor_get(v_a_2365_, 0);
v_tail_2377_ = lean_ctor_get(v_a_2365_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_a_2365_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2379_ = v_a_2365_;
v_isShared_2380_ = v_isSharedCheck_2386_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_tail_2377_);
lean_inc(v_head_2376_);
lean_dec(v_a_2365_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2386_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___f_2381_; lean_object* v___x_2383_; 
lean_inc(v_x_x27_2362_);
lean_inc_ref(v_S_2361_);
v___f_2381_ = lean_alloc_closure((void*)(lp_tree_List_mapTR_loop___at___00Formalism_MainNotions_N_Eel_spec__0___lam__0), 7, 5);
lean_closure_set(v___f_2381_, 0, v_S_2361_);
lean_closure_set(v___f_2381_, 1, v_x_x27_2362_);
lean_closure_set(v___f_2381_, 2, v_head_2376_);
lean_closure_set(v___f_2381_, 3, v_toMul_2371_);
lean_closure_set(v___f_2381_, 4, v_toSub_2375_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_a_2366_);
lean_ctor_set(v___x_2379_, 0, v___f_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___f_2381_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2366_);
v___x_2383_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
v_a_2365_ = v_tail_2377_;
v_a_2366_ = v___x_2383_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel___redArg(lean_object* v_R_2387_, lean_object* v_N_2388_, lean_object* v_i_2389_, lean_object* v_S_2390_, lean_object* v_x_x27_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_t_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_t_2394_ = lean_ctor_get(v_R_2387_, 3);
v___x_2395_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_2387_);
v___x_2396_ = lean_unsigned_to_nat(2u);
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_sub(v_t_2394_, v___x_2397_);
v___x_2399_ = lean_nat_add(v___x_2396_, v___x_2398_);
v___x_2400_ = lean_box(0);
v___x_2401_ = l_List_range_x27TR_go(v___x_2397_, v___x_2398_, v___x_2399_, v___x_2400_);
lean_inc(v_i_2389_);
lean_inc_ref(v_N_2388_);
v___x_2402_ = lp_tree_List_mapTR_loop___at___00Formalism_MainNotions_N_Eel_spec__0(v_S_2390_, v_x_x27_2391_, v_N_2388_, v_i_2389_, v___x_2401_, v___x_2400_);
v___x_2403_ = lp_tree_List_prod___at___00Formalism_MainNotions_N_Eel_spec__1(v___x_2395_, v_N_2388_, v_i_2389_, v___x_2402_, v_a_2392_, v_a_2393_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel___redArg___boxed(lean_object* v_R_2404_, lean_object* v_N_2405_, lean_object* v_i_2406_, lean_object* v_S_2407_, lean_object* v_x_x27_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = lp_tree_Formalism_MainNotions_N_Eel___redArg(v_R_2404_, v_N_2405_, v_i_2406_, v_S_2407_, v_x_x27_2408_, v_a_2409_, v_a_2410_);
lean_dec_ref(v_R_2404_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel(lean_object* v_R_2412_, lean_object* v_H_2413_, lean_object* v_what_u2082_2414_, lean_object* v_N_2415_, lean_object* v_i_2416_, lean_object* v_S_2417_, lean_object* v_x_x27_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lp_tree_Formalism_MainNotions_N_Eel___redArg(v_R_2412_, v_N_2415_, v_i_2416_, v_S_2417_, v_x_x27_2418_, v_a_2419_, v_a_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Eel___boxed(lean_object* v_R_2422_, lean_object* v_H_2423_, lean_object* v_what_u2082_2424_, lean_object* v_N_2425_, lean_object* v_i_2426_, lean_object* v_S_2427_, lean_object* v_x_x27_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = lp_tree_Formalism_MainNotions_N_Eel(v_R_2422_, v_H_2423_, v_what_u2082_2424_, v_N_2425_, v_i_2426_, v_S_2427_, v_x_x27_2428_, v_a_2429_, v_a_2430_);
lean_dec_ref(v_what_u2082_2424_);
lean_dec_ref(v_H_2423_);
lean_dec_ref(v_R_2422_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2(lean_object* v___x_2432_, lean_object* v_N_2433_, lean_object* v_i_2434_, lean_object* v_d_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2___redArg(v_N_2433_, v_i_2434_, v_d_2435_, v_a_2436_, v_a_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2___boxed(lean_object* v___x_2439_, lean_object* v_N_2440_, lean_object* v_i_2441_, lean_object* v_d_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = lp_tree_Matrix_diagonal___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__2(v___x_2439_, v_N_2440_, v_i_2441_, v_d_2442_, v_a_2443_, v_a_2444_);
lean_dec(v___x_2439_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2(lean_object* v_N_2446_, lean_object* v_i_2447_, lean_object* v_00_u03b9_2448_, lean_object* v_s_2449_, lean_object* v_f_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = lp_tree_Finset_sum___at___00dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1_spec__2___redArg(v_N_2446_, v_i_2447_, v_s_2449_, v_f_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_Ioc___at___00Formalism_MainNotions_N_del51_spec__0(lean_object* v_a_2452_, lean_object* v_b_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_nat_add(v_a_2452_, v___x_2454_);
v___x_2456_ = lean_nat_sub(v_b_2453_, v_a_2452_);
v___x_2457_ = lean_nat_add(v___x_2455_, v___x_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v___x_2459_ = l_List_range_x27TR_go(v___x_2454_, v___x_2456_, v___x_2457_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_Ioc___at___00Formalism_MainNotions_N_del51_spec__0___boxed(lean_object* v_a_2460_, lean_object* v_b_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = lp_tree_Finset_Ioc___at___00Formalism_MainNotions_N_del51_spec__0(v_a_2460_, v_b_2461_);
lean_dec(v_b_2461_);
lean_dec(v_a_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___redArg___lam__0(lean_object* v_S_2463_, lean_object* v___x_2464_, lean_object* v_x_x27_2465_, lean_object* v_toSub_2466_, lean_object* v_c_2467_){
_start:
{
lean_object* v_rr_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_rr_2468_ = lean_ctor_get(v_S_2463_, 8);
lean_inc_n(v_rr_2468_, 2);
lean_dec_ref(v_S_2463_);
lean_inc(v_x_x27_2465_);
v___x_2469_ = lean_apply_2(v_rr_2468_, v___x_2464_, v_x_x27_2465_);
v___x_2470_ = lean_apply_2(v_rr_2468_, v_c_2467_, v_x_x27_2465_);
v___x_2471_ = lean_apply_2(v_toSub_2466_, v___x_2469_, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1_spec__1___lam__0(lean_object* v_toMul_2472_, lean_object* v_x1_2473_, lean_object* v_x2_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_apply_2(v_toMul_2472_, v_x1_2473_, v_x2_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1_spec__1(lean_object* v_N_2476_, lean_object* v_i_2477_, lean_object* v_s_2478_){
_start:
{
lean_object* v_instO_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_toOne_2483_; lean_object* v_toMul_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; 
v_instO_2479_ = lean_ctor_get(v_N_2476_, 9);
lean_inc_ref(v_instO_2479_);
lean_dec_ref(v_N_2476_);
v___x_2480_ = lean_apply_1(v_instO_2479_, v_i_2477_);
v___x_2481_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_2480_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_2481_);
lean_dec_ref(v___x_2481_);
v_toOne_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_toOne_2483_);
v_toMul_2484_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_toMul_2484_);
lean_dec_ref(v___x_2482_);
v___f_2485_ = lean_alloc_closure((void*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1_spec__1___lam__0), 3, 1);
lean_closure_set(v___f_2485_, 0, v_toMul_2484_);
v___x_2486_ = l_List_foldrTR___redArg(v___f_2485_, v_toOne_2483_, v_s_2478_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1___redArg(lean_object* v_N_2487_, lean_object* v_i_2488_, lean_object* v_s_2489_, lean_object* v_f_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lp_mathlib_Multiset_map___redArg(v_f_2490_, v_s_2489_);
v___x_2492_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1_spec__1(v_N_2487_, v_i_2488_, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___redArg(lean_object* v_R_2493_, lean_object* v_N_2494_, lean_object* v_i_2495_, lean_object* v_S_2496_, lean_object* v_x_x27_2497_){
_start:
{
lean_object* v_instO_2498_; lean_object* v___x_2499_; lean_object* v_t_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_toSub_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; 
v_instO_2498_ = lean_ctor_get(v_N_2494_, 9);
lean_inc_ref(v_instO_2498_);
lean_inc(v_i_2495_);
v___x_2499_ = lean_apply_1(v_instO_2498_, v_i_2495_);
v_t_2500_ = lean_ctor_get(v_R_2493_, 3);
v___x_2501_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_2499_);
v___x_2502_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_2501_);
lean_dec_ref(v___x_2501_);
v_toSub_2503_ = lean_ctor_get(v___x_2502_, 2);
lean_inc(v_toSub_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = lean_unsigned_to_nat(1u);
v___x_2505_ = lp_tree_Finset_Ioc___at___00Formalism_MainNotions_N_del51_spec__0(v___x_2504_, v_t_2500_);
v___f_2506_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_del51___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2506_, 0, v_S_2496_);
lean_closure_set(v___f_2506_, 1, v___x_2504_);
lean_closure_set(v___f_2506_, 2, v_x_x27_2497_);
lean_closure_set(v___f_2506_, 3, v_toSub_2503_);
v___x_2507_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1___redArg(v_N_2494_, v_i_2495_, v___x_2505_, v___f_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___redArg___boxed(lean_object* v_R_2508_, lean_object* v_N_2509_, lean_object* v_i_2510_, lean_object* v_S_2511_, lean_object* v_x_x27_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = lp_tree_Formalism_MainNotions_N_del51___redArg(v_R_2508_, v_N_2509_, v_i_2510_, v_S_2511_, v_x_x27_2512_);
lean_dec_ref(v_R_2508_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51(lean_object* v_R_2514_, lean_object* v_H_2515_, lean_object* v_what_u2082_2516_, lean_object* v_N_2517_, lean_object* v_i_2518_, lean_object* v_S_2519_, lean_object* v_x_x27_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = lp_tree_Formalism_MainNotions_N_del51___redArg(v_R_2514_, v_N_2517_, v_i_2518_, v_S_2519_, v_x_x27_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_del51___boxed(lean_object* v_R_2522_, lean_object* v_H_2523_, lean_object* v_what_u2082_2524_, lean_object* v_N_2525_, lean_object* v_i_2526_, lean_object* v_S_2527_, lean_object* v_x_x27_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = lp_tree_Formalism_MainNotions_N_del51(v_R_2522_, v_H_2523_, v_what_u2082_2524_, v_N_2525_, v_i_2526_, v_S_2527_, v_x_x27_2528_);
lean_dec_ref(v_what_u2082_2524_);
lean_dec_ref(v_H_2523_);
lean_dec_ref(v_R_2522_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1(lean_object* v_N_2530_, lean_object* v_i_2531_, lean_object* v_00_u03b9_2532_, lean_object* v_s_2533_, lean_object* v_f_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_N_del51_spec__1___redArg(v_N_2530_, v_i_2531_, v_s_2533_, v_f_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg___lam__0(lean_object* v_f_u2097_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_apply_2(v_f_u2097_2536_, v___y_2537_, v___y_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg(lean_object* v_f_u2097_2540_){
_start:
{
lean_object* v___f_2541_; 
v___f_2541_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2541_, 0, v_f_u2097_2540_);
return v___f_2541_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1(lean_object* v_N_2542_, lean_object* v_i_2543_, lean_object* v___x_2544_, lean_object* v_inst_2545_, lean_object* v_f_u2097_2546_){
_start:
{
lean_object* v___f_2547_; 
v___f_2547_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2547_, 0, v_f_u2097_2546_);
return v___f_2547_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___boxed(lean_object* v_N_2548_, lean_object* v_i_2549_, lean_object* v___x_2550_, lean_object* v_inst_2551_, lean_object* v_f_u2097_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1(v_N_2548_, v_i_2549_, v___x_2550_, v_inst_2551_, v_f_u2097_2552_);
lean_dec(v_i_2549_);
lean_dec_ref(v_N_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___redArg___lam__1(lean_object* v___f_2554_, lean_object* v___f_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_2554_, v___f_2555_, v___y_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17(lean_object* v_N_2558_, lean_object* v_i_2559_, lean_object* v___x_2560_, lean_object* v_S_2561_, lean_object* v_r_u2081_2562_, lean_object* v_s_u2081_2563_, lean_object* v_r_u2082_2564_, lean_object* v_s_u2082_2565_){
_start:
{
lean_object* v_instO_2566_; lean_object* v___x_2567_; lean_object* v_toSemiring_2568_; lean_object* v_toAddCommMonoid_2569_; lean_object* v_toMonoid_2570_; lean_object* v_toAddSemigroup_2571_; lean_object* v___x_2572_; lean_object* v_toMul_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2584_; 
v_instO_2566_ = lean_ctor_get(v_N_2558_, 9);
lean_inc_ref(v_instO_2566_);
lean_dec_ref(v_N_2558_);
v___x_2567_ = lean_apply_1(v_instO_2566_, v_i_2559_);
v_toSemiring_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_toSemiring_2568_);
lean_dec_ref(v___x_2567_);
v_toAddCommMonoid_2569_ = lean_ctor_get(v_toSemiring_2568_, 0);
lean_inc_ref(v_toAddCommMonoid_2569_);
v_toMonoid_2570_ = lean_ctor_get(v_toSemiring_2568_, 1);
lean_inc_ref(v_toMonoid_2570_);
lean_dec_ref(v_toSemiring_2568_);
v_toAddSemigroup_2571_ = lean_ctor_get(v_toAddCommMonoid_2569_, 0);
lean_inc(v_toAddSemigroup_2571_);
lean_dec_ref(v_toAddCommMonoid_2569_);
v___x_2572_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_2570_);
lean_dec_ref(v_toMonoid_2570_);
v_toMul_2573_ = lean_ctor_get(v___x_2572_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v___x_2572_, 0);
lean_dec(v_unused_2585_);
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_toMul_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_inc_n(v_toMul_2573_, 2);
lean_inc(v_s_u2082_2565_);
v___x_2577_ = lean_apply_2(v_toMul_2573_, v_s_u2082_2565_, v_r_u2081_2562_);
lean_inc(v_s_u2081_2563_);
v___x_2578_ = lean_apply_2(v_toMul_2573_, v_s_u2081_2563_, v_r_u2082_2564_);
v___x_2579_ = lean_apply_2(v_toAddSemigroup_2571_, v___x_2577_, v___x_2578_);
v___x_2580_ = lean_apply_2(v_toMul_2573_, v_s_u2082_2565_, v_s_u2081_2563_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2580_);
lean_ctor_set(v___x_2575_, 0, v___x_2579_);
v___x_2582_ = v___x_2575_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14(lean_object* v_N_2586_, lean_object* v_i_2587_, lean_object* v___x_2588_, lean_object* v_S_2589_, lean_object* v_r_u2082_2590_, lean_object* v_s_u2082_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_fst_2593_; lean_object* v_snd_2594_; lean_object* v___x_2595_; 
v_fst_2593_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_fst_2593_);
v_snd_2594_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2594_);
lean_dec(v_a_2592_);
v___x_2595_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17(v_N_2586_, v_i_2587_, v___x_2588_, v_S_2589_, v_fst_2593_, v_snd_2594_, v_r_u2082_2590_, v_s_u2082_2591_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12(lean_object* v_N_2596_, lean_object* v_i_2597_, lean_object* v___x_2598_, lean_object* v_S_2599_, lean_object* v_x_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_fst_2602_; lean_object* v_snd_2603_; lean_object* v___x_2604_; 
v_fst_2602_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_fst_2602_);
v_snd_2603_ = lean_ctor_get(v_a_2601_, 1);
lean_inc(v_snd_2603_);
lean_dec(v_a_2601_);
v___x_2604_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14(v_N_2596_, v_i_2597_, v___x_2598_, v_S_2599_, v_fst_2602_, v_snd_2603_, v_x_2600_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9___lam__0(lean_object* v_N_2605_, lean_object* v_i_2606_, lean_object* v___x_2607_, lean_object* v_x1_2608_, lean_object* v_x2_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12(v_N_2605_, v_i_2606_, v___x_2607_, v___x_2607_, v_x1_2608_, v_x2_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__13___redArg(lean_object* v_N_2611_, lean_object* v_i_2612_){
_start:
{
lean_object* v_instO_2613_; lean_object* v___x_2614_; lean_object* v_toSemiring_2615_; lean_object* v___x_2616_; lean_object* v_toMonoid_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v_toZero_2620_; lean_object* v___x_2621_; lean_object* v_toOne_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_instO_2613_ = lean_ctor_get(v_N_2611_, 9);
lean_inc_ref(v_instO_2613_);
lean_dec_ref(v_N_2611_);
v___x_2614_ = lean_apply_1(v_instO_2613_, v_i_2612_);
v_toSemiring_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_ref(v_toSemiring_2615_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_2615_);
lean_dec_ref(v_toSemiring_2615_);
v_toMonoid_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_ref(v_toMonoid_2617_);
v___x_2618_ = lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(v___x_2616_);
v___x_2619_ = lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(v___x_2618_);
v_toZero_2620_ = lean_ctor_get(v___x_2619_, 1);
lean_inc(v_toZero_2620_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_2617_);
lean_dec_ref(v_toMonoid_2617_);
v_toOne_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v___x_2621_, 1);
lean_dec(v_unused_2630_);
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_toOne_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v_toOne_2622_);
lean_ctor_set(v___x_2624_, 0, v_toZero_2620_);
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_toZero_2620_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_toOne_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9(lean_object* v_N_2631_, lean_object* v_i_2632_, lean_object* v___x_2633_, lean_object* v_s_2634_){
_start:
{
lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_inc(v_i_2632_);
lean_inc_ref(v_N_2631_);
v___f_2635_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9___lam__0), 5, 3);
lean_closure_set(v___f_2635_, 0, v_N_2631_);
lean_closure_set(v___f_2635_, 1, v_i_2632_);
lean_closure_set(v___f_2635_, 2, v___x_2633_);
v___x_2636_ = lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__13___redArg(v_N_2631_, v_i_2632_);
v___x_2637_ = l_List_foldrTR___redArg(v___f_2635_, v___x_2636_, v_s_2634_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_N_2638_, lean_object* v_i_2639_, lean_object* v___x_2640_, lean_object* v_s_2641_, lean_object* v_f_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lp_mathlib_Multiset_map___redArg(v_f_2642_, v_s_2641_);
v___x_2644_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9(v_N_2638_, v_i_2639_, v___x_2640_, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__0(lean_object* v_toMonoid_2645_, lean_object* v_x1_2646_, lean_object* v_x2_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v_toMul_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2660_; 
v___x_2650_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_2645_);
v_toMul_2651_ = lean_ctor_get(v___x_2650_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v___x_2650_, 0);
lean_dec(v_unused_2661_);
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_toMul_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_inc(v_toMul_2651_);
v___x_2655_ = lean_apply_2(v_toMul_2651_, v_x1_2646_, v___y_2648_);
v___x_2656_ = lean_apply_2(v_toMul_2651_, v___y_2649_, v_x2_2647_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2656_);
lean_ctor_set(v___x_2653_, 0, v___x_2655_);
v___x_2658_ = v___x_2653_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_toMonoid_2662_, lean_object* v_x1_2663_, lean_object* v_x2_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__0(v_toMonoid_2662_, v_x1_2663_, v_x2_2664_, v___y_2665_, v___y_2666_);
lean_dec_ref(v_toMonoid_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__1(lean_object* v_toMonoid_2668_, lean_object* v___x_2669_, lean_object* v_x1_2670_, lean_object* v_x2_2671_){
_start:
{
lean_object* v___f_2672_; lean_object* v___x_2673_; 
v___f_2672_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2672_, 0, v_toMonoid_2668_);
lean_closure_set(v___f_2672_, 1, v_x1_2670_);
lean_closure_set(v___f_2672_, 2, v_x2_2671_);
v___x_2673_ = lp_tree_OreLocalization_liftExpand___at___00TensorProduct_SMul_aux___at___00Module_End_genEigenspace___at___00Formalism_BasicNotions_heckeEig___at___00Formalism_BasicNotions_NData_eigSum_spec__0_spec__2_spec__6_spec__13___redArg(v___f_2672_, v___x_2669_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__2(lean_object* v_toSemiring_2674_, lean_object* v_v_2675_, lean_object* v_w_2676_, lean_object* v_i_2677_){
_start:
{
lean_object* v___x_2678_; lean_object* v_toMonoid_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; 
v___x_2678_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_2674_);
v_toMonoid_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc_ref(v_toMonoid_2679_);
lean_dec_ref(v___x_2678_);
lean_inc(v_i_2677_);
v___x_2680_ = lean_apply_1(v_v_2675_, v_i_2677_);
v___x_2681_ = lean_apply_1(v_w_2676_, v_i_2677_);
v___f_2682_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__1), 4, 2);
lean_closure_set(v___f_2682_, 0, v_toMonoid_2679_);
lean_closure_set(v___f_2682_, 1, v___x_2681_);
v___x_2683_ = lp_tree_OreLocalization_liftExpand___at___00TensorProduct_SMul_aux___at___00Module_End_genEigenspace___at___00Formalism_BasicNotions_heckeEig___at___00Formalism_BasicNotions_NData_eigSum_spec__0_spec__2_spec__6_spec__13___redArg(v___f_2682_, v___x_2680_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_toSemiring_2684_, lean_object* v_v_2685_, lean_object* v_w_2686_, lean_object* v_i_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__2(v_toSemiring_2684_, v_v_2685_, v_w_2686_, v_i_2687_);
lean_dec_ref(v_toSemiring_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2(lean_object* v___x_2689_, lean_object* v_N_2690_, lean_object* v_i_2691_, lean_object* v___x_2692_, lean_object* v_v_2693_, lean_object* v_w_2694_){
_start:
{
lean_object* v_instO_2695_; lean_object* v___x_2696_; lean_object* v_toSemiring_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_instO_2695_ = lean_ctor_get(v_N_2690_, 9);
lean_inc_ref(v_instO_2695_);
lean_inc(v_i_2691_);
v___x_2696_ = lean_apply_1(v_instO_2695_, v_i_2691_);
v_toSemiring_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc_ref(v_toSemiring_2697_);
lean_dec_ref(v___x_2696_);
v___f_2698_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2698_, 0, v_toSemiring_2697_);
lean_closure_set(v___f_2698_, 1, v_v_2693_);
lean_closure_set(v___f_2698_, 2, v_w_2694_);
v___x_2699_ = l_List_finRange(v___x_2689_);
v___x_2700_ = lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5___redArg(v_N_2690_, v_i_2691_, v___x_2692_, v___x_2699_, v___f_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0___redArg(lean_object* v_N_2701_, lean_object* v_i_2702_, lean_object* v___x_2703_, lean_object* v___x_2704_, lean_object* v_M_2705_, lean_object* v_v_2706_, lean_object* v_x_2707_){
_start:
{
lean_object* v___f_2708_; lean_object* v___x_2709_; 
v___f_2708_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00LinearMap_toMatrix_x27___at___00Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0_spec__3_spec__5_spec__6___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2708_, 0, v_M_2705_);
lean_closure_set(v___f_2708_, 1, v_x_2707_);
v___x_2709_ = lp_tree_dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2(v___x_2704_, v_N_2701_, v_i_2702_, v___x_2703_, v___f_2708_, v_v_2706_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg___lam__0(lean_object* v_N_2710_, lean_object* v_i_2711_, lean_object* v___x_2712_, lean_object* v___x_2713_, lean_object* v_M_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0___redArg(v_N_2710_, v_i_2711_, v___x_2712_, v___x_2713_, v_M_2714_, v___y_2715_, v___y_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg(lean_object* v_N_2718_, lean_object* v_i_2719_, lean_object* v___x_2720_, lean_object* v___x_2721_){
_start:
{
lean_object* v___f_2722_; 
v___f_2722_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2722_, 0, v_N_2718_);
lean_closure_set(v___f_2722_, 1, v_i_2719_);
lean_closure_set(v___f_2722_, 2, v___x_2720_);
lean_closure_set(v___f_2722_, 3, v___x_2721_);
return v___f_2722_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___lam__0(lean_object* v___y_2723_){
_start:
{
lean_inc(v___y_2723_);
return v___y_2723_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___lam__0___boxed(lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___lam__0(v___y_2724_);
lean_dec(v___y_2724_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3(lean_object* v_N_2727_, lean_object* v_i_2728_, lean_object* v___x_2729_, lean_object* v_p_2730_){
_start:
{
lean_object* v___f_2731_; 
v___f_2731_ = ((lean_object*)(lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___closed__0));
return v___f_2731_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___boxed(lean_object* v_N_2732_, lean_object* v_i_2733_, lean_object* v___x_2734_, lean_object* v_p_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3(v_N_2732_, v_i_2733_, v___x_2734_, v_p_2735_);
lean_dec(v_i_2733_);
lean_dec_ref(v_N_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg___lam__0(lean_object* v_f_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_apply_1(v_f_2737_, v___y_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg(lean_object* v_f_2740_){
_start:
{
lean_object* v___f_2741_; 
v___f_2741_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2741_, 0, v_f_2740_);
return v___f_2741_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0(lean_object* v_f_2742_, lean_object* v_x_2743_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = lean_apply_1(v_f_2742_, v_x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg(lean_object* v_c_2745_, lean_object* v_f_2746_){
_start:
{
lean_object* v___f_2747_; 
v___f_2747_ = lean_alloc_closure((void*)(lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2747_, 0, v_f_2746_);
return v___f_2747_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_con___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__10(lean_object* v_N_2748_, lean_object* v_i_2749_, lean_object* v_N_2750_, lean_object* v_nN_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_box(0);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_con___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__10___boxed(lean_object* v_N_2753_, lean_object* v_i_2754_, lean_object* v_N_2755_, lean_object* v_nN_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = lp_tree_QuotientAddGroup_con___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__10(v_N_2753_, v_i_2754_, v_N_2755_, v_nN_2756_);
lean_dec(v_i_2754_);
lean_dec_ref(v_N_2753_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___redArg(lean_object* v_N_2758_, lean_object* v_i_2759_, lean_object* v___x_2760_, lean_object* v_q_2761_, lean_object* v_N_2762_, lean_object* v_00_u03c6_2763_){
_start:
{
lean_object* v___f_2764_; 
v___f_2764_ = lean_alloc_closure((void*)(lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2764_, 0, v_00_u03c6_2763_);
return v___f_2764_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_N_2765_, lean_object* v_i_2766_, lean_object* v___x_2767_, lean_object* v_q_2768_, lean_object* v_N_2769_, lean_object* v_00_u03c6_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___redArg(v_N_2765_, v_i_2766_, v___x_2767_, v_q_2768_, v_N_2769_, v_00_u03c6_2770_);
lean_dec(v_i_2766_);
lean_dec_ref(v_N_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg(lean_object* v_N_2772_, lean_object* v_i_2773_, lean_object* v___x_2774_, lean_object* v_q_2775_, lean_object* v_p_2776_, lean_object* v_00_u03c4_u2081_u2082_2777_, lean_object* v_f_2778_){
_start:
{
lean_object* v___f_2779_; lean_object* v___f_2780_; 
v___f_2779_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2779_, 0, v_f_2778_);
v___f_2780_ = lean_alloc_closure((void*)(lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2780_, 0, v___f_2779_);
return v___f_2780_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg___boxed(lean_object* v_N_2781_, lean_object* v_i_2782_, lean_object* v___x_2783_, lean_object* v_q_2784_, lean_object* v_p_2785_, lean_object* v_00_u03c4_u2081_u2082_2786_, lean_object* v_f_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg(v_N_2781_, v_i_2782_, v___x_2783_, v_q_2784_, v_p_2785_, v_00_u03c4_u2081_u2082_2786_, v_f_2787_);
lean_dec(v_00_u03c4_u2081_u2082_2786_);
lean_dec(v_i_2782_);
lean_dec_ref(v_N_2781_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg(lean_object* v_N_2789_, lean_object* v_i_2790_, lean_object* v___x_2791_, lean_object* v_p_2792_, lean_object* v_00_u03c4_u2081_u2082_2793_, lean_object* v_q_2794_, lean_object* v_f_2795_){
_start:
{
lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; 
v___f_2796_ = ((lean_object*)(lp_tree_Submodule_mkQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__3___closed__0));
v___f_2797_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2797_, 0, v_f_2795_);
lean_closure_set(v___f_2797_, 1, v___f_2796_);
v___x_2798_ = lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg(v_N_2789_, v_i_2790_, v___x_2791_, v_q_2794_, v_p_2792_, v_00_u03c4_u2081_u2082_2793_, v___f_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg___boxed(lean_object* v_N_2799_, lean_object* v_i_2800_, lean_object* v___x_2801_, lean_object* v_p_2802_, lean_object* v_00_u03c4_u2081_u2082_2803_, lean_object* v_q_2804_, lean_object* v_f_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg(v_N_2799_, v_i_2800_, v___x_2801_, v_p_2802_, v_00_u03c4_u2081_u2082_2803_, v_q_2804_, v_f_2805_);
lean_dec(v_00_u03c4_u2081_u2082_2803_);
lean_dec(v_i_2800_);
lean_dec_ref(v_N_2799_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___redArg(lean_object* v_R_2807_, lean_object* v_N_2808_, lean_object* v_i_2809_, lean_object* v_A_2810_){
_start:
{
lean_object* v_instO_2811_; lean_object* v___x_2812_; lean_object* v_toSemiring_2813_; lean_object* v_toMonoid_2814_; lean_object* v___x_2815_; lean_object* v_toOne_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___f_2820_; lean_object* v___f_2821_; lean_object* v___f_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; 
v_instO_2811_ = lean_ctor_get(v_N_2808_, 9);
lean_inc_ref(v_instO_2811_);
lean_inc_n(v_i_2809_, 2);
v___x_2812_ = lean_apply_1(v_instO_2811_, v_i_2809_);
v_toSemiring_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_ref(v_toSemiring_2813_);
lean_dec_ref(v___x_2812_);
v_toMonoid_2814_ = lean_ctor_get(v_toSemiring_2813_, 1);
lean_inc_ref(v_toMonoid_2814_);
lean_dec_ref(v_toSemiring_2813_);
v___x_2815_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_2814_);
lean_dec_ref(v_toMonoid_2814_);
v_toOne_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_toOne_2816_);
lean_dec_ref(v___x_2815_);
v___x_2817_ = lean_box(0);
v___x_2818_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_2807_);
v___x_2819_ = lean_box(0);
v___f_2820_ = ((lean_object*)(lp_tree_Matrix_toLin_x27___at___00Formalism_MainNotions_N_glRep___at___00Formalism_MainNotions_N_Glob_Wp_spec__0_spec__0___redArg___closed__0));
v___f_2821_ = lean_alloc_closure((void*)(lp_tree_Algebra_linearMap___at___00Formalism_MainNotions_N_stdO_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2821_, 0, v_toOne_2816_);
v___f_2822_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_matQ___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2822_, 0, v___f_2820_);
lean_closure_set(v___f_2822_, 1, v___f_2821_);
v___x_2823_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_map), 8, 6);
lean_closure_set(v___x_2823_, 0, lean_box(0));
lean_closure_set(v___x_2823_, 1, lean_box(0));
lean_closure_set(v___x_2823_, 2, lean_box(0));
lean_closure_set(v___x_2823_, 3, lean_box(0));
lean_closure_set(v___x_2823_, 4, v_A_2810_);
lean_closure_set(v___x_2823_, 5, v___f_2822_);
lean_inc_ref(v_N_2808_);
v___x_2824_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg___lam__0), 7, 5);
lean_closure_set(v___x_2824_, 0, v_N_2808_);
lean_closure_set(v___x_2824_, 1, v_i_2809_);
lean_closure_set(v___x_2824_, 2, v___x_2817_);
lean_closure_set(v___x_2824_, 3, v___x_2818_);
lean_closure_set(v___x_2824_, 4, v___x_2823_);
v___f_2825_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_N_matQ_spec__1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2825_, 0, v___x_2824_);
v___x_2826_ = lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg(v_N_2808_, v_i_2809_, v___x_2817_, v___x_2819_, v___f_2820_, v___x_2819_, v___f_2825_);
lean_dec(v_i_2809_);
lean_dec_ref(v_N_2808_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___redArg___boxed(lean_object* v_R_2827_, lean_object* v_N_2828_, lean_object* v_i_2829_, lean_object* v_A_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = lp_tree_Formalism_MainNotions_N_matQ___redArg(v_R_2827_, v_N_2828_, v_i_2829_, v_A_2830_);
lean_dec_ref(v_R_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ(lean_object* v_R_2832_, lean_object* v_H_2833_, lean_object* v_what_u2082_2834_, lean_object* v_N_2835_, lean_object* v_i_2836_, lean_object* v_A_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = lp_tree_Formalism_MainNotions_N_matQ___redArg(v_R_2832_, v_N_2835_, v_i_2836_, v_A_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_matQ___boxed(lean_object* v_R_2839_, lean_object* v_H_2840_, lean_object* v_what_u2082_2841_, lean_object* v_N_2842_, lean_object* v_i_2843_, lean_object* v_A_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = lp_tree_Formalism_MainNotions_N_matQ(v_R_2839_, v_H_2840_, v_what_u2082_2841_, v_N_2842_, v_i_2843_, v_A_2844_);
lean_dec_ref(v_what_u2082_2841_);
lean_dec_ref(v_H_2840_);
lean_dec_ref(v_R_2839_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0(lean_object* v_N_2846_, lean_object* v_i_2847_, lean_object* v___x_2848_, lean_object* v___x_2849_, lean_object* v_m_2850_, lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_inst_2853_){
_start:
{
lean_object* v___f_2854_; 
v___f_2854_ = lean_alloc_closure((void*)(lp_tree_Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0___redArg___lam__0), 7, 4);
lean_closure_set(v___f_2854_, 0, v_N_2846_);
lean_closure_set(v___f_2854_, 1, v_i_2847_);
lean_closure_set(v___f_2854_, 2, v___x_2848_);
lean_closure_set(v___f_2854_, 3, v___x_2849_);
return v___f_2854_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2(lean_object* v_N_2855_, lean_object* v_i_2856_, lean_object* v___x_2857_, lean_object* v_p_2858_, lean_object* v_00_u03c4_u2081_u2082_2859_, lean_object* v_q_2860_, lean_object* v_f_2861_, lean_object* v_h_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___redArg(v_N_2855_, v_i_2856_, v___x_2857_, v_p_2858_, v_00_u03c4_u2081_u2082_2859_, v_q_2860_, v_f_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2___boxed(lean_object* v_N_2864_, lean_object* v_i_2865_, lean_object* v___x_2866_, lean_object* v_p_2867_, lean_object* v_00_u03c4_u2081_u2082_2868_, lean_object* v_q_2869_, lean_object* v_f_2870_, lean_object* v_h_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = lp_tree_Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2(v_N_2864_, v_i_2865_, v___x_2866_, v_p_2867_, v_00_u03c4_u2081_u2082_2868_, v_q_2869_, v_f_2870_, v_h_2871_);
lean_dec(v_00_u03c4_u2081_u2082_2868_);
lean_dec(v_i_2865_);
lean_dec_ref(v_N_2864_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0(lean_object* v_N_2873_, lean_object* v_i_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v_m_2877_, lean_object* v_M_2878_, lean_object* v_v_2879_, lean_object* v_x_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = lp_tree_Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0___redArg(v_N_2873_, v_i_2874_, v___x_2875_, v___x_2876_, v_M_2878_, v_v_2879_, v_x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6___redArg(lean_object* v_p_2882_){
_start:
{
return v_p_2882_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6(lean_object* v_N_2883_, lean_object* v_i_2884_, lean_object* v___x_2885_, lean_object* v_p_2886_){
_start:
{
return v_p_2886_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6___boxed(lean_object* v_N_2887_, lean_object* v_i_2888_, lean_object* v___x_2889_, lean_object* v_p_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = lp_tree_Submodule_toAddSubgroup___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__6(v_N_2887_, v_i_2888_, v___x_2889_, v_p_2890_);
lean_dec(v_i_2888_);
lean_dec_ref(v_N_2887_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7(lean_object* v_N_2892_, lean_object* v_i_2893_, lean_object* v___x_2894_, lean_object* v_q_2895_, lean_object* v_00_u03c3_2896_, lean_object* v_f_2897_){
_start:
{
lean_object* v___f_2898_; 
v___f_2898_ = lean_alloc_closure((void*)(lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2898_, 0, v_f_2897_);
return v___f_2898_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7___boxed(lean_object* v_N_2899_, lean_object* v_i_2900_, lean_object* v___x_2901_, lean_object* v_q_2902_, lean_object* v_00_u03c3_2903_, lean_object* v_f_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = lp_tree_LinearMap_toAddMonoidHom___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__7(v_N_2899_, v_i_2900_, v___x_2901_, v_q_2902_, v_00_u03c3_2903_, v_f_2904_);
lean_dec(v_00_u03c3_2903_);
lean_dec(v_i_2900_);
lean_dec_ref(v_N_2899_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4(lean_object* v_N_2906_, lean_object* v_i_2907_, lean_object* v___x_2908_, lean_object* v_q_2909_, lean_object* v_p_2910_, lean_object* v_00_u03c4_u2081_u2082_2911_, lean_object* v_f_2912_, lean_object* v_h_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___redArg(v_N_2906_, v_i_2907_, v___x_2908_, v_q_2909_, v_p_2910_, v_00_u03c4_u2081_u2082_2911_, v_f_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4___boxed(lean_object* v_N_2915_, lean_object* v_i_2916_, lean_object* v___x_2917_, lean_object* v_q_2918_, lean_object* v_p_2919_, lean_object* v_00_u03c4_u2081_u2082_2920_, lean_object* v_f_2921_, lean_object* v_h_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = lp_tree_Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4(v_N_2915_, v_i_2916_, v___x_2917_, v_q_2918_, v_p_2919_, v_00_u03c4_u2081_u2082_2920_, v_f_2921_, v_h_2922_);
lean_dec(v_00_u03c4_u2081_u2082_2920_);
lean_dec(v_i_2916_);
lean_dec_ref(v_N_2915_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8(lean_object* v_N_2924_, lean_object* v_i_2925_, lean_object* v___x_2926_, lean_object* v_q_2927_, lean_object* v_N_2928_, lean_object* v_nN_2929_, lean_object* v_00_u03c6_2930_, lean_object* v_HN_2931_){
_start:
{
lean_object* v___f_2932_; 
v___f_2932_ = lean_alloc_closure((void*)(lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2932_, 0, v_00_u03c6_2930_);
return v___f_2932_;
}
}
LEAN_EXPORT lean_object* lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8___boxed(lean_object* v_N_2933_, lean_object* v_i_2934_, lean_object* v___x_2935_, lean_object* v_q_2936_, lean_object* v_N_2937_, lean_object* v_nN_2938_, lean_object* v_00_u03c6_2939_, lean_object* v_HN_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = lp_tree_QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8(v_N_2933_, v_i_2934_, v___x_2935_, v_q_2936_, v_N_2937_, v_nN_2938_, v_00_u03c6_2939_, v_HN_2940_);
lean_dec(v_i_2934_);
lean_dec_ref(v_N_2933_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5(lean_object* v_N_2942_, lean_object* v_i_2943_, lean_object* v___x_2944_, lean_object* v_00_u03b9_2945_, lean_object* v_s_2946_, lean_object* v_f_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = lp_tree_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5___redArg(v_N_2942_, v_i_2943_, v___x_2944_, v_s_2946_, v_f_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11(lean_object* v_N_2949_, lean_object* v_i_2950_, lean_object* v___x_2951_, lean_object* v_q_2952_, lean_object* v_c_2953_, lean_object* v_f_2954_, lean_object* v_H_2955_){
_start:
{
lean_object* v___f_2956_; 
v___f_2956_ = lean_alloc_closure((void*)(lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2956_, 0, v_f_2954_);
return v___f_2956_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11___boxed(lean_object* v_N_2957_, lean_object* v_i_2958_, lean_object* v___x_2959_, lean_object* v_q_2960_, lean_object* v_c_2961_, lean_object* v_f_2962_, lean_object* v_H_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = lp_tree_AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11(v_N_2957_, v_i_2958_, v___x_2959_, v_q_2960_, v_c_2961_, v_f_2962_, v_H_2963_);
lean_dec(v_i_2958_);
lean_dec_ref(v_N_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_liftOn_x27___at___00AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13_spec__16___redArg(lean_object* v_q_2965_, lean_object* v_f_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_apply_1(v_f_2966_, v_q_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_liftOn_x27___at___00AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13_spec__16(lean_object* v_c_2968_, lean_object* v_00_u03c6_2969_, lean_object* v_q_2970_, lean_object* v_f_2971_, lean_object* v_h_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_apply_1(v_f_2971_, v_q_2970_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13___redArg(lean_object* v_c_2974_, lean_object* v_q_2975_, lean_object* v_f_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_apply_1(v_f_2976_, v_q_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13(lean_object* v_N_2978_, lean_object* v_i_2979_, lean_object* v_00_u03b2_2980_, lean_object* v_c_2981_, lean_object* v_q_2982_, lean_object* v_f_2983_, lean_object* v_h_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_apply_1(v_f_2983_, v_q_2982_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13___boxed(lean_object* v_N_2986_, lean_object* v_i_2987_, lean_object* v_00_u03b2_2988_, lean_object* v_c_2989_, lean_object* v_q_2990_, lean_object* v_f_2991_, lean_object* v_h_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = lp_tree_AddCon_liftOn___at___00AddCon_lift___at___00QuotientAddGroup_lift___at___00Submodule_liftQ___at___00Submodule_mapQ___at___00Formalism_MainNotions_N_matQ_spec__2_spec__4_spec__8_spec__11_spec__13(v_N_2986_, v_i_2987_, v_00_u03b2_2988_, v_c_2989_, v_q_2990_, v_f_2991_, v_h_2992_);
lean_dec(v_i_2987_);
lean_dec_ref(v_N_2986_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__13(lean_object* v_N_2994_, lean_object* v_i_2995_, lean_object* v___x_2996_, lean_object* v_S_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__13___redArg(v_N_2994_, v_i_2995_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___redArg(lean_object* v_s_2999_){
_start:
{
lean_inc(v_s_2999_);
return v_s_2999_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___redArg___boxed(lean_object* v_s_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___redArg(v_s_3000_);
lean_dec(v_s_3000_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19(lean_object* v_N_3002_, lean_object* v_i_3003_, lean_object* v___x_3004_, lean_object* v_S_3005_, lean_object* v_r_3006_, lean_object* v_s_3007_){
_start:
{
lean_inc(v_s_3007_);
return v_s_3007_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19___boxed(lean_object* v_N_3008_, lean_object* v_i_3009_, lean_object* v___x_3010_, lean_object* v_S_3011_, lean_object* v_r_3012_, lean_object* v_s_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__19(v_N_3008_, v_i_3009_, v___x_3010_, v_S_3011_, v_r_3012_, v_s_3013_);
lean_dec(v_s_3013_);
lean_dec(v_r_3012_);
lean_dec(v_i_3009_);
lean_dec_ref(v_N_3008_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___redArg(lean_object* v_r_3015_){
_start:
{
lean_inc(v_r_3015_);
return v_r_3015_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___redArg___boxed(lean_object* v_r_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___redArg(v_r_3016_);
lean_dec(v_r_3016_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20(lean_object* v_N_3018_, lean_object* v_i_3019_, lean_object* v___x_3020_, lean_object* v_S_3021_, lean_object* v_r_3022_, lean_object* v_s_3023_){
_start:
{
lean_inc(v_r_3022_);
return v_r_3022_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20___boxed(lean_object* v_N_3024_, lean_object* v_i_3025_, lean_object* v___x_3026_, lean_object* v_S_3027_, lean_object* v_r_3028_, lean_object* v_s_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__20(v_N_3024_, v_i_3025_, v___x_3026_, v_S_3027_, v_r_3028_, v_s_3029_);
lean_dec(v_s_3029_);
lean_dec(v_r_3028_);
lean_dec(v_i_3025_);
lean_dec_ref(v_N_3024_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21___redArg(lean_object* v_r_3031_, lean_object* v_s_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_r_3031_);
lean_ctor_set(v___x_3033_, 1, v_s_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21(lean_object* v_N_3034_, lean_object* v_i_3035_, lean_object* v___x_3036_, lean_object* v_S_3037_, lean_object* v_r_3038_, lean_object* v_s_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v_r_3038_);
lean_ctor_set(v___x_3040_, 1, v_s_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21___boxed(lean_object* v_N_3041_, lean_object* v_i_3042_, lean_object* v___x_3043_, lean_object* v_S_3044_, lean_object* v_r_3045_, lean_object* v_s_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = lp_tree_OreLocalization_oreDiv___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00Matrix_mulVecBilin___at___00Formalism_MainNotions_N_matQ_spec__0_spec__0_spec__2_spec__5_spec__9_spec__12_spec__14_spec__17_spec__21(v_N_3041_, v_i_3042_, v___x_3043_, v_S_3044_, v_r_3045_, v_s_3046_);
lean_dec(v_i_3042_);
lean_dec_ref(v_N_3041_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0(lean_object* v_i_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_apply_1(v___y_3049_, v_i_3048_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg(lean_object* v_i_3051_){
_start:
{
lean_object* v___f_3052_; 
v___f_3052_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3052_, 0, v_i_3051_);
return v___f_3052_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0(lean_object* v_N_3053_, lean_object* v_i_3054_, lean_object* v_R_3055_, lean_object* v_H_3056_, lean_object* v_what_u2082_3057_, lean_object* v___x_3058_, lean_object* v___x_3059_, lean_object* v_i_3060_){
_start:
{
lean_object* v___f_3061_; 
v___f_3061_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3061_, 0, v_i_3060_);
return v___f_3061_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___boxed(lean_object* v_N_3062_, lean_object* v_i_3063_, lean_object* v_R_3064_, lean_object* v_H_3065_, lean_object* v_what_u2082_3066_, lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v_i_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0(v_N_3062_, v_i_3063_, v_R_3064_, v_H_3065_, v_what_u2082_3066_, v___x_3067_, v___x_3068_, v_i_3069_);
lean_dec_ref(v_what_u2082_3066_);
lean_dec_ref(v_H_3065_);
lean_dec_ref(v_R_3064_);
lean_dec(v_i_3063_);
lean_dec_ref(v_N_3062_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__3(lean_object* v_N_3071_, lean_object* v_i_3072_, lean_object* v_R_3073_, lean_object* v_H_3074_, lean_object* v_what_u2082_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v_00_u03b9_3078_, lean_object* v_s_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__3___boxed(lean_object* v_N_3081_, lean_object* v_i_3082_, lean_object* v_R_3083_, lean_object* v_H_3084_, lean_object* v_what_u2082_3085_, lean_object* v___x_3086_, lean_object* v___x_3087_, lean_object* v_00_u03b9_3088_, lean_object* v_s_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__3(v_N_3081_, v_i_3082_, v_R_3083_, v_H_3084_, v_what_u2082_3085_, v___x_3086_, v___x_3087_, v_00_u03b9_3088_, v_s_3089_);
lean_dec_ref(v_s_3089_);
lean_dec_ref(v_what_u2082_3085_);
lean_dec_ref(v_H_3084_);
lean_dec_ref(v_R_3083_);
lean_dec(v_i_3082_);
lean_dec_ref(v_N_3081_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__4(lean_object* v_N_3091_, lean_object* v_i_3092_, lean_object* v_R_3093_, lean_object* v_H_3094_, lean_object* v_what_u2082_3095_, lean_object* v___x_3096_, lean_object* v___x_3097_, lean_object* v_00_u03b9_3098_, lean_object* v_s_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_box(0);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__4___boxed(lean_object* v_N_3101_, lean_object* v_i_3102_, lean_object* v_R_3103_, lean_object* v_H_3104_, lean_object* v_what_u2082_3105_, lean_object* v___x_3106_, lean_object* v___x_3107_, lean_object* v_00_u03b9_3108_, lean_object* v_s_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = lp_tree_iInf___at___00Formalism_MainNotions_N_homRho_spec__4(v_N_3101_, v_i_3102_, v_R_3103_, v_H_3104_, v_what_u2082_3105_, v___x_3106_, v___x_3107_, v_00_u03b9_3108_, v_s_3109_);
lean_dec_ref(v_s_3109_);
lean_dec_ref(v_what_u2082_3105_);
lean_dec_ref(v_H_3104_);
lean_dec_ref(v_R_3103_);
lean_dec(v_i_3102_);
lean_dec_ref(v_N_3101_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__0(lean_object* v_S_3111_, lean_object* v_00_u03b8_3112_, lean_object* v_R_3113_, lean_object* v_N_3114_, lean_object* v_i_3115_, lean_object* v_j_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_00_u03c8_u03c1_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___f_3122_; lean_object* v___x_3123_; 
v_00_u03c8_u03c1_3118_ = lean_ctor_get(v_S_3111_, 11);
lean_inc(v_00_u03c8_u03c1_3118_);
lean_dec_ref(v_S_3111_);
lean_inc(v_j_3116_);
v___x_3119_ = lean_apply_1(v_00_u03b8_3112_, v_j_3116_);
v___x_3120_ = lean_apply_1(v_00_u03c8_u03c1_3118_, v___x_3119_);
v___x_3121_ = lp_tree_Formalism_MainNotions_N_matQ___redArg(v_R_3113_, v_N_3114_, v_i_3115_, v___x_3120_);
v___f_3122_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3122_, 0, v_j_3116_);
v___x_3123_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___f_3122_, v___x_3121_, v___y_3117_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__0___boxed(lean_object* v_S_3124_, lean_object* v_00_u03b8_3125_, lean_object* v_R_3126_, lean_object* v_N_3127_, lean_object* v_i_3128_, lean_object* v_j_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__0(v_S_3124_, v_00_u03b8_3125_, v_R_3126_, v_N_3127_, v_i_3128_, v_j_3129_, v___y_3130_);
lean_dec_ref(v_R_3126_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2_spec__3(lean_object* v_N_3132_, lean_object* v_i_3133_, lean_object* v_R_3134_, lean_object* v_H_3135_, lean_object* v_what_u2082_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_00_u03c3_u2081_u2082_3139_, lean_object* v_f_3140_, lean_object* v_p_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_box(0);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2_spec__3___boxed(lean_object* v_N_3143_, lean_object* v_i_3144_, lean_object* v_R_3145_, lean_object* v_H_3146_, lean_object* v_what_u2082_3147_, lean_object* v___x_3148_, lean_object* v___x_3149_, lean_object* v_00_u03c3_u2081_u2082_3150_, lean_object* v_f_3151_, lean_object* v_p_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2_spec__3(v_N_3143_, v_i_3144_, v_R_3145_, v_H_3146_, v_what_u2082_3147_, v___x_3148_, v___x_3149_, v_00_u03c3_u2081_u2082_3150_, v_f_3151_, v_p_3152_);
lean_dec(v_f_3151_);
lean_dec(v_00_u03c3_u2081_u2082_3150_);
lean_dec_ref(v_what_u2082_3147_);
lean_dec_ref(v_H_3146_);
lean_dec_ref(v_R_3145_);
lean_dec(v_i_3144_);
lean_dec_ref(v_N_3143_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2(lean_object* v_N_3154_, lean_object* v_i_3155_, lean_object* v_R_3156_, lean_object* v_H_3157_, lean_object* v_what_u2082_3158_, lean_object* v___x_3159_, lean_object* v___x_3160_, lean_object* v_00_u03c4_u2081_u2082_3161_, lean_object* v_f_3162_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_box(0);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2___boxed(lean_object* v_N_3164_, lean_object* v_i_3165_, lean_object* v_R_3166_, lean_object* v_H_3167_, lean_object* v_what_u2082_3168_, lean_object* v___x_3169_, lean_object* v___x_3170_, lean_object* v_00_u03c4_u2081_u2082_3171_, lean_object* v_f_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homRho_spec__2(v_N_3164_, v_i_3165_, v_R_3166_, v_H_3167_, v_what_u2082_3168_, v___x_3169_, v___x_3170_, v_00_u03c4_u2081_u2082_3171_, v_f_3172_);
lean_dec(v_f_3172_);
lean_dec(v_00_u03c4_u2081_u2082_3171_);
lean_dec_ref(v_what_u2082_3168_);
lean_dec_ref(v_H_3167_);
lean_dec_ref(v_R_3166_);
lean_dec(v_i_3165_);
lean_dec_ref(v_N_3164_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__4(lean_object* v___f_3174_, lean_object* v_x_3175_){
_start:
{
lean_inc(v___f_3174_);
return v___f_3174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__4___boxed(lean_object* v___f_3176_, lean_object* v_x_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__4(v___f_3176_, v_x_3177_);
lean_dec(v_x_3177_);
lean_dec(v___f_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__3(lean_object* v___f_3179_, lean_object* v_x_3180_){
_start:
{
lean_object* v___x_3181_; lean_object* v_toAddMonoid_3182_; lean_object* v___x_3183_; lean_object* v_toZero_3184_; 
v___x_3181_ = lean_apply_1(v___f_3179_, v_x_3180_);
v_toAddMonoid_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_ref(v_toAddMonoid_3182_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_3182_);
lean_dec_ref(v_toAddMonoid_3182_);
v_toZero_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_toZero_3184_);
lean_dec_ref(v___x_3183_);
return v_toZero_3184_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__1(lean_object* v___f_3185_, lean_object* v_x1_3186_, lean_object* v___y_3187_, lean_object* v_x2_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3190_; lean_object* v_toAddMonoid_3191_; lean_object* v_toAddSemigroup_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_inc_n(v___y_3189_, 2);
v___x_3190_ = lean_apply_1(v___f_3185_, v___y_3189_);
v_toAddMonoid_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc_ref(v_toAddMonoid_3191_);
lean_dec_ref(v___x_3190_);
v_toAddSemigroup_3192_ = lean_ctor_get(v_toAddMonoid_3191_, 0);
lean_inc(v_toAddSemigroup_3192_);
lean_dec_ref(v_toAddMonoid_3191_);
lean_inc(v___y_3187_);
v___x_3193_ = lean_apply_2(v_x1_3186_, v___y_3187_, v___y_3189_);
v___x_3194_ = lean_apply_2(v_x2_3188_, v___y_3187_, v___y_3189_);
v___x_3195_ = lean_apply_2(v_toAddSemigroup_3192_, v___x_3193_, v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__2(lean_object* v___f_3196_, lean_object* v_x1_3197_, lean_object* v_x2_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___f_3200_; 
v___f_3200_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3200_, 0, v___f_3196_);
lean_closure_set(v___f_3200_, 1, v_x1_3197_);
lean_closure_set(v___f_3200_, 2, v___y_3199_);
lean_closure_set(v___f_3200_, 3, v_x2_3198_);
return v___f_3200_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__0(lean_object* v___x_3201_, lean_object* v___x_3202_, lean_object* v___x_3203_, lean_object* v_i_3204_){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_box(0);
v___x_3206_ = lp_mathlib_OreLocalization_oreSetComm(lean_box(0), v___x_3201_, v___x_3205_);
v___x_3207_ = lp_mathlib_OreLocalization_instAddGroupOreLocalization___redArg(v___x_3201_, v___x_3205_, v___x_3206_, v___x_3202_, v___x_3203_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___x_3208_, lean_object* v___x_3209_, lean_object* v___x_3210_, lean_object* v_i_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__0(v___x_3208_, v___x_3209_, v___x_3210_, v_i_3211_);
lean_dec(v_i_3211_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg(lean_object* v_N_3213_, lean_object* v_i_3214_, lean_object* v_s_3215_){
_start:
{
lean_object* v_instO_3216_; lean_object* v___x_3217_; lean_object* v_toSemiring_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___f_3225_; lean_object* v___x_3226_; 
v_instO_3216_ = lean_ctor_get(v_N_3213_, 9);
lean_inc_ref(v_instO_3216_);
lean_dec_ref(v_N_3213_);
v___x_3217_ = lean_apply_1(v_instO_3216_, v_i_3214_);
v_toSemiring_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_ref(v_toSemiring_3218_);
v___x_3219_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_3217_);
v___x_3220_ = lp_mathlib_Ring_toAddCommGroup___redArg(v___x_3217_);
lean_dec_ref(v___x_3217_);
v___x_3221_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_3218_);
lean_dec_ref(v_toSemiring_3218_);
v___f_3222_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3222_, 0, v___x_3219_);
lean_closure_set(v___f_3222_, 1, v___x_3220_);
lean_closure_set(v___f_3222_, 2, v___x_3221_);
lean_inc_ref(v___f_3222_);
v___f_3223_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__2), 4, 1);
lean_closure_set(v___f_3223_, 0, v___f_3222_);
v___f_3224_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3224_, 0, v___f_3222_);
v___f_3225_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_3225_, 0, v___f_3224_);
v___x_3226_ = l_List_foldrTR___redArg(v___f_3223_, v___f_3225_, v_s_3215_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___redArg(lean_object* v_N_3227_, lean_object* v_i_3228_, lean_object* v_R_3229_, lean_object* v_H_3230_, lean_object* v_what_u2082_3231_, lean_object* v___x_3232_, lean_object* v___x_3233_, lean_object* v_s_3234_, lean_object* v_f_3235_){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lp_mathlib_Multiset_map___redArg(v_f_3235_, v_s_3234_);
v___x_3237_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg(v_N_3227_, v_i_3228_, v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___redArg___boxed(lean_object* v_N_3238_, lean_object* v_i_3239_, lean_object* v_R_3240_, lean_object* v_H_3241_, lean_object* v_what_u2082_3242_, lean_object* v___x_3243_, lean_object* v___x_3244_, lean_object* v_s_3245_, lean_object* v_f_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___redArg(v_N_3238_, v_i_3239_, v_R_3240_, v_H_3241_, v_what_u2082_3242_, v___x_3243_, v___x_3244_, v_s_3245_, v_f_3246_);
lean_dec_ref(v_what_u2082_3242_);
lean_dec_ref(v_H_3241_);
lean_dec_ref(v_R_3240_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__1(lean_object* v_g_3248_, lean_object* v_N_3249_, lean_object* v_i_3250_, lean_object* v_R_3251_, lean_object* v_H_3252_, lean_object* v_what_u2082_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v___f_3256_, lean_object* v_h_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_box(0);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__1___boxed(lean_object* v_g_3259_, lean_object* v_N_3260_, lean_object* v_i_3261_, lean_object* v_R_3262_, lean_object* v_H_3263_, lean_object* v_what_u2082_3264_, lean_object* v___x_3265_, lean_object* v___x_3266_, lean_object* v___f_3267_, lean_object* v_h_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__1(v_g_3259_, v_N_3260_, v_i_3261_, v_R_3262_, v_H_3263_, v_what_u2082_3264_, v___x_3265_, v___x_3266_, v___f_3267_, v_h_3268_);
lean_dec(v___f_3267_);
lean_dec_ref(v_what_u2082_3264_);
lean_dec_ref(v_H_3263_);
lean_dec_ref(v_R_3262_);
lean_dec(v_i_3261_);
lean_dec_ref(v_N_3260_);
lean_dec(v_g_3259_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__2(lean_object* v_S_3270_, lean_object* v_R_3271_, lean_object* v_N_3272_, lean_object* v_i_3273_, lean_object* v_g_3274_, lean_object* v_H_3275_, lean_object* v_what_u2082_3276_, lean_object* v___x_3277_, lean_object* v___x_3278_, lean_object* v_00_u03b8_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__2___boxed(lean_object* v_S_3281_, lean_object* v_R_3282_, lean_object* v_N_3283_, lean_object* v_i_3284_, lean_object* v_g_3285_, lean_object* v_H_3286_, lean_object* v_what_u2082_3287_, lean_object* v___x_3288_, lean_object* v___x_3289_, lean_object* v_00_u03b8_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = lp_tree_Formalism_MainNotions_N_homRho___redArg___lam__2(v_S_3281_, v_R_3282_, v_N_3283_, v_i_3284_, v_g_3285_, v_H_3286_, v_what_u2082_3287_, v___x_3288_, v___x_3289_, v_00_u03b8_3290_);
lean_dec(v_00_u03b8_3290_);
lean_dec_ref(v_what_u2082_3287_);
lean_dec_ref(v_H_3286_);
lean_dec(v_g_3285_);
lean_dec(v_i_3284_);
lean_dec_ref(v_N_3283_);
lean_dec_ref(v_R_3282_);
lean_dec_ref(v_S_3281_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg(lean_object* v_R_3292_, lean_object* v_H_3293_, lean_object* v_what_u2082_3294_, lean_object* v_N_3295_, lean_object* v_i_3296_, lean_object* v_S_3297_, lean_object* v_g_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___redArg___boxed(lean_object* v_R_3300_, lean_object* v_H_3301_, lean_object* v_what_u2082_3302_, lean_object* v_N_3303_, lean_object* v_i_3304_, lean_object* v_S_3305_, lean_object* v_g_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = lp_tree_Formalism_MainNotions_N_homRho___redArg(v_R_3300_, v_H_3301_, v_what_u2082_3302_, v_N_3303_, v_i_3304_, v_S_3305_, v_g_3306_);
lean_dec(v_g_3306_);
lean_dec_ref(v_S_3305_);
lean_dec(v_i_3304_);
lean_dec_ref(v_N_3303_);
lean_dec_ref(v_what_u2082_3302_);
lean_dec_ref(v_H_3301_);
lean_dec_ref(v_R_3300_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho(lean_object* v_R_3308_, lean_object* v_H_3309_, lean_object* v_what_u2082_3310_, lean_object* v_N_3311_, lean_object* v_i_3312_, lean_object* v_S_3313_, lean_object* v_g_3314_, lean_object* v_Rel_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_box(0);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homRho___boxed(lean_object* v_R_3317_, lean_object* v_H_3318_, lean_object* v_what_u2082_3319_, lean_object* v_N_3320_, lean_object* v_i_3321_, lean_object* v_S_3322_, lean_object* v_g_3323_, lean_object* v_Rel_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = lp_tree_Formalism_MainNotions_N_homRho(v_R_3317_, v_H_3318_, v_what_u2082_3319_, v_N_3320_, v_i_3321_, v_S_3322_, v_g_3323_, v_Rel_3324_);
lean_dec(v_g_3323_);
lean_dec_ref(v_S_3322_);
lean_dec(v_i_3321_);
lean_dec_ref(v_N_3320_);
lean_dec_ref(v_what_u2082_3319_);
lean_dec_ref(v_H_3318_);
lean_dec_ref(v_R_3317_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1(lean_object* v_N_3326_, lean_object* v_i_3327_, lean_object* v_R_3328_, lean_object* v_H_3329_, lean_object* v_what_u2082_3330_, lean_object* v___x_3331_, lean_object* v___x_3332_, lean_object* v_00_u03b9_3333_, lean_object* v_s_3334_, lean_object* v_f_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___redArg(v_N_3326_, v_i_3327_, v_R_3328_, v_H_3329_, v_what_u2082_3330_, v___x_3331_, v___x_3332_, v_s_3334_, v_f_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1___boxed(lean_object* v_N_3337_, lean_object* v_i_3338_, lean_object* v_R_3339_, lean_object* v_H_3340_, lean_object* v_what_u2082_3341_, lean_object* v___x_3342_, lean_object* v___x_3343_, lean_object* v_00_u03b9_3344_, lean_object* v_s_3345_, lean_object* v_f_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1(v_N_3337_, v_i_3338_, v_R_3339_, v_H_3340_, v_what_u2082_3341_, v___x_3342_, v___x_3343_, v_00_u03b9_3344_, v_s_3345_, v_f_3346_);
lean_dec_ref(v_what_u2082_3341_);
lean_dec_ref(v_H_3340_);
lean_dec_ref(v_R_3339_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1_spec__4___redArg(lean_object* v_f_3348_, lean_object* v_q_u2081_3349_, lean_object* v_q_u2082_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = lean_apply_2(v_f_3348_, v_q_u2081_3349_, v_q_u2082_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1_spec__4(lean_object* v_f_3352_, lean_object* v_h_3353_, lean_object* v_q_u2081_3354_, lean_object* v_q_u2082_3355_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_apply_2(v_f_3352_, v_q_u2081_3354_, v_q_u2082_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1(lean_object* v_N_3357_, lean_object* v_i_3358_, lean_object* v_R_3359_, lean_object* v_H_3360_, lean_object* v_what_u2082_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_s_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___redArg(v_N_3357_, v_i_3358_, v_s_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1___boxed(lean_object* v_N_3366_, lean_object* v_i_3367_, lean_object* v_R_3368_, lean_object* v_H_3369_, lean_object* v_what_u2082_3370_, lean_object* v___x_3371_, lean_object* v___x_3372_, lean_object* v_s_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homRho_spec__1_spec__1(v_N_3366_, v_i_3367_, v_R_3368_, v_H_3369_, v_what_u2082_3370_, v___x_3371_, v___x_3372_, v_s_3373_);
lean_dec_ref(v_what_u2082_3370_);
lean_dec_ref(v_H_3369_);
lean_dec_ref(v_R_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2___redArg(lean_object* v_i_3375_){
_start:
{
lean_object* v___f_3376_; 
v___f_3376_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3376_, 0, v_i_3375_);
return v___f_3376_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2(lean_object* v_N_3377_, lean_object* v_i_3378_, lean_object* v___x_3379_, lean_object* v___x_3380_, lean_object* v_i_3381_){
_start:
{
lean_object* v___f_3382_; 
v___f_3382_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homRho_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3382_, 0, v_i_3381_);
return v___f_3382_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2___boxed(lean_object* v_N_3383_, lean_object* v_i_3384_, lean_object* v___x_3385_, lean_object* v___x_3386_, lean_object* v_i_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = lp_tree_LinearMap_proj___at___00Formalism_MainNotions_N_homChi_spec__2(v_N_3383_, v_i_3384_, v___x_3385_, v___x_3386_, v_i_3387_);
lean_dec(v_i_3384_);
lean_dec_ref(v_N_3383_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__5(lean_object* v_N_3389_, lean_object* v_i_3390_, lean_object* v___x_3391_, lean_object* v___x_3392_, lean_object* v_00_u03b9_3393_, lean_object* v_s_3394_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_box(0);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__5___boxed(lean_object* v_N_3396_, lean_object* v_i_3397_, lean_object* v___x_3398_, lean_object* v___x_3399_, lean_object* v_00_u03b9_3400_, lean_object* v_s_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__5(v_N_3396_, v_i_3397_, v___x_3398_, v___x_3399_, v_00_u03b9_3400_, v_s_3401_);
lean_dec_ref(v_s_3401_);
lean_dec(v_i_3397_);
lean_dec_ref(v_N_3396_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__6(lean_object* v_N_3403_, lean_object* v_i_3404_, lean_object* v___x_3405_, lean_object* v___x_3406_, lean_object* v_00_u03b9_3407_, lean_object* v_s_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_box(0);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__6___boxed(lean_object* v_N_3410_, lean_object* v_i_3411_, lean_object* v___x_3412_, lean_object* v___x_3413_, lean_object* v_00_u03b9_3414_, lean_object* v_s_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = lp_tree_iInf___at___00Formalism_MainNotions_N_homChi_spec__6(v_N_3410_, v_i_3411_, v___x_3412_, v___x_3413_, v_00_u03b9_3414_, v_s_3415_);
lean_dec_ref(v_s_3415_);
lean_dec(v_i_3411_);
lean_dec_ref(v_N_3410_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3___redArg(lean_object* v_P_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3421_; 
v_fst_3419_ = lean_ctor_get(v_a_3418_, 0);
lean_inc(v_fst_3419_);
v_snd_3420_ = lean_ctor_get(v_a_3418_, 1);
lean_inc(v_snd_3420_);
lean_dec(v_a_3418_);
v___x_3421_ = lean_apply_2(v_P_3417_, v_fst_3419_, v_snd_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1___lam__0(lean_object* v_toSemiring_3422_, lean_object* v_c_3423_, lean_object* v_toOne_3424_, lean_object* v_toMul_3425_, lean_object* v_m_3426_, lean_object* v_s_3427_){
_start:
{
lean_object* v___x_3428_; lean_object* v_toMul_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3438_; 
v___x_3428_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_3422_);
v_toMul_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v___x_3428_, 1);
lean_dec(v_unused_3439_);
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_toMul_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3433_ = lean_apply_2(v_toMul_3429_, v_c_3423_, v_toOne_3424_);
v___x_3434_ = lean_apply_2(v_toMul_3425_, v___x_3433_, v_m_3426_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v_s_3427_);
lean_ctor_set(v___x_3431_, 0, v___x_3434_);
v___x_3436_ = v___x_3431_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_s_3427_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1(lean_object* v_N_3440_, lean_object* v_i_3441_, lean_object* v___x_3442_, lean_object* v_S_3443_, lean_object* v_c_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v_instO_3446_; lean_object* v___x_3447_; lean_object* v_toSemiring_3448_; lean_object* v_toMonoid_3449_; lean_object* v___x_3450_; lean_object* v_toOne_3451_; lean_object* v_toMul_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; 
v_instO_3446_ = lean_ctor_get(v_N_3440_, 9);
lean_inc_ref(v_instO_3446_);
lean_dec_ref(v_N_3440_);
v___x_3447_ = lean_apply_1(v_instO_3446_, v_i_3441_);
v_toSemiring_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc_ref(v_toSemiring_3448_);
lean_dec_ref(v___x_3447_);
v_toMonoid_3449_ = lean_ctor_get(v_toSemiring_3448_, 1);
v___x_3450_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_3449_);
v_toOne_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_toOne_3451_);
v_toMul_3452_ = lean_ctor_get(v___x_3450_, 1);
lean_inc(v_toMul_3452_);
lean_dec_ref(v___x_3450_);
v___f_3453_ = lean_alloc_closure((void*)(lp_tree_OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1___lam__0), 6, 4);
lean_closure_set(v___f_3453_, 0, v_toSemiring_3448_);
lean_closure_set(v___f_3453_, 1, v_c_3444_);
lean_closure_set(v___f_3453_, 2, v_toOne_3451_);
lean_closure_set(v___f_3453_, 3, v_toMul_3452_);
v___x_3454_ = lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3___redArg(v___f_3453_, v_a_3445_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__0(lean_object* v_S_3455_, lean_object* v_00_u03b8_3456_, lean_object* v_c_3457_, lean_object* v_N_3458_, lean_object* v_i_3459_, lean_object* v___x_3460_, lean_object* v_j_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_00_u03c8_u03c7_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_00_u03c8_u03c7_3463_ = lean_ctor_get(v_S_3455_, 12);
lean_inc(v_00_u03c8_u03c7_3463_);
lean_dec_ref(v_S_3455_);
lean_inc(v_j_3461_);
v___x_3464_ = lean_apply_1(v_00_u03b8_3456_, v_j_3461_);
v___x_3465_ = lean_apply_2(v_00_u03c8_u03c7_3463_, v_c_3457_, v___x_3464_);
v___x_3466_ = lean_apply_1(v___y_3462_, v_j_3461_);
v___x_3467_ = lp_tree_OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1(v_N_3458_, v_i_3459_, v___x_3460_, v___x_3460_, v___x_3465_, v___x_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4_spec__8(lean_object* v_N_3468_, lean_object* v_i_3469_, lean_object* v___x_3470_, lean_object* v___x_3471_, lean_object* v_00_u03c3_u2081_u2082_3472_, lean_object* v_f_3473_, lean_object* v_p_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_box(0);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4_spec__8___boxed(lean_object* v_N_3476_, lean_object* v_i_3477_, lean_object* v___x_3478_, lean_object* v___x_3479_, lean_object* v_00_u03c3_u2081_u2082_3480_, lean_object* v_f_3481_, lean_object* v_p_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = lp_tree_Submodule_comap___at___00LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4_spec__8(v_N_3476_, v_i_3477_, v___x_3478_, v___x_3479_, v_00_u03c3_u2081_u2082_3480_, v_f_3481_, v_p_3482_);
lean_dec(v_f_3481_);
lean_dec(v_00_u03c3_u2081_u2082_3480_);
lean_dec(v_i_3477_);
lean_dec_ref(v_N_3476_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4(lean_object* v_N_3484_, lean_object* v_i_3485_, lean_object* v___x_3486_, lean_object* v___x_3487_, lean_object* v_00_u03c4_u2081_u2082_3488_, lean_object* v_f_3489_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_box(0);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4___boxed(lean_object* v_N_3491_, lean_object* v_i_3492_, lean_object* v___x_3493_, lean_object* v___x_3494_, lean_object* v_00_u03c4_u2081_u2082_3495_, lean_object* v_f_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = lp_tree_LinearMap_ker___at___00Formalism_MainNotions_N_homChi_spec__4(v_N_3491_, v_i_3492_, v___x_3493_, v___x_3494_, v_00_u03c4_u2081_u2082_3495_, v_f_3496_);
lean_dec(v_f_3496_);
lean_dec(v_00_u03c4_u2081_u2082_3495_);
lean_dec(v_i_3492_);
lean_dec_ref(v_N_3491_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__11___redArg(lean_object* v_N_3498_, lean_object* v_i_3499_){
_start:
{
lean_object* v_instO_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v_toAddMonoid_3504_; lean_object* v___x_3505_; lean_object* v_toZero_3506_; lean_object* v___x_3507_; lean_object* v_toOne_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_instO_3500_ = lean_ctor_get(v_N_3498_, 9);
lean_inc_ref(v_instO_3500_);
lean_dec_ref(v_N_3498_);
v___x_3501_ = lean_apply_1(v_instO_3500_, v_i_3499_);
v___x_3502_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_3501_);
v___x_3503_ = lp_mathlib_Ring_toAddCommGroup___redArg(v___x_3501_);
lean_dec_ref(v___x_3501_);
v_toAddMonoid_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc_ref(v_toAddMonoid_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddMonoid_3504_);
lean_dec_ref(v_toAddMonoid_3504_);
v_toZero_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_toZero_3506_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_3502_);
lean_dec_ref(v___x_3502_);
v_toOne_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v___x_3507_, 1);
lean_dec(v_unused_3516_);
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_toOne_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v_toOne_3508_);
lean_ctor_set(v___x_3510_, 0, v_toZero_3506_);
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_toZero_3506_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_toOne_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__1(lean_object* v_N_3517_, lean_object* v_i_3518_, lean_object* v_x_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__11___redArg(v_N_3517_, v_i_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__1___boxed(lean_object* v_N_3521_, lean_object* v_i_3522_, lean_object* v_x_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__1(v_N_3521_, v_i_3522_, v_x_3523_);
lean_dec(v_x_3523_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14___redArg(lean_object* v_N_3525_, lean_object* v_i_3526_, lean_object* v_r_u2081_3527_, lean_object* v_s_u2081_3528_, lean_object* v_r_u2082_3529_, lean_object* v_s_u2082_3530_){
_start:
{
lean_object* v_instO_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v_toAddMonoid_3535_; lean_object* v_toSemiring_3536_; lean_object* v_toAddSemigroup_3537_; lean_object* v___x_3538_; lean_object* v_toMonoid_3539_; lean_object* v___x_3540_; lean_object* v_toMul_3541_; lean_object* v_toMul_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3553_; 
v_instO_3531_ = lean_ctor_get(v_N_3525_, 9);
lean_inc_ref(v_instO_3531_);
lean_dec_ref(v_N_3525_);
v___x_3532_ = lean_apply_1(v_instO_3531_, v_i_3526_);
v___x_3533_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_3532_);
v___x_3534_ = lp_mathlib_Ring_toAddCommGroup___redArg(v___x_3532_);
v_toAddMonoid_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_ref(v_toAddMonoid_3535_);
lean_dec_ref(v___x_3534_);
v_toSemiring_3536_ = lean_ctor_get(v___x_3532_, 0);
lean_inc_ref(v_toSemiring_3536_);
lean_dec_ref(v___x_3532_);
v_toAddSemigroup_3537_ = lean_ctor_get(v_toAddMonoid_3535_, 0);
lean_inc(v_toAddSemigroup_3537_);
lean_dec_ref(v_toAddMonoid_3535_);
v___x_3538_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_3533_);
lean_dec_ref(v___x_3533_);
v_toMonoid_3539_ = lean_ctor_get(v_toSemiring_3536_, 1);
lean_inc_ref(v_toMonoid_3539_);
lean_dec_ref(v_toSemiring_3536_);
v___x_3540_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_3539_);
lean_dec_ref(v_toMonoid_3539_);
v_toMul_3541_ = lean_ctor_get(v___x_3540_, 1);
lean_inc(v_toMul_3541_);
lean_dec_ref(v___x_3540_);
v_toMul_3542_ = lean_ctor_get(v___x_3538_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v___x_3538_, 0);
lean_dec(v_unused_3554_);
v___x_3544_ = v___x_3538_;
v_isShared_3545_ = v_isSharedCheck_3553_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_toMul_3542_);
lean_dec(v___x_3538_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3553_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_inc(v_toMul_3541_);
lean_inc(v_s_u2082_3530_);
v___x_3546_ = lean_apply_2(v_toMul_3541_, v_s_u2082_3530_, v_r_u2081_3527_);
lean_inc(v_s_u2081_3528_);
v___x_3547_ = lean_apply_2(v_toMul_3541_, v_s_u2081_3528_, v_r_u2082_3529_);
v___x_3548_ = lean_apply_2(v_toAddSemigroup_3537_, v___x_3546_, v___x_3547_);
v___x_3549_ = lean_apply_2(v_toMul_3542_, v_s_u2082_3530_, v_s_u2081_3528_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v___x_3549_);
lean_ctor_set(v___x_3544_, 0, v___x_3548_);
v___x_3551_ = v___x_3544_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12(lean_object* v_N_3555_, lean_object* v_i_3556_, lean_object* v___x_3557_, lean_object* v_S_3558_, lean_object* v_r_u2082_3559_, lean_object* v_s_u2082_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v___x_3564_; 
v_fst_3562_ = lean_ctor_get(v_a_3561_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_a_3561_, 1);
lean_inc(v_snd_3563_);
lean_dec(v_a_3561_);
v___x_3564_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14___redArg(v_N_3555_, v_i_3556_, v_fst_3562_, v_snd_3563_, v_r_u2082_3559_, v_s_u2082_3560_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9(lean_object* v_N_3565_, lean_object* v_i_3566_, lean_object* v___x_3567_, lean_object* v_S_3568_, lean_object* v_x_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_fst_3571_; lean_object* v_snd_3572_; lean_object* v___x_3573_; 
v_fst_3571_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_fst_3571_);
v_snd_3572_ = lean_ctor_get(v_a_3570_, 1);
lean_inc(v_snd_3572_);
lean_dec(v_a_3570_);
v___x_3573_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12(v_N_3565_, v_i_3566_, v___x_3567_, v_S_3568_, v_fst_3571_, v_snd_3572_, v_x_3569_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__0(lean_object* v_N_3574_, lean_object* v_i_3575_, lean_object* v___x_3576_, lean_object* v_x1_3577_, lean_object* v_x2_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_inc(v___y_3579_);
v___x_3580_ = lean_apply_1(v_x1_3577_, v___y_3579_);
v___x_3581_ = lean_apply_1(v_x2_3578_, v___y_3579_);
v___x_3582_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9(v_N_3574_, v_i_3575_, v___x_3576_, v___x_3576_, v___x_3580_, v___x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg(lean_object* v_N_3583_, lean_object* v_i_3584_, lean_object* v___x_3585_, lean_object* v_s_3586_){
_start:
{
lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___x_3589_; 
lean_inc(v_i_3584_);
lean_inc_ref(v_N_3583_);
v___f_3587_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__0), 6, 3);
lean_closure_set(v___f_3587_, 0, v_N_3583_);
lean_closure_set(v___f_3587_, 1, v_i_3584_);
lean_closure_set(v___f_3587_, 2, v___x_3585_);
v___f_3588_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3588_, 0, v_N_3583_);
lean_closure_set(v___f_3588_, 1, v_i_3584_);
v___x_3589_ = l_List_foldrTR___redArg(v___f_3587_, v___f_3588_, v_s_3586_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3___redArg(lean_object* v_N_3590_, lean_object* v_i_3591_, lean_object* v___x_3592_, lean_object* v___x_3593_, lean_object* v_s_3594_, lean_object* v_f_3595_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lp_mathlib_Multiset_map___redArg(v_f_3595_, v_s_3594_);
v___x_3597_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg(v_N_3590_, v_i_3591_, v___x_3592_, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__1(lean_object* v_g_3598_, lean_object* v_N_3599_, lean_object* v_i_3600_, lean_object* v___x_3601_, lean_object* v___x_3602_, lean_object* v___f_3603_, lean_object* v___f_3604_, lean_object* v_h_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_box(0);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__1___boxed(lean_object* v_g_3607_, lean_object* v_N_3608_, lean_object* v_i_3609_, lean_object* v___x_3610_, lean_object* v___x_3611_, lean_object* v___f_3612_, lean_object* v___f_3613_, lean_object* v_h_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__1(v_g_3607_, v_N_3608_, v_i_3609_, v___x_3610_, v___x_3611_, v___f_3612_, v___f_3613_, v_h_3614_);
lean_dec(v___f_3613_);
lean_dec(v___f_3612_);
lean_dec(v_i_3609_);
lean_dec_ref(v_N_3608_);
lean_dec(v_g_3607_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__2(lean_object* v_S_3616_, lean_object* v_c_3617_, lean_object* v_N_3618_, lean_object* v_i_3619_, lean_object* v___x_3620_, lean_object* v_g_3621_, lean_object* v___x_3622_, lean_object* v___f_3623_, lean_object* v_00_u03b8_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_box(0);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__2___boxed(lean_object* v_S_3626_, lean_object* v_c_3627_, lean_object* v_N_3628_, lean_object* v_i_3629_, lean_object* v___x_3630_, lean_object* v_g_3631_, lean_object* v___x_3632_, lean_object* v___f_3633_, lean_object* v_00_u03b8_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = lp_tree_Formalism_MainNotions_N_homChi___redArg___lam__2(v_S_3626_, v_c_3627_, v_N_3628_, v_i_3629_, v___x_3630_, v_g_3631_, v___x_3632_, v___f_3633_, v_00_u03b8_3634_);
lean_dec(v_00_u03b8_3634_);
lean_dec(v___f_3633_);
lean_dec(v_g_3631_);
lean_dec(v_i_3629_);
lean_dec_ref(v_N_3628_);
lean_dec(v_c_3627_);
lean_dec_ref(v_S_3626_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__1(lean_object* v_N_3636_, lean_object* v_i_3637_, lean_object* v___x_3638_, lean_object* v_p_3639_, lean_object* v_s_3640_, lean_object* v_hs_3641_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_box(0);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__1___boxed(lean_object* v_N_3643_, lean_object* v_i_3644_, lean_object* v___x_3645_, lean_object* v_p_3646_, lean_object* v_s_3647_, lean_object* v_hs_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__1(v_N_3643_, v_i_3644_, v___x_3645_, v_p_3646_, v_s_3647_, v_hs_3648_);
lean_dec(v_i_3644_);
lean_dec_ref(v_N_3643_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__0(lean_object* v_N_3650_, lean_object* v_i_3651_, lean_object* v___x_3652_, lean_object* v_00_u03c3_u2081_u2082_3653_, lean_object* v_inst_3654_, lean_object* v_f_3655_, lean_object* v_p_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_box(0);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__0___boxed(lean_object* v_N_3658_, lean_object* v_i_3659_, lean_object* v___x_3660_, lean_object* v_00_u03c3_u2081_u2082_3661_, lean_object* v_inst_3662_, lean_object* v_f_3663_, lean_object* v_p_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0_spec__0(v_N_3658_, v_i_3659_, v___x_3660_, v_00_u03c3_u2081_u2082_3661_, v_inst_3662_, v_f_3663_, v_p_3664_);
lean_dec(v_f_3663_);
lean_dec(v_00_u03c3_u2081_u2082_3661_);
lean_dec(v_i_3659_);
lean_dec_ref(v_N_3658_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___redArg(lean_object* v_N_3666_, lean_object* v_i_3667_, lean_object* v___x_3668_, lean_object* v_00_u03c4_u2081_u2082_3669_, lean_object* v_f_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_box(0);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___redArg___boxed(lean_object* v_N_3672_, lean_object* v_i_3673_, lean_object* v___x_3674_, lean_object* v_00_u03c4_u2081_u2082_3675_, lean_object* v_f_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___redArg(v_N_3672_, v_i_3673_, v___x_3674_, v_00_u03c4_u2081_u2082_3675_, v_f_3676_);
lean_dec(v_f_3676_);
lean_dec(v_00_u03c4_u2081_u2082_3675_);
lean_dec(v_i_3673_);
lean_dec_ref(v_N_3672_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg(lean_object* v_N_3678_, lean_object* v_i_3679_, lean_object* v_S_3680_, lean_object* v_g_3681_, lean_object* v_c_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_box(0);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___redArg___boxed(lean_object* v_N_3684_, lean_object* v_i_3685_, lean_object* v_S_3686_, lean_object* v_g_3687_, lean_object* v_c_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = lp_tree_Formalism_MainNotions_N_homChi___redArg(v_N_3684_, v_i_3685_, v_S_3686_, v_g_3687_, v_c_3688_);
lean_dec(v_c_3688_);
lean_dec(v_g_3687_);
lean_dec_ref(v_S_3686_);
lean_dec(v_i_3685_);
lean_dec_ref(v_N_3684_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi(lean_object* v_R_3690_, lean_object* v_H_3691_, lean_object* v_what_u2082_3692_, lean_object* v_N_3693_, lean_object* v_i_3694_, lean_object* v_S_3695_, lean_object* v_g_3696_, lean_object* v_Rel_3697_, lean_object* v_c_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_box(0);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_homChi___boxed(lean_object* v_R_3700_, lean_object* v_H_3701_, lean_object* v_what_u2082_3702_, lean_object* v_N_3703_, lean_object* v_i_3704_, lean_object* v_S_3705_, lean_object* v_g_3706_, lean_object* v_Rel_3707_, lean_object* v_c_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = lp_tree_Formalism_MainNotions_N_homChi(v_R_3700_, v_H_3701_, v_what_u2082_3702_, v_N_3703_, v_i_3704_, v_S_3705_, v_g_3706_, v_Rel_3707_, v_c_3708_);
lean_dec(v_c_3708_);
lean_dec(v_g_3706_);
lean_dec_ref(v_S_3705_);
lean_dec(v_i_3704_);
lean_dec_ref(v_N_3703_);
lean_dec_ref(v_what_u2082_3702_);
lean_dec_ref(v_H_3701_);
lean_dec_ref(v_R_3700_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0(lean_object* v_N_3710_, lean_object* v_i_3711_, lean_object* v___x_3712_, lean_object* v_00_u03c4_u2081_u2082_3713_, lean_object* v_inst_3714_, lean_object* v_f_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_box(0);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0___boxed(lean_object* v_N_3717_, lean_object* v_i_3718_, lean_object* v___x_3719_, lean_object* v_00_u03c4_u2081_u2082_3720_, lean_object* v_inst_3721_, lean_object* v_f_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = lp_tree_LinearMap_range___at___00Formalism_MainNotions_N_homChi_spec__0(v_N_3717_, v_i_3718_, v___x_3719_, v_00_u03c4_u2081_u2082_3720_, v_inst_3721_, v_f_3722_);
lean_dec(v_f_3722_);
lean_dec(v_00_u03c4_u2081_u2082_3720_);
lean_dec(v_i_3718_);
lean_dec_ref(v_N_3717_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3(lean_object* v_N_3724_, lean_object* v_i_3725_, lean_object* v___x_3726_, lean_object* v_S_3727_, lean_object* v_C_3728_, lean_object* v_P_3729_, lean_object* v_hP_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3___redArg(v_P_3729_, v_a_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3___boxed(lean_object* v_N_3733_, lean_object* v_i_3734_, lean_object* v___x_3735_, lean_object* v_S_3736_, lean_object* v_C_3737_, lean_object* v_P_3738_, lean_object* v_hP_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = lp_tree_OreLocalization_liftExpand___at___00OreLocalization_hsmul___at___00Formalism_MainNotions_N_homChi_spec__1_spec__3(v_N_3733_, v_i_3734_, v___x_3735_, v_S_3736_, v_C_3737_, v_P_3738_, v_hP_3739_, v_a_3740_);
lean_dec(v_i_3734_);
lean_dec_ref(v_N_3733_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3(lean_object* v_N_3742_, lean_object* v_i_3743_, lean_object* v___x_3744_, lean_object* v___x_3745_, lean_object* v_00_u03b9_3746_, lean_object* v_s_3747_, lean_object* v_f_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3___redArg(v_N_3742_, v_i_3743_, v___x_3744_, v___x_3745_, v_s_3747_, v_f_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__10___redArg(lean_object* v_f_3750_, lean_object* v_q_u2081_3751_, lean_object* v_q_u2082_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_apply_2(v_f_3750_, v_q_u2081_3751_, v_q_u2082_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* lp_tree_Quotient_map_u2082___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__10(lean_object* v_f_3754_, lean_object* v_h_3755_, lean_object* v_q_u2081_3756_, lean_object* v_q_u2082_3757_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_apply_2(v_f_3754_, v_q_u2081_3756_, v_q_u2082_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6(lean_object* v_N_3759_, lean_object* v_i_3760_, lean_object* v___x_3761_, lean_object* v___x_3762_, lean_object* v_s_3763_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6___redArg(v_N_3759_, v_i_3760_, v___x_3761_, v_s_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__11(lean_object* v_N_3765_, lean_object* v_i_3766_, lean_object* v___x_3767_, lean_object* v_S_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = lp_tree_OreLocalization_zero___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__11___redArg(v_N_3765_, v_i_3766_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object* v_s_3770_){
_start:
{
lean_inc(v_s_3770_);
return v_s_3770_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object* v_s_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_s_3771_);
lean_dec(v_s_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object* v_N_3773_, lean_object* v_i_3774_, lean_object* v___x_3775_, lean_object* v_S_3776_, lean_object* v_r_3777_, lean_object* v_s_3778_){
_start:
{
lean_inc(v_s_3778_);
return v_s_3778_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object* v_N_3779_, lean_object* v_i_3780_, lean_object* v___x_3781_, lean_object* v_S_3782_, lean_object* v_r_3783_, lean_object* v_s_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = lp_tree_OreLocalization_oreDenom___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__16(v_N_3779_, v_i_3780_, v___x_3781_, v_S_3782_, v_r_3783_, v_s_3784_);
lean_dec(v_s_3784_);
lean_dec(v_r_3783_);
lean_dec(v_i_3780_);
lean_dec_ref(v_N_3779_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___redArg(lean_object* v_r_3786_){
_start:
{
lean_inc(v_r_3786_);
return v_r_3786_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___redArg___boxed(lean_object* v_r_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___redArg(v_r_3787_);
lean_dec(v_r_3787_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17(lean_object* v_N_3789_, lean_object* v_i_3790_, lean_object* v___x_3791_, lean_object* v_S_3792_, lean_object* v_r_3793_, lean_object* v_s_3794_){
_start:
{
lean_inc(v_r_3793_);
return v_r_3793_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17___boxed(lean_object* v_N_3795_, lean_object* v_i_3796_, lean_object* v___x_3797_, lean_object* v_S_3798_, lean_object* v_r_3799_, lean_object* v_s_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = lp_tree_OreLocalization_oreNum___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14_spec__17(v_N_3795_, v_i_3796_, v___x_3797_, v_S_3798_, v_r_3799_, v_s_3800_);
lean_dec(v_s_3800_);
lean_dec(v_r_3799_);
lean_dec(v_i_3796_);
lean_dec_ref(v_N_3795_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14(lean_object* v_N_3802_, lean_object* v_i_3803_, lean_object* v___x_3804_, lean_object* v_S_3805_, lean_object* v_r_u2081_3806_, lean_object* v_s_u2081_3807_, lean_object* v_r_u2082_3808_, lean_object* v_s_u2082_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = lp_tree___private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add_x27___at___00__private_Mathlib_RingTheory_OreLocalization_Basic_0__OreLocalization_add___at___00Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_N_homChi_spec__3_spec__6_spec__9_spec__12_spec__14___redArg(v_N_3802_, v_i_3803_, v_r_u2081_3806_, v_s_u2081_3807_, v_r_u2082_3808_, v_s_u2082_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__0(lean_object* v_R_3811_, lean_object* v_N_3812_, lean_object* v_i_3813_, lean_object* v_S_3814_, lean_object* v_x_x27_3815_, lean_object* v_a_3816_, lean_object* v_j_3817_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = lp_tree_Formalism_MainNotions_N_Eel___redArg(v_R_3811_, v_N_3812_, v_i_3813_, v_S_3814_, v_x_x27_3815_, v_j_3817_, v_a_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__0___boxed(lean_object* v_R_3819_, lean_object* v_N_3820_, lean_object* v_i_3821_, lean_object* v_S_3822_, lean_object* v_x_x27_3823_, lean_object* v_a_3824_, lean_object* v_j_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = lp_tree_Formalism_MainNotions_N_yg___redArg___lam__0(v_R_3819_, v_N_3820_, v_i_3821_, v_S_3822_, v_x_x27_3823_, v_a_3824_, v_j_3825_);
lean_dec_ref(v_R_3819_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__1(lean_object* v_R_3827_, lean_object* v_N_3828_, lean_object* v_i_3829_, lean_object* v_r_3830_, lean_object* v___x_3831_, lean_object* v_00_u03b3_3832_, lean_object* v_a_3833_, lean_object* v_j_3834_){
_start:
{
lean_object* v___x_492__overap_3835_; lean_object* v___x_3836_; 
v___x_492__overap_3835_ = lp_tree_Formalism_MainNotions_N_rO___redArg(v_R_3827_, v_N_3828_, v_i_3829_, v_r_3830_, v___x_3831_);
v___x_3836_ = lean_apply_3(v___x_492__overap_3835_, v_00_u03b3_3832_, v_a_3833_, v_j_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg___lam__1___boxed(lean_object* v_R_3837_, lean_object* v_N_3838_, lean_object* v_i_3839_, lean_object* v_r_3840_, lean_object* v___x_3841_, lean_object* v_00_u03b3_3842_, lean_object* v_a_3843_, lean_object* v_j_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = lp_tree_Formalism_MainNotions_N_yg___redArg___lam__1(v_R_3837_, v_N_3838_, v_i_3839_, v_r_3840_, v___x_3841_, v_00_u03b3_3842_, v_a_3843_, v_j_3844_);
lean_dec(v_i_3839_);
lean_dec_ref(v_N_3838_);
lean_dec_ref(v_R_3837_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___redArg(lean_object* v_R_3846_, lean_object* v_N_3847_, lean_object* v_i_3848_, lean_object* v_r_3849_, lean_object* v_S_3850_, lean_object* v_00_u03b3_3851_, lean_object* v_x_x27_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_instO_3855_; lean_object* v_chi_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_toSub_3860_; lean_object* v_toSemiring_3861_; lean_object* v___x_3862_; lean_object* v_toMul_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v_inv_3866_; lean_object* v_p_3867_; lean_object* v___f_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___f_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_instO_3855_ = lean_ctor_get(v_N_3847_, 9);
v_chi_3856_ = lean_ctor_get(v_N_3847_, 19);
lean_inc_ref(v_instO_3855_);
lean_inc_n(v_i_3848_, 5);
v___x_3857_ = lean_apply_1(v_instO_3855_, v_i_3848_);
lean_inc_ref(v___x_3857_);
v___x_3858_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_3857_);
v___x_3859_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_3858_);
lean_dec_ref(v___x_3858_);
v_toSub_3860_ = lean_ctor_get(v___x_3859_, 2);
lean_inc(v_toSub_3860_);
lean_dec_ref(v___x_3859_);
v_toSemiring_3861_ = lean_ctor_get(v___x_3857_, 0);
lean_inc_ref(v_toSemiring_3861_);
lean_dec_ref(v___x_3857_);
v___x_3862_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_3861_);
v_toMul_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_toMul_3863_);
lean_dec_ref(v___x_3862_);
v___x_3864_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_chi_3856_);
lean_inc_ref(v_00_u03b3_3851_);
v___x_3865_ = lean_apply_3(v_chi_3856_, v_i_3848_, v___x_3864_, v_00_u03b3_3851_);
v_inv_3866_ = lean_ctor_get(v___x_3865_, 1);
lean_inc(v_inv_3866_);
lean_dec_ref(v___x_3865_);
v_p_3867_ = lean_ctor_get(v_S_3850_, 6);
lean_inc(v_a_3854_);
lean_inc_n(v_x_x27_3852_, 2);
lean_inc_ref(v_S_3850_);
lean_inc_ref_n(v_N_3847_, 3);
lean_inc_ref_n(v_R_3846_, 2);
v___f_3868_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_yg___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3868_, 0, v_R_3846_);
lean_closure_set(v___f_3868_, 1, v_N_3847_);
lean_closure_set(v___f_3868_, 2, v_i_3848_);
lean_closure_set(v___f_3868_, 3, v_S_3850_);
lean_closure_set(v___f_3868_, 4, v_x_x27_3852_);
lean_closure_set(v___f_3868_, 5, v_a_3854_);
v___x_3869_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_3846_);
lean_inc(v_p_3867_);
v___x_3870_ = lean_apply_1(v_p_3867_, v_x_x27_3852_);
lean_inc(v_a_3853_);
v___f_3871_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_N_yg___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_3871_, 0, v_R_3846_);
lean_closure_set(v___f_3871_, 1, v_N_3847_);
lean_closure_set(v___f_3871_, 2, v_i_3848_);
lean_closure_set(v___f_3871_, 3, v_r_3849_);
lean_closure_set(v___f_3871_, 4, v___x_3870_);
lean_closure_set(v___f_3871_, 5, v_00_u03b3_3851_);
lean_closure_set(v___f_3871_, 6, v_a_3853_);
v___x_3872_ = lp_tree_dotProduct___at___00List_prod___at___00Formalism_MainNotions_N_Eel_spec__1_spec__1(v___x_3869_, v_N_3847_, v_i_3848_, v___f_3871_, v___f_3868_);
v___x_3873_ = lean_apply_2(v_toMul_3863_, v_inv_3866_, v___x_3872_);
v___x_3874_ = lp_tree_Formalism_MainNotions_N_Eel___redArg(v_R_3846_, v_N_3847_, v_i_3848_, v_S_3850_, v_x_x27_3852_, v_a_3853_, v_a_3854_);
lean_dec_ref(v_R_3846_);
v___x_3875_ = lean_apply_2(v_toSub_3860_, v___x_3873_, v___x_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg(lean_object* v_R_3876_, lean_object* v_H_3877_, lean_object* v_what_u2082_3878_, lean_object* v_N_3879_, lean_object* v_i_3880_, lean_object* v_r_3881_, lean_object* v_S_3882_, lean_object* v_00_u03b3_3883_, lean_object* v_x_x27_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = lp_tree_Formalism_MainNotions_N_yg___redArg(v_R_3876_, v_N_3879_, v_i_3880_, v_r_3881_, v_S_3882_, v_00_u03b3_3883_, v_x_x27_3884_, v_a_3885_, v_a_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_yg___boxed(lean_object* v_R_3888_, lean_object* v_H_3889_, lean_object* v_what_u2082_3890_, lean_object* v_N_3891_, lean_object* v_i_3892_, lean_object* v_r_3893_, lean_object* v_S_3894_, lean_object* v_00_u03b3_3895_, lean_object* v_x_x27_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = lp_tree_Formalism_MainNotions_N_yg(v_R_3888_, v_H_3889_, v_what_u2082_3890_, v_N_3891_, v_i_3892_, v_r_3893_, v_S_3894_, v_00_u03b3_3895_, v_x_x27_3896_, v_a_3897_, v_a_3898_);
lean_dec_ref(v_what_u2082_3890_);
lean_dec_ref(v_H_3889_);
return v_res_3899_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__0(void){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = lp_mathlib_TopologicalSpace_instCompleteLattice(lean_box(0));
return v___x_3900_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__1(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_obj_once(&lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__0, &lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__0_once, _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__0);
v___x_3902_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr(lean_object* v_R_3903_, lean_object* v_H_3904_, lean_object* v_what_u2082_3905_, lean_object* v_N_3906_, lean_object* v_i_3907_){
_start:
{
lean_object* v___x_3908_; lean_object* v_toOrderBot_3909_; 
v___x_3908_ = lean_obj_once(&lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__1, &lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__1_once, _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___closed__1);
v_toOrderBot_3909_ = lean_ctor_get(v___x_3908_, 2);
lean_inc(v_toOrderBot_3909_);
return v_toOrderBot_3909_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr___boxed(lean_object* v_R_3910_, lean_object* v_H_3911_, lean_object* v_what_u2082_3912_, lean_object* v_N_3913_, lean_object* v_i_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKr(v_R_3910_, v_H_3911_, v_what_u2082_3912_, v_N_3913_, v_i_3914_);
lean_dec(v_i_3914_);
lean_dec_ref(v_N_3913_);
lean_dec_ref(v_what_u2082_3912_);
lean_dec_ref(v_H_3911_);
lean_dec_ref(v_R_3910_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdG(lean_object* v_O_3916_, lean_object* v_LL_3917_, lean_object* v_inst_3918_, lean_object* v_inst_3919_, lean_object* v_inst_3920_, lean_object* v_k_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_box(0);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdG___boxed(lean_object* v_O_3923_, lean_object* v_LL_3924_, lean_object* v_inst_3925_, lean_object* v_inst_3926_, lean_object* v_inst_3927_, lean_object* v_k_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = lp_tree_Formalism_MainNotions_N_stdG(v_O_3923_, v_LL_3924_, v_inst_3925_, v_inst_3926_, v_inst_3927_, v_k_3928_);
lean_dec(v_k_3928_);
lean_dec_ref(v_inst_3927_);
lean_dec_ref(v_inst_3926_);
lean_dec_ref(v_inst_3925_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLatG(lean_object* v_O_3930_, lean_object* v_LL_3931_, lean_object* v_inst_3932_, lean_object* v_inst_3933_, lean_object* v_inst_3934_, lean_object* v_hinj_3935_, lean_object* v_00_u0393_3936_, lean_object* v_inst_3937_, lean_object* v_k_3938_, lean_object* v_M_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_box(0);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_stdLatG___boxed(lean_object* v_O_3941_, lean_object* v_LL_3942_, lean_object* v_inst_3943_, lean_object* v_inst_3944_, lean_object* v_inst_3945_, lean_object* v_hinj_3946_, lean_object* v_00_u0393_3947_, lean_object* v_inst_3948_, lean_object* v_k_3949_, lean_object* v_M_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = lp_tree_Formalism_MainNotions_N_stdLatG(v_O_3941_, v_LL_3942_, v_inst_3943_, v_inst_3944_, v_inst_3945_, v_hinj_3946_, v_00_u0393_3947_, v_inst_3948_, v_k_3949_, v_M_3950_);
lean_dec(v_M_3950_);
lean_dec(v_k_3949_);
lean_dec_ref(v_inst_3948_);
lean_dec_ref(v_inst_3945_);
lean_dec_ref(v_inst_3944_);
lean_dec_ref(v_inst_3943_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOG(lean_object* v_O_3952_, lean_object* v_inst_3953_, lean_object* v_inst_3954_, lean_object* v_k_3955_){
_start:
{
lean_object* v___x_3956_; lean_object* v_toOrderBot_3957_; 
v___x_3956_ = lean_obj_once(&lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1, &lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1_once, _init_lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOr___closed__1);
v_toOrderBot_3957_ = lean_ctor_get(v___x_3956_, 2);
lean_inc(v_toOrderBot_3957_);
return v_toOrderBot_3957_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOG___boxed(lean_object* v_O_3958_, lean_object* v_inst_3959_, lean_object* v_inst_3960_, lean_object* v_k_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = lp_tree_Formalism_MainNotions_N_instTopologicalSpaceKOG(v_O_3958_, v_inst_3959_, v_inst_3960_, v_k_3961_);
lean_dec(v_k_3961_);
lean_dec_ref(v_inst_3959_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Br_PD___redArg(lean_object* v_N_3963_, lean_object* v_L_3964_, lean_object* v_nbr_3965_, lean_object* v_i_3966_, lean_object* v_w_3967_){
_start:
{
lean_object* v_l_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v_PD_3971_; lean_object* v___x_3972_; lean_object* v_Kw_3973_; lean_object* v___x_3974_; 
v_l_3968_ = lean_ctor_get(v_N_3963_, 4);
lean_inc_ref(v_l_3968_);
lean_dec_ref(v_N_3963_);
lean_inc(v_i_3966_);
v___x_3969_ = lean_apply_1(v_l_3968_, v_i_3966_);
v___x_3970_ = lean_apply_2(v_L_3964_, v___x_3969_, lean_box(0));
v_PD_3971_ = lean_ctor_get(v___x_3970_, 1);
lean_inc_ref(v_PD_3971_);
lean_dec_ref(v___x_3970_);
v___x_3972_ = lean_apply_3(v_nbr_3965_, v_i_3966_, v_w_3967_, lean_box(0));
v_Kw_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_Kw_3973_);
lean_dec_ref(v___x_3972_);
v___x_3974_ = lean_apply_1(v_PD_3971_, v_Kw_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Br_PD(lean_object* v_R_3975_, lean_object* v_H_3976_, lean_object* v_what_u2082_3977_, lean_object* v_N_3978_, lean_object* v_L_3979_, lean_object* v_nbr_3980_, lean_object* v_i_3981_, lean_object* v_w_3982_, lean_object* v_hw_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = lp_tree_Formalism_MainNotions_N_Br_PD___redArg(v_N_3978_, v_L_3979_, v_nbr_3980_, v_i_3981_, v_w_3982_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_N_Br_PD___boxed(lean_object* v_R_3985_, lean_object* v_H_3986_, lean_object* v_what_u2082_3987_, lean_object* v_N_3988_, lean_object* v_L_3989_, lean_object* v_nbr_3990_, lean_object* v_i_3991_, lean_object* v_w_3992_, lean_object* v_hw_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = lp_tree_Formalism_MainNotions_N_Br_PD(v_R_3985_, v_H_3986_, v_what_u2082_3987_, v_N_3988_, v_L_3989_, v_nbr_3990_, v_i_3991_, v_w_3992_, v_hw_3993_);
lean_dec_ref(v_what_u2082_3987_);
lean_dec_ref(v_H_3986_);
lean_dec_ref(v_R_3985_);
return v_res_3994_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataN(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc(uint8_t builtin);
lean_object* initialize_tree_Formalism_WeaklyAdmissibleFiltrations_StatementTor(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaloisCohomology_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_WeaklyAdmissibleFiltrations_StatementTor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaloisCohomology_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
