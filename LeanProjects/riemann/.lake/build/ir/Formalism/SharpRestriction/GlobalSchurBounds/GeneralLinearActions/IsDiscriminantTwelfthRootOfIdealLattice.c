// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* lp_mathlib_Additive_ofMul(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Additive_toMul(lean_object*);
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toMonoidWithZero___redArg(lean_object*);
lean_object* lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
uint8_t lp_mathlib_Fintype_IsSquare_decidablePred___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0;
static lean_once_cell_t lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1;
static lean_once_cell_t lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_chK(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_fF(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_fF___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_homL_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_homL_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_YYl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_YYl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_lamOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_lamOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_La(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_La___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___lam__0(lean_object*);
static const lean_closure_object lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_detId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_detId_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___closed__0 = (const lean_object*)&lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg___lam__0(lean_object* v_00_u03c7_1_, lean_object* v_f_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_00_u03c7_1_, v_a_3_);
v___x_5_ = lean_apply_1(v_f_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg(lean_object* v_00_u03c7_6_, lean_object* v_f_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_8_, 0, v_00_u03c7_6_);
lean_closure_set(v___f_8_, 1, v_f_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1(lean_object* v___x_9_, lean_object* v_00_u03c7_10_, lean_object* v_f_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = lean_alloc_closure((void*)(lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_12_, 0, v_00_u03c7_10_);
lean_closure_set(v___f_12_, 1, v_f_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___boxed(lean_object* v___x_13_, lean_object* v_00_u03c7_14_, lean_object* v_f_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1(v___x_13_, v_00_u03c7_14_, v_f_15_);
lean_dec(v___x_13_);
return v_res_16_;
}
}
static lean_object* _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_to_int(v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0);
v___x_20_ = lean_int_neg(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0(lean_object* v___x_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_toSemiring_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_toMul_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_toZero_34_; uint8_t v___x_35_; 
lean_inc(v___x_23_);
v___x_25_ = lp_mathlib_ZMod_instField___redArg(v___x_23_);
v___x_26_ = lp_mathlib_Field_toSemifield___redArg(v___x_25_);
lean_dec_ref(v___x_25_);
v___x_27_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_26_);
v_toSemiring_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_ref(v_toSemiring_28_);
lean_dec_ref(v___x_27_);
v___x_29_ = lp_mathlib_Semiring_toMonoidWithZero___redArg(v_toSemiring_28_);
v___x_30_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_28_);
v_toMul_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_toMul_31_);
lean_dec_ref(v___x_30_);
v___x_32_ = lp_mathlib_MonoidWithZero_toMulZeroOneClass___redArg(v___x_29_);
v___x_33_ = lp_mathlib_MulZeroOneClass_toMulZeroClass___redArg(v___x_32_);
v_toZero_34_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_toZero_34_);
lean_dec_ref(v___x_33_);
v___x_35_ = lp_mathlib_ZMod_decidableEq(v___x_23_, v_a_24_, v_toZero_34_);
lean_dec(v_toZero_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
lean_inc(v___x_23_);
v___x_36_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_36_, 0, v___x_23_);
v___x_37_ = lp_mathlib_ZMod_fintype___redArg(v___x_23_);
lean_dec(v___x_23_);
v___x_38_ = lp_mathlib_Fintype_IsSquare_decidablePred___redArg(v_toMul_31_, v___x_37_, v___x_36_, v_a_24_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1);
return v___x_39_;
}
else
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0);
return v___x_40_;
}
}
else
{
lean_object* v___x_41_; 
lean_dec(v_toMul_31_);
lean_dec(v_a_24_);
lean_dec(v___x_23_);
v___x_41_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__2, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__2_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__2);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0___lam__0(lean_object* v___x_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0(v___x_42_, v___y_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0(lean_object* v___x_45_){
_start:
{
lean_object* v___f_46_; 
v___f_46_ = lean_alloc_closure((void*)(lp_tree_quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_46_, 0, v___x_45_);
return v___f_46_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lp_mathlib_Complex_commRing;
v___x_48_ = lp_mathlib_Ring_toNonAssocRing___redArg(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__0, &lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__0_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__0);
v___x_50_ = lp_mathlib_Int_castRingHom___redArg(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_chK(lean_object* v_D_51_){
_start:
{
lean_object* v_host_52_; lean_object* v_toHostAx_53_; lean_object* v_d_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___f_57_; 
v_host_52_ = lean_ctor_get(v_D_51_, 1);
lean_inc_ref(v_host_52_);
lean_dec_ref(v_D_51_);
v_toHostAx_53_ = lean_ctor_get(v_host_52_, 0);
lean_inc_ref(v_toHostAx_53_);
lean_dec_ref(v_host_52_);
v_d_54_ = lean_ctor_get(v_toHostAx_53_, 1);
lean_inc(v_d_54_);
lean_dec_ref(v_toHostAx_53_);
v___f_55_ = lean_alloc_closure((void*)(lp_tree_quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_55_, 0, v_d_54_);
v___x_56_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__1, &lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__1_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_chK___closed__1);
v___f_57_ = lean_alloc_closure((void*)(lp_tree_MulChar_ringHomComp___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_57_, 0, v___f_55_);
lean_closure_set(v___f_57_, 1, v___x_56_);
return v___f_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_fF(lean_object* v_D_58_){
_start:
{
lean_object* v_R_59_; lean_object* v___x_60_; 
v_R_59_ = lean_ctor_get(v_D_58_, 0);
v___x_60_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_fF___boxed(lean_object* v_D_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_fF(v_D_61_);
lean_dec_ref(v_D_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_homL_spec__0(lean_object* v___x_63_, lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_homL_spec__0___boxed(lean_object* v___x_66_, lean_object* v_s_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_homL_spec__0(v___x_66_, v_s_67_);
lean_dec_ref(v___x_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___redArg(lean_object* v_D_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___redArg___boxed(lean_object* v_D_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___redArg(v_D_71_);
lean_dec_ref(v_D_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL(lean_object* v_D_73_, lean_object* v_N_74_, lean_object* v_N_x27_75_, lean_object* v_L_76_, lean_object* v_L_x27_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_homL___boxed(lean_object* v_D_79_, lean_object* v_N_80_, lean_object* v_N_x27_81_, lean_object* v_L_82_, lean_object* v_L_x27_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_homL(v_D_79_, v_N_80_, v_N_x27_81_, v_L_82_, v_L_x27_83_);
lean_dec(v_N_x27_81_);
lean_dec(v_N_80_);
lean_dec_ref(v_D_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_YYl(lean_object* v_D_85_, lean_object* v_N_86_, lean_object* v_N_x27_87_, lean_object* v_L_88_, lean_object* v_L_x27_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_YYl___boxed(lean_object* v_D_91_, lean_object* v_N_92_, lean_object* v_N_x27_93_, lean_object* v_L_94_, lean_object* v_L_x27_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_YYl(v_D_91_, v_N_92_, v_N_x27_93_, v_L_94_, v_L_x27_95_);
lean_dec(v_N_x27_93_);
lean_dec(v_N_92_);
lean_dec_ref(v_D_91_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__2(lean_object* v_S_97_, lean_object* v_s_98_, lean_object* v_hs_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__1(lean_object* v_00_u03b9_101_, lean_object* v_s_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__1___boxed(lean_object* v_00_u03b9_104_, lean_object* v_s_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__1(v_00_u03b9_104_, v_s_105_);
lean_dec_ref(v_s_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__0(lean_object* v_00_u03b9_107_, lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__0___boxed(lean_object* v_00_u03b9_110_, lean_object* v_s_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0_spec__0(v_00_u03b9_110_, v_s_111_);
lean_dec_ref(v_s_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0___lam__0(lean_object* v_S_113_, lean_object* v_h_114_){
_start:
{
return v_S_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0___lam__1(lean_object* v_S_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_lamOf_spec__0(lean_object* v_k_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_lamOf(lean_object* v_D_119_, lean_object* v_cc_120_, lean_object* v_00_u03b4_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_lamOf___boxed(lean_object* v_D_123_, lean_object* v_cc_124_, lean_object* v_00_u03b4_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_lamOf(v_D_123_, v_cc_124_, v_00_u03b4_125_);
lean_dec_ref(v_00_u03b4_125_);
lean_dec_ref(v_D_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(lean_object* v_T_127_, lean_object* v_A_128_, lean_object* v_00_u03c4_129_, lean_object* v_i_130_, lean_object* v_j_131_){
_start:
{
lean_object* v_emb_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_emb_132_ = lean_ctor_get(v_T_127_, 0);
lean_inc_ref(v_emb_132_);
lean_dec_ref(v_T_127_);
v___x_133_ = lean_apply_2(v_A_128_, v_i_130_, v_j_131_);
v___x_134_ = lean_apply_2(v_emb_132_, v_00_u03c4_129_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV(lean_object* v_D_135_, lean_object* v_T_136_, lean_object* v_N_137_, lean_object* v_N_x27_138_, lean_object* v_A_139_, lean_object* v_00_u03c4_140_, lean_object* v_i_141_, lean_object* v_j_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(v_T_136_, v_A_139_, v_00_u03c4_140_, v_i_141_, v_j_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___boxed(lean_object* v_D_144_, lean_object* v_T_145_, lean_object* v_N_146_, lean_object* v_N_x27_147_, lean_object* v_A_148_, lean_object* v_00_u03c4_149_, lean_object* v_i_150_, lean_object* v_j_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_embV(v_D_144_, v_T_145_, v_N_146_, v_N_x27_147_, v_A_148_, v_00_u03c4_149_, v_i_150_, v_j_151_);
lean_dec(v_N_x27_147_);
lean_dec(v_N_146_);
lean_dec_ref(v_D_144_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__1(lean_object* v_00_u03b9_153_, lean_object* v_s_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__1___boxed(lean_object* v_00_u03b9_156_, lean_object* v_s_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__1(v_00_u03b9_156_, v_s_157_);
lean_dec_ref(v_s_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__2(lean_object* v_S_159_, lean_object* v_s_160_, lean_object* v_hs_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_box(0);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__0(lean_object* v_00_u03b9_163_, lean_object* v_s_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__0___boxed(lean_object* v_00_u03b9_166_, lean_object* v_s_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_tree_iInf___at___00AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0_spec__0(v_00_u03b9_166_, v_s_167_);
lean_dec_ref(v_s_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0___lam__0(lean_object* v_S_169_, lean_object* v_h_170_){
_start:
{
return v_S_169_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0___lam__1(lean_object* v_S_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_closure___at___00Formalism_MainNotions_TaylorLogMetric_La_spec__0(lean_object* v_k_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_La(lean_object* v_D_175_, lean_object* v_T_176_, lean_object* v_N_177_, lean_object* v_N_x27_178_, lean_object* v_L_179_, lean_object* v_L_x27_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_box(0);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_La___boxed(lean_object* v_D_182_, lean_object* v_T_183_, lean_object* v_N_184_, lean_object* v_N_x27_185_, lean_object* v_L_186_, lean_object* v_L_x27_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_La(v_D_182_, v_T_183_, v_N_184_, v_N_x27_185_, v_L_186_, v_L_x27_187_);
lean_dec(v_N_x27_185_);
lean_dec(v_N_184_);
lean_dec_ref(v_T_183_);
lean_dec_ref(v_D_182_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___lam__0(lean_object* v_z_189_){
_start:
{
lean_object* v_re_190_; lean_object* v_im_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_re_190_ = lean_ctor_get(v_z_189_, 0);
v_im_191_ = lean_ctor_get(v_z_189_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_z_189_);
if (v_isSharedCheck_199_ == 0)
{
v___x_193_ = v_z_189_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_im_191_);
lean_inc(v_re_190_);
lean_dec(v_z_189_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___f_195_; lean_object* v___x_197_; 
v___f_195_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_195_, 0, v_im_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___f_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_re_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___f_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg(lean_object* v_M_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___f_204_ = ((lean_object*)(lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg___closed__0));
v___x_205_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_205_, 0, lean_box(0));
lean_closure_set(v___x_205_, 1, lean_box(0));
lean_closure_set(v___x_205_, 2, lean_box(0));
lean_closure_set(v___x_205_, 3, v_M_201_);
v___x_206_ = lp_mathlib_Matrix_map___redArg(v___x_205_, v___f_204_, v_a_202_, v_a_203_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0(lean_object* v_m_207_, lean_object* v_n_208_, lean_object* v_M_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg(v_M_209_, v_a_210_, v_a_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__0(lean_object* v_00_u03b3_213_, lean_object* v___x_214_, lean_object* v___y_215_, lean_object* v_j_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lp_mathlib_Matrix_map___redArg(v_00_u03b3_213_, v___x_214_, v_j_216_, v___y_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__1(lean_object* v___x_218_, lean_object* v___y_219_, lean_object* v_j_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lp_tree_Matrix_conjTranspose___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__0___redArg(v___x_218_, v___y_219_, v_j_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__2(lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v_j_224_, lean_object* v_j_225_){
_start:
{
lean_object* v_toFun_226_; lean_object* v___x_227_; 
v_toFun_226_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_toFun_226_);
lean_dec_ref(v___x_222_);
v___x_227_ = lean_apply_3(v_toFun_226_, v___x_223_, v_j_225_, v_j_224_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(lean_object* v_s_228_, lean_object* v_f_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lp_mathlib_Multiset_map___redArg(v_f_229_, v_s_228_);
v___x_231_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1___lam__0(lean_object* v_v_232_, lean_object* v_w_233_, lean_object* v_i_234_){
_start:
{
lean_object* v___x_235_; lean_object* v_re_236_; lean_object* v_im_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_inc(v_i_234_);
v___x_235_ = lean_apply_1(v_v_232_, v_i_234_);
v_re_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_re_236_);
v_im_237_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_im_237_);
lean_dec_ref(v___x_235_);
v___x_238_ = lean_apply_1(v_w_233_, v_i_234_);
v___x_239_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_236_, v_im_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1(lean_object* v_N_x27_240_, lean_object* v_v_241_, lean_object* v_w_242_){
_start:
{
lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___f_243_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_243_, 0, v_v_241_);
lean_closure_set(v___f_243_, 1, v_w_242_);
v___x_244_ = l_List_finRange(v_N_x27_240_);
v___x_245_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v___x_244_, v___f_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__3(lean_object* v___x_246_, lean_object* v___x_247_, lean_object* v_N_x27_248_, lean_object* v___f_249_, lean_object* v_j_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_252_; 
v___f_251_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__2), 4, 3);
lean_closure_set(v___f_251_, 0, v___x_246_);
lean_closure_set(v___f_251_, 1, v___x_247_);
lean_closure_set(v___f_251_, 2, v_j_250_);
v___x_252_ = lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1(v_N_x27_248_, v___f_249_, v___f_251_);
return v___x_252_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4(lean_object* v_T_254_, lean_object* v_00_u03b3_255_, lean_object* v_00_u03b3_x27_256_, lean_object* v_z_257_, lean_object* v_N_x27_258_, lean_object* v_N_259_, lean_object* v_00_u03c4_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_emb_263_; lean_object* v___x_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___x_271_; 
v_emb_263_ = lean_ctor_get(v_T_254_, 0);
lean_inc_ref(v_emb_263_);
lean_dec_ref(v_T_254_);
lean_inc(v_00_u03c4_260_);
v___x_264_ = lean_apply_1(v_emb_263_, v_00_u03c4_260_);
lean_inc_ref(v___x_264_);
v___f_265_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__0), 4, 3);
lean_closure_set(v___f_265_, 0, v_00_u03b3_255_);
lean_closure_set(v___f_265_, 1, v___x_264_);
lean_closure_set(v___f_265_, 2, v___y_262_);
v___x_266_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_map), 8, 6);
lean_closure_set(v___x_266_, 0, lean_box(0));
lean_closure_set(v___x_266_, 1, lean_box(0));
lean_closure_set(v___x_266_, 2, lean_box(0));
lean_closure_set(v___x_266_, 3, lean_box(0));
lean_closure_set(v___x_266_, 4, v_00_u03b3_x27_256_);
lean_closure_set(v___x_266_, 5, v___x_264_);
v___f_267_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__1), 3, 2);
lean_closure_set(v___f_267_, 0, v___x_266_);
lean_closure_set(v___f_267_, 1, v___y_261_);
v___x_268_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4___closed__0, &lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4___closed__0_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4___closed__0);
v___x_269_ = lean_apply_1(v_z_257_, v_00_u03c4_260_);
v___f_270_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__3), 5, 4);
lean_closure_set(v___f_270_, 0, v___x_268_);
lean_closure_set(v___f_270_, 1, v___x_269_);
lean_closure_set(v___f_270_, 2, v_N_x27_258_);
lean_closure_set(v___f_270_, 3, v___f_267_);
v___x_271_ = lp_tree_dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1(v_N_259_, v___f_270_, v___f_265_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg(lean_object* v_T_272_, lean_object* v_N_273_, lean_object* v_N_x27_274_, lean_object* v_00_u03b3_275_, lean_object* v_00_u03b3_x27_276_, lean_object* v_G_277_, lean_object* v_z_278_){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; 
v___f_279_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg___lam__4), 9, 6);
lean_closure_set(v___f_279_, 0, v_T_272_);
lean_closure_set(v___f_279_, 1, v_00_u03b3_275_);
lean_closure_set(v___f_279_, 2, v_00_u03b3_x27_276_);
lean_closure_set(v___f_279_, 3, v_z_278_);
lean_closure_set(v___f_279_, 4, v_N_x27_274_);
lean_closure_set(v___f_279_, 5, v_N_273_);
v___x_280_ = lean_apply_1(v_G_277_, v___f_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull(lean_object* v_D_281_, lean_object* v_T_282_, lean_object* v_N_283_, lean_object* v_N_x27_284_, lean_object* v_00_u03b3_285_, lean_object* v_00_u03b3_x27_286_, lean_object* v_G_287_, lean_object* v_z_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___redArg(v_T_282_, v_N_283_, v_N_x27_284_, v_00_u03b3_285_, v_00_u03b3_x27_286_, v_G_287_, v_z_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_pull___boxed(lean_object* v_D_290_, lean_object* v_T_291_, lean_object* v_N_292_, lean_object* v_N_x27_293_, lean_object* v_00_u03b3_294_, lean_object* v_00_u03b3_x27_295_, lean_object* v_G_296_, lean_object* v_z_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_pull(v_D_290_, v_T_291_, v_N_292_, v_N_x27_293_, v_00_u03b3_294_, v_00_u03b3_x27_295_, v_G_296_, v_z_297_);
lean_dec_ref(v_D_290_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1(lean_object* v_00_u03b9_299_, lean_object* v_s_300_, lean_object* v_f_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_MainNotions_TaylorLogMetric_pull_spec__1_spec__1___redArg(v_s_300_, v_f_301_);
return v___x_302_;
}
}
static lean_object* _init_lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_304_ = lp_mathlib_Complex_ofReal(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_zero_307_; uint8_t v_isZero_308_; 
v_zero_307_ = lean_unsigned_to_nat(0u);
v_isZero_308_ = lean_nat_dec_eq(v_x_305_, v_zero_307_);
if (v_isZero_308_ == 1)
{
lean_object* v___x_309_; 
lean_dec_ref(v_x_306_);
v___x_309_ = lean_obj_once(&lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0, &lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0_once, _init_lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0);
return v___x_309_;
}
else
{
lean_object* v_one_310_; lean_object* v_n_311_; lean_object* v___x_312_; lean_object* v_re_313_; lean_object* v_im_314_; lean_object* v___x_315_; 
v_one_310_ = lean_unsigned_to_nat(1u);
v_n_311_ = lean_nat_sub(v_x_305_, v_one_310_);
lean_inc_ref(v_x_306_);
v___x_312_ = lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(v_n_311_, v_x_306_);
lean_dec(v_n_311_);
v_re_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_re_313_);
v_im_314_ = lean_ctor_get(v___x_312_, 1);
lean_inc(v_im_314_);
lean_dec_ref(v___x_312_);
v___x_315_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_313_, v_im_314_, v_x_306_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___boxed(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(v_x_316_, v_x_317_);
lean_dec(v_x_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg___lam__0(lean_object* v_z_319_, lean_object* v_k_320_, lean_object* v_n_321_){
_start:
{
lean_object* v_snd_322_; lean_object* v_fst_323_; lean_object* v_fst_324_; lean_object* v_snd_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_snd_322_ = lean_ctor_get(v_k_320_, 1);
lean_inc(v_snd_322_);
v_fst_323_ = lean_ctor_get(v_k_320_, 0);
lean_inc(v_fst_323_);
lean_dec_ref(v_k_320_);
v_fst_324_ = lean_ctor_get(v_snd_322_, 0);
lean_inc(v_fst_324_);
v_snd_325_ = lean_ctor_get(v_snd_322_, 1);
lean_inc(v_snd_325_);
lean_dec(v_snd_322_);
v___x_326_ = lean_apply_3(v_z_319_, v_fst_323_, v_fst_324_, v_snd_325_);
v___x_327_ = lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(v_n_321_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg___lam__0___boxed(lean_object* v_z_328_, lean_object* v_k_329_, lean_object* v_n_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg___lam__0(v_z_328_, v_k_329_, v_n_330_);
lean_dec(v_n_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg___lam__0(lean_object* v_toFun_332_, lean_object* v_g_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc(v_a_334_);
v___x_335_ = lean_apply_1(v_toFun_332_, v_a_334_);
v___x_336_ = lean_apply_2(v_g_333_, v_a_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___lam__0(lean_object* v_x1_337_, lean_object* v_x2_338_){
_start:
{
lean_object* v_re_339_; lean_object* v_im_340_; lean_object* v___x_341_; 
v_re_339_ = lean_ctor_get(v_x1_337_, 0);
lean_inc(v_re_339_);
v_im_340_ = lean_ctor_get(v_x1_337_, 1);
lean_inc(v_im_340_);
lean_dec_ref(v_x1_337_);
v___x_341_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_339_, v_im_340_, v_x2_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2(lean_object* v_s_343_){
_start:
{
lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___f_344_ = ((lean_object*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2___closed__0));
v___x_345_ = lean_obj_once(&lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0, &lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0_once, _init_lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0___closed__0);
v___x_346_ = l_List_foldrTR___redArg(v___f_344_, v___x_345_, v_s_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1___redArg(lean_object* v_s_347_, lean_object* v_f_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lp_mathlib_Multiset_map___redArg(v_f_348_, v_s_347_);
v___x_350_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1_spec__2(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg(lean_object* v_f_351_, lean_object* v_g_352_){
_start:
{
lean_object* v_support_353_; lean_object* v_toFun_354_; lean_object* v___f_355_; lean_object* v___x_356_; 
v_support_353_ = lean_ctor_get(v_f_351_, 0);
lean_inc(v_support_353_);
v_toFun_354_ = lean_ctor_get(v_f_351_, 1);
lean_inc(v_toFun_354_);
lean_dec_ref(v_f_351_);
v___f_355_ = lean_alloc_closure((void*)(lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_355_, 0, v_toFun_354_);
lean_closure_set(v___f_355_, 1, v_g_352_);
v___x_356_ = lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1___redArg(v_support_353_, v___f_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg(lean_object* v_00_u03b1_357_, lean_object* v_z_358_){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; 
v___f_359_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_359_, 0, v_z_358_);
v___x_360_ = lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg(v_00_u03b1_357_, v___f_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono(lean_object* v_D_361_, lean_object* v_N_362_, lean_object* v_N_x27_363_, lean_object* v_00_u03b1_364_, lean_object* v_z_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___redArg(v_00_u03b1_364_, v_z_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_mono___boxed(lean_object* v_D_367_, lean_object* v_N_368_, lean_object* v_N_x27_369_, lean_object* v_00_u03b1_370_, lean_object* v_z_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_mono(v_D_367_, v_N_368_, v_N_x27_369_, v_00_u03b1_370_, v_z_371_);
lean_dec(v_N_x27_369_);
lean_dec(v_N_368_);
lean_dec_ref(v_D_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1(lean_object* v_00_u03b1_373_, lean_object* v_f_374_, lean_object* v_g_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lp_tree_Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1___redArg(v_f_374_, v_g_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1(lean_object* v_00_u03b9_377_, lean_object* v_s_378_, lean_object* v_f_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lp_tree_Finset_prod___at___00Finsupp_prod___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__1_spec__1___redArg(v_s_378_, v_f_379_);
return v___x_380_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__0(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__0);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__1(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_obj_once(&lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1, &lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1_once, _init_lp_tree_quadraticCharFun___at___00quadraticChar___at___00Formalism_MainNotions_TaylorLogMetric_chK_spec__0_spec__0___closed__1);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2(void){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_385_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__0, &lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__0_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__0);
v___x_387_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__1, &lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__1_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__1);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm(lean_object* v_D_389_){
_start:
{
lean_object* v_R_390_; lean_object* v_toFrame_391_; lean_object* v_grp_392_; lean_object* v___x_393_; lean_object* v_toZero_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_405_; 
v_R_390_ = lean_ctor_get(v_D_389_, 0);
v_toFrame_391_ = lean_ctor_get(v_R_390_, 0);
v_grp_392_ = lean_ctor_get(v_toFrame_391_, 2);
v___x_393_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_grp_392_);
v_toZero_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_393_, 1);
lean_dec(v_unused_406_);
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_405_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_toZero_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_405_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v_toFun_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_398_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2, &lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2);
v_toFun_399_ = lean_ctor_get(v___x_398_, 0);
v___x_400_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__3, &lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__3_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__3);
lean_inc(v_toFun_399_);
v___x_401_ = lean_apply_1(v_toFun_399_, v_toZero_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_401_);
lean_ctor_set(v___x_396_, 0, v___x_400_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___boxed(lean_object* v_D_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm(v_D_407_);
lean_dec_ref(v_D_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_detId_spec__0(lean_object* v___x_409_, lean_object* v_s_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_detId_spec__0___boxed(lean_object* v___x_412_, lean_object* v_s_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = lp_tree_Submodule_span___at___00Formalism_MainNotions_TaylorLogMetric_detId_spec__0(v___x_412_, v_s_413_);
lean_dec_ref(v___x_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___redArg(lean_object* v_D_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___redArg___boxed(lean_object* v_D_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___redArg(v_D_417_);
lean_dec_ref(v_D_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId(lean_object* v_D_419_, lean_object* v_N_420_, lean_object* v_L_421_, lean_object* v_L_x27_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_box(0);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_detId___boxed(lean_object* v_D_424_, lean_object* v_N_425_, lean_object* v_L_426_, lean_object* v_L_x27_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_detId(v_D_424_, v_N_425_, v_L_426_, v_L_x27_427_);
lean_dec(v_N_425_);
lean_dec_ref(v_D_424_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__0(lean_object* v___x_429_, lean_object* v___x_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__0___boxed(lean_object* v___x_432_, lean_object* v___x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = lp_tree_integralClosure___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__0(v___x_432_, v___x_433_);
lean_dec_ref(v___x_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__1(lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_inst_437_, lean_object* v_s_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_box(0);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__1___boxed(lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v_inst_442_, lean_object* v_s_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = lp_tree_Subsemiring_ofClass___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__1(v___x_440_, v___x_441_, v_inst_442_, v_s_443_);
lean_dec_ref(v___x_440_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___lam__0(lean_object* v_self_445_){
_start:
{
lean_inc(v_self_445_);
return v_self_445_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___lam__0___boxed(lean_object* v_self_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___lam__0(v_self_446_);
lean_dec(v_self_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2(lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_s_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = ((lean_object*)(lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___closed__0));
return v___f_452_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___boxed(lean_object* v___x_453_, lean_object* v___x_454_, lean_object* v_s_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2(v___x_453_, v___x_454_, v_s_455_);
lean_dec_ref(v___x_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__3(lean_object* v___x_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_instField_459_; lean_object* v___x_460_; lean_object* v_toRing_461_; lean_object* v___x_462_; lean_object* v_toAddMonoidWithOne_463_; lean_object* v_toNatCast_464_; lean_object* v___x_465_; 
v_instField_459_ = lean_ctor_get(v___x_457_, 3);
lean_inc_ref(v_instField_459_);
lean_dec_ref(v___x_457_);
v___x_460_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_459_);
v_toRing_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_toRing_461_);
lean_dec_ref(v___x_460_);
v___x_462_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_461_);
v_toAddMonoidWithOne_463_ = lean_ctor_get(v___x_462_, 1);
lean_inc_ref(v_toAddMonoidWithOne_463_);
lean_dec_ref(v___x_462_);
v_toNatCast_464_ = lean_ctor_get(v_toAddMonoidWithOne_463_, 0);
lean_inc(v_toNatCast_464_);
lean_dec_ref(v_toAddMonoidWithOne_463_);
v___x_465_ = lean_apply_1(v_toNatCast_464_, v_a_458_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__0(lean_object* v_y_466_, lean_object* v_toHostAx_467_, lean_object* v_b_468_, lean_object* v_toMul_469_, lean_object* v_i_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc(v_i_470_);
v___x_473_ = lean_apply_1(v_y_466_, v_i_470_);
v___x_474_ = lp_tree_Nat_cast___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__3(v_toHostAx_467_, v___x_473_);
v___x_475_ = lean_apply_3(v_b_468_, v_i_470_, v___y_471_, v___y_472_);
v___x_476_ = lean_apply_2(v_toMul_469_, v___x_474_, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__1(lean_object* v_toZero_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_inc(v_toZero_477_);
return v_toZero_477_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__1___boxed(lean_object* v_toZero_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__1(v_toZero_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec(v___y_481_);
lean_dec(v_toZero_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__0(lean_object* v_toAddCommMonoid_484_, lean_object* v_x1_485_, lean_object* v_x2_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_toAddSemigroup_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_toAddSemigroup_489_ = lean_ctor_get(v_toAddCommMonoid_484_, 0);
lean_inc(v_toAddSemigroup_489_);
lean_dec_ref(v_toAddCommMonoid_484_);
lean_inc(v___y_488_);
lean_inc(v___y_487_);
v___x_490_ = lean_apply_2(v_x1_485_, v___y_487_, v___y_488_);
v___x_491_ = lean_apply_2(v_x2_486_, v___y_487_, v___y_488_);
v___x_492_ = lean_apply_2(v_toAddSemigroup_489_, v___x_490_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4(lean_object* v___x_493_, lean_object* v_s_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_instField_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_toSemiring_500_; lean_object* v_toAddCommMonoid_501_; lean_object* v___x_502_; lean_object* v_toZero_503_; lean_object* v___f_504_; lean_object* v___f_505_; lean_object* v___x_1489__overap_506_; lean_object* v___x_507_; 
v_instField_497_ = lean_ctor_get(v___x_493_, 3);
v___x_498_ = lp_mathlib_Field_toSemifield___redArg(v_instField_497_);
v___x_499_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_498_);
v_toSemiring_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc_ref(v_toSemiring_500_);
lean_dec_ref(v___x_499_);
v_toAddCommMonoid_501_ = lean_ctor_get(v_toSemiring_500_, 0);
lean_inc_ref(v_toAddCommMonoid_501_);
lean_dec_ref(v_toSemiring_500_);
v___x_502_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_501_);
v_toZero_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_toZero_503_);
lean_dec_ref(v___x_502_);
v___f_504_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__0), 5, 1);
lean_closure_set(v___f_504_, 0, v_toAddCommMonoid_501_);
v___f_505_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___lam__1___boxed), 3, 1);
lean_closure_set(v___f_505_, 0, v_toZero_503_);
v___x_1489__overap_506_ = l_List_foldrTR___redArg(v___f_504_, v___f_505_, v_s_494_);
v___x_507_ = lean_apply_2(v___x_1489__overap_506_, v___y_495_, v___y_496_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4___boxed(lean_object* v___x_508_, lean_object* v_s_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4(v___x_508_, v_s_509_, v___y_510_, v___y_511_);
lean_dec_ref(v___x_508_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg(lean_object* v___x_513_, lean_object* v_s_514_, lean_object* v_f_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lp_mathlib_Multiset_map___redArg(v_f_515_, v_s_514_);
v___x_519_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4_spec__4(v___x_513_, v___x_518_, v___y_516_, v___y_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg___boxed(lean_object* v___x_520_, lean_object* v_s_521_, lean_object* v_f_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg(v___x_520_, v_s_521_, v_f_522_, v___y_523_, v___y_524_);
lean_dec_ref(v___x_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__1(lean_object* v_toHostAx_526_, lean_object* v___x_527_, lean_object* v___f_528_, lean_object* v_toMul_529_, lean_object* v___x_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg(v_toHostAx_526_, v___x_527_, v___f_528_, v___y_531_, v___y_532_);
v___x_534_ = lean_apply_2(v_toMul_529_, v___x_530_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__1___boxed(lean_object* v_toHostAx_535_, lean_object* v___x_536_, lean_object* v___f_537_, lean_object* v_toMul_538_, lean_object* v___x_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__1(v_toHostAx_535_, v___x_536_, v___f_537_, v_toMul_538_, v___x_539_, v___y_540_, v___y_541_);
lean_dec_ref(v_toHostAx_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg(lean_object* v_D_544_, lean_object* v_T_545_, lean_object* v_00_u03b4_546_, lean_object* v_r_547_, lean_object* v_p_548_, lean_object* v_n_549_, lean_object* v_00_u03b5_550_, lean_object* v_b_551_, lean_object* v_y_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_host_556_; lean_object* v_toHostAx_557_; lean_object* v_instField_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_toSemiring_561_; lean_object* v___x_562_; lean_object* v_toMul_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_toMonoid_566_; lean_object* v_toDiv_567_; lean_object* v_toNPow_568_; lean_object* v_re_569_; lean_object* v_im_570_; lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_host_556_ = lean_ctor_get(v_D_544_, 1);
lean_inc_ref(v_host_556_);
lean_dec_ref(v_D_544_);
v_toHostAx_557_ = lean_ctor_get(v_host_556_, 0);
lean_inc_ref_n(v_toHostAx_557_, 3);
lean_dec_ref(v_host_556_);
v_instField_558_ = lean_ctor_get(v_toHostAx_557_, 3);
v___x_559_ = lp_mathlib_Field_toSemifield___redArg(v_instField_558_);
v___x_560_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_559_);
v_toSemiring_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref_n(v_toSemiring_561_, 2);
lean_dec_ref(v___x_560_);
v___x_562_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_561_);
v_toMul_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_n(v_toMul_563_, 2);
lean_dec_ref(v___x_562_);
lean_inc_ref(v_instField_558_);
v___x_564_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_558_);
v___x_565_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_564_);
lean_dec_ref(v___x_564_);
v_toMonoid_566_ = lean_ctor_get(v_toSemiring_561_, 1);
lean_inc_ref(v_toMonoid_566_);
lean_dec_ref(v_toSemiring_561_);
v_toDiv_567_ = lean_ctor_get(v___x_565_, 2);
lean_inc(v_toDiv_567_);
lean_dec_ref(v___x_565_);
v_toNPow_568_ = lean_ctor_get(v_toMonoid_566_, 2);
lean_inc(v_toNPow_568_);
lean_dec_ref(v_toMonoid_566_);
v_re_569_ = lean_ctor_get(v_00_u03b4_546_, 0);
lean_inc(v_re_569_);
v_im_570_ = lean_ctor_get(v_00_u03b4_546_, 1);
lean_inc(v_im_570_);
lean_dec_ref(v_00_u03b4_546_);
v___f_571_ = ((lean_object*)(lp_tree_Subsemiring_subtype___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__2___closed__0));
v___f_572_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__0), 7, 4);
lean_closure_set(v___f_572_, 0, v_y_552_);
lean_closure_set(v___f_572_, 1, v_toHostAx_557_);
lean_closure_set(v___f_572_, 2, v_b_551_);
lean_closure_set(v___f_572_, 3, v_toMul_563_);
v___f_573_ = ((lean_object*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___closed__0));
v___x_574_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_571_, v___f_573_, v_00_u03b5_550_);
v___x_575_ = lp_tree_Nat_cast___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__3(v_toHostAx_557_, v_p_548_);
v___x_576_ = lean_apply_2(v_toNPow_568_, v_n_549_, v___x_575_);
v___x_577_ = lean_apply_2(v_toDiv_567_, v___x_574_, v___x_576_);
v___x_578_ = l_List_finRange(v_r_547_);
v___f_579_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_579_, 0, v_toHostAx_557_);
lean_closure_set(v___f_579_, 1, v___x_578_);
lean_closure_set(v___f_579_, 2, v___f_572_);
lean_closure_set(v___f_579_, 3, v_toMul_563_);
lean_closure_set(v___f_579_, 4, v___x_577_);
v___x_580_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(v_T_545_, v___f_579_, v_a_553_, v_a_554_, v_a_555_);
v___x_581_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_569_, v_im_570_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY(lean_object* v_D_582_, lean_object* v_T_583_, lean_object* v_00_u03b4_584_, lean_object* v_N_585_, lean_object* v_N_x27_586_, lean_object* v_r_587_, lean_object* v_p_588_, lean_object* v_n_589_, lean_object* v_00_u03b5_590_, lean_object* v_b_591_, lean_object* v_y_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___redArg(v_D_582_, v_T_583_, v_00_u03b4_584_, v_r_587_, v_p_588_, v_n_589_, v_00_u03b5_590_, v_b_591_, v_y_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY___boxed(lean_object* v_D_597_, lean_object* v_T_598_, lean_object* v_00_u03b4_599_, lean_object* v_N_600_, lean_object* v_N_x27_601_, lean_object* v_r_602_, lean_object* v_p_603_, lean_object* v_n_604_, lean_object* v_00_u03b5_605_, lean_object* v_b_606_, lean_object* v_y_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_liftY(v_D_597_, v_T_598_, v_00_u03b4_599_, v_N_600_, v_N_x27_601_, v_r_602_, v_p_603_, v_n_604_, v_00_u03b5_605_, v_b_606_, v_y_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_N_x27_601_);
lean_dec(v_N_600_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4(lean_object* v___x_612_, lean_object* v_00_u03b9_613_, lean_object* v_s_614_, lean_object* v_f_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___redArg(v___x_612_, v_s_614_, v_f_615_, v___y_616_, v___y_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___boxed(lean_object* v___x_619_, lean_object* v_00_u03b9_620_, lean_object* v_s_621_, lean_object* v_f_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4(v___x_619_, v_00_u03b9_620_, v_s_621_, v_f_622_, v___y_623_, v___y_624_);
lean_dec_ref(v___x_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___redArg___lam__0(lean_object* v_a_626_, lean_object* v_toHostAx_627_, lean_object* v_b_628_, lean_object* v_toMul_629_, lean_object* v_i_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_inc(v_i_630_);
v___x_633_ = lean_apply_1(v_a_626_, v_i_630_);
v___x_634_ = lp_tree_Nat_cast___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__3(v_toHostAx_627_, v___x_633_);
v___x_635_ = lean_apply_3(v_b_628_, v_i_630_, v___y_631_, v___y_632_);
v___x_636_ = lean_apply_2(v_toMul_629_, v___x_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___redArg(lean_object* v_D_637_, lean_object* v_T_638_, lean_object* v_00_u03b4_639_, lean_object* v_r_640_, lean_object* v_b_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_host_646_; lean_object* v_toHostAx_647_; lean_object* v_instField_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_toSemiring_651_; lean_object* v___x_652_; lean_object* v_toMul_653_; lean_object* v_re_654_; lean_object* v_im_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_host_646_ = lean_ctor_get(v_D_637_, 1);
lean_inc_ref(v_host_646_);
lean_dec_ref(v_D_637_);
v_toHostAx_647_ = lean_ctor_get(v_host_646_, 0);
lean_inc_ref_n(v_toHostAx_647_, 2);
lean_dec_ref(v_host_646_);
v_instField_648_ = lean_ctor_get(v_toHostAx_647_, 3);
v___x_649_ = lp_mathlib_Field_toSemifield___redArg(v_instField_648_);
v___x_650_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_649_);
v_toSemiring_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_toSemiring_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_651_);
v_toMul_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_toMul_653_);
lean_dec_ref(v___x_652_);
v_re_654_ = lean_ctor_get(v_00_u03b4_639_, 0);
lean_inc(v_re_654_);
v_im_655_ = lean_ctor_get(v_00_u03b4_639_, 1);
lean_inc(v_im_655_);
lean_dec_ref(v_00_u03b4_639_);
v___x_656_ = l_List_finRange(v_r_640_);
v___f_657_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___redArg___lam__0), 7, 4);
lean_closure_set(v___f_657_, 0, v_a_642_);
lean_closure_set(v___f_657_, 1, v_toHostAx_647_);
lean_closure_set(v___f_657_, 2, v_b_641_);
lean_closure_set(v___f_657_, 3, v_toMul_653_);
v___x_658_ = lean_alloc_closure((void*)(lp_tree_Finset_sum___at___00Formalism_MainNotions_TaylorLogMetric_liftY_spec__4___boxed), 6, 4);
lean_closure_set(v___x_658_, 0, v_toHostAx_647_);
lean_closure_set(v___x_658_, 1, lean_box(0));
lean_closure_set(v___x_658_, 2, v___x_656_);
lean_closure_set(v___x_658_, 3, v___f_657_);
v___x_659_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_embV___redArg(v_T_638_, v___x_658_, v_a_643_, v_a_644_, v_a_645_);
v___x_660_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_654_, v_im_655_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN(lean_object* v_D_661_, lean_object* v_T_662_, lean_object* v_00_u03b4_663_, lean_object* v_N_664_, lean_object* v_N_x27_665_, lean_object* v_r_666_, lean_object* v_p_667_, lean_object* v_n_668_, lean_object* v_b_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___redArg(v_D_661_, v_T_662_, v_00_u03b4_663_, v_r_666_, v_b_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN___boxed(lean_object* v_D_675_, lean_object* v_T_676_, lean_object* v_00_u03b4_677_, lean_object* v_N_678_, lean_object* v_N_x27_679_, lean_object* v_r_680_, lean_object* v_p_681_, lean_object* v_n_682_, lean_object* v_b_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_vecN(v_D_675_, v_T_676_, v_00_u03b4_677_, v_N_678_, v_N_x27_679_, v_r_680_, v_p_681_, v_n_682_, v_b_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_n_682_);
lean_dec(v_p_681_);
lean_dec(v_N_x27_679_);
lean_dec(v_N_678_);
return v_res_688_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__0(void){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lp_mathlib_Additive_ofMul(lean_box(0));
return v___x_689_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__1(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lp_mathlib_Additive_toMul(lean_box(0));
return v___x_690_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__2(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_691_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG(lean_object* v_D_692_, lean_object* v_00_u03c6_693_, lean_object* v_d_694_, lean_object* v_00_u03c40_695_, lean_object* v_s_696_){
_start:
{
lean_object* v_R_697_; lean_object* v_toFrame_698_; lean_object* v_grp_699_; lean_object* v_toAddMonoid_700_; lean_object* v_eTau_701_; lean_object* v_fst_702_; lean_object* v_toAddSemigroup_703_; lean_object* v_toNSMul_704_; lean_object* v_toFun_705_; lean_object* v_snd_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; lean_object* v___x_709_; lean_object* v_toFun_710_; lean_object* v___x_711_; lean_object* v_toFun_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_val_715_; lean_object* v_inv_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_800_; 
v_R_697_ = lean_ctor_get(v_D_692_, 0);
v_toFrame_698_ = lean_ctor_get(v_R_697_, 0);
v_grp_699_ = lean_ctor_get(v_toFrame_698_, 2);
v_toAddMonoid_700_ = lean_ctor_get(v_grp_699_, 0);
lean_inc_ref(v_toAddMonoid_700_);
v_eTau_701_ = lean_ctor_get(v_D_692_, 5);
lean_inc_ref(v_eTau_701_);
lean_dec_ref(v_D_692_);
v_fst_702_ = lean_ctor_get(v_00_u03c6_693_, 0);
lean_inc(v_fst_702_);
v_toAddSemigroup_703_ = lean_ctor_get(v_toAddMonoid_700_, 0);
lean_inc(v_toAddSemigroup_703_);
v_toNSMul_704_ = lean_ctor_get(v_toAddMonoid_700_, 2);
lean_inc(v_toNSMul_704_);
lean_dec_ref(v_toAddMonoid_700_);
v_toFun_705_ = lean_ctor_get(v_eTau_701_, 0);
lean_inc(v_toFun_705_);
lean_dec_ref(v_eTau_701_);
v_snd_706_ = lean_ctor_get(v_00_u03c6_693_, 1);
lean_inc(v_snd_706_);
lean_dec_ref(v_00_u03c6_693_);
v_fst_707_ = lean_ctor_get(v_fst_702_, 0);
lean_inc(v_fst_707_);
v_snd_708_ = lean_ctor_get(v_fst_702_, 1);
lean_inc(v_snd_708_);
lean_dec(v_fst_702_);
v___x_709_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__0, &lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__0_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__0);
v_toFun_710_ = lean_ctor_get(v___x_709_, 0);
v___x_711_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__1, &lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__1_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__1);
v_toFun_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_toFun_710_);
v___x_713_ = lean_apply_1(v_toFun_710_, v_fst_707_);
lean_inc(v_toFun_712_);
v___x_714_ = lean_apply_1(v_toFun_712_, v___x_713_);
v_val_715_ = lean_ctor_get(v___x_714_, 0);
v_inv_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_800_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_800_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_inv_716_);
lean_inc(v_val_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_800_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_720_ = lp_mathlib_ZMod_val(v_d_694_, v_s_696_);
v___x_721_ = l_Int_pow(v_val_715_, v___x_720_);
lean_dec(v_val_715_);
v___x_722_ = l_Int_pow(v_inv_716_, v___x_720_);
lean_dec(v_inv_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_722_);
lean_ctor_set(v___x_718_, 0, v___x_721_);
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_799_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_val_729_; lean_object* v_inv_730_; lean_object* v___x_731_; lean_object* v_toFun_732_; lean_object* v___x_733_; lean_object* v_toFun_734_; lean_object* v___x_735_; lean_object* v_fst_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_798_; 
lean_inc_n(v_toFun_710_, 2);
v___x_725_ = lean_apply_1(v_toFun_710_, v___x_724_);
lean_inc_n(v_toFun_712_, 2);
v___x_726_ = lean_apply_1(v_toFun_712_, v___x_725_);
v___x_727_ = lean_apply_1(v_toFun_710_, v_snd_708_);
v___x_728_ = lean_apply_1(v_toFun_712_, v___x_727_);
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
v_inv_730_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_inv_730_);
lean_dec_ref(v___x_728_);
v___x_731_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__2, &lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__2_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___closed__2);
v_toFun_732_ = lean_ctor_get(v___x_731_, 0);
v___x_733_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2, &lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2_once, _init_lp_tree_Formalism_MainNotions_TaylorLogMetric_sgm___closed__2);
v_toFun_734_ = lean_ctor_get(v___x_733_, 0);
v___x_735_ = lean_apply_1(v_toFun_705_, v_00_u03c40_695_);
v_fst_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_fst_736_);
v_fst_737_ = lean_ctor_get(v_fst_736_, 0);
v_snd_738_ = lean_ctor_get(v_fst_736_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_fst_736_);
if (v_isSharedCheck_798_ == 0)
{
v___x_740_ = v_fst_736_;
v_isShared_741_ = v_isSharedCheck_798_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_inc(v_fst_737_);
lean_dec(v_fst_736_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_798_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_796_; 
v_snd_742_ = lean_ctor_get(v___x_735_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_735_, 0);
lean_dec(v_unused_797_);
v___x_744_ = v___x_735_;
v_isShared_745_ = v_isSharedCheck_796_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_dec(v___x_735_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_796_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_val_746_; lean_object* v_inv_747_; lean_object* v_val_748_; lean_object* v_inv_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_795_; 
v_val_746_ = lean_ctor_get(v_fst_737_, 0);
lean_inc(v_val_746_);
v_inv_747_ = lean_ctor_get(v_fst_737_, 1);
lean_inc(v_inv_747_);
lean_dec(v_fst_737_);
v_val_748_ = lean_ctor_get(v___x_726_, 0);
v_inv_749_ = lean_ctor_get(v___x_726_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_795_ == 0)
{
v___x_751_ = v___x_726_;
v_isShared_752_ = v_isSharedCheck_795_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_inv_749_);
lean_inc(v_val_748_);
lean_dec(v___x_726_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_795_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_val_753_; lean_object* v_inv_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_794_; 
v_val_753_ = lean_ctor_get(v_snd_738_, 0);
v_inv_754_ = lean_ctor_get(v_snd_738_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_snd_738_);
if (v_isSharedCheck_794_ == 0)
{
v___x_756_ = v_snd_738_;
v_isShared_757_ = v_isSharedCheck_794_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_inv_754_);
lean_inc(v_val_753_);
lean_dec(v_snd_738_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_794_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = l_Int_pow(v_val_729_, v___x_720_);
lean_dec(v_val_729_);
v___x_759_ = l_Int_pow(v_inv_730_, v___x_720_);
lean_dec(v_inv_730_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v___x_759_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_761_ = v___x_756_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_793_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_val_764_; lean_object* v_inv_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_792_; 
lean_inc(v_toFun_710_);
v___x_762_ = lean_apply_1(v_toFun_710_, v___x_761_);
lean_inc(v_toFun_712_);
v___x_763_ = lean_apply_1(v_toFun_712_, v___x_762_);
v_val_764_ = lean_ctor_get(v___x_763_, 0);
v_inv_765_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_792_ == 0)
{
v___x_767_ = v___x_763_;
v_isShared_768_ = v_isSharedCheck_792_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_inv_765_);
lean_inc(v_val_764_);
lean_dec(v___x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_792_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_inc(v_toFun_732_);
v___x_769_ = lean_apply_1(v_toFun_732_, v_snd_706_);
v___x_770_ = lean_apply_2(v_toNSMul_704_, v___x_720_, v___x_769_);
lean_inc(v_toFun_734_);
v___x_771_ = lean_apply_1(v_toFun_734_, v___x_770_);
v___x_772_ = lean_int_mul(v_val_746_, v_val_748_);
lean_dec(v_val_748_);
lean_dec(v_val_746_);
v___x_773_ = lean_int_mul(v_inv_749_, v_inv_747_);
lean_dec(v_inv_747_);
lean_dec(v_inv_749_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_773_);
lean_ctor_set(v___x_767_, 0, v___x_772_);
v___x_775_ = v___x_767_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_791_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_776_ = lean_int_mul(v_val_753_, v_val_764_);
lean_dec(v_val_764_);
lean_dec(v_val_753_);
v___x_777_ = lean_int_mul(v_inv_765_, v_inv_754_);
lean_dec(v_inv_754_);
lean_dec(v_inv_765_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_777_);
lean_ctor_set(v___x_751_, 0, v___x_776_);
v___x_779_ = v___x_751_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_790_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_779_);
lean_ctor_set(v___x_740_, 0, v___x_775_);
v___x_781_ = v___x_740_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_789_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_inc_n(v_toFun_732_, 2);
v___x_782_ = lean_apply_1(v_toFun_732_, v_snd_742_);
v___x_783_ = lean_apply_1(v_toFun_732_, v___x_771_);
v___x_784_ = lean_apply_2(v_toAddSemigroup_703_, v___x_782_, v___x_783_);
lean_inc(v_toFun_734_);
v___x_785_ = lean_apply_1(v_toFun_734_, v___x_784_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_785_);
lean_ctor_set(v___x_744_, 0, v___x_781_);
v___x_787_ = v___x_744_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TaylorLogMetric_posG___boxed(lean_object* v_D_801_, lean_object* v_00_u03c6_802_, lean_object* v_d_803_, lean_object* v_00_u03c40_804_, lean_object* v_s_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = lp_tree_Formalism_MainNotions_TaylorLogMetric_posG(v_D_801_, v_00_u03c6_802_, v_d_803_, v_00_u03c40_804_, v_s_805_);
lean_dec(v_s_805_);
lean_dec(v_d_803_);
return v_res_806_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_IsDiscriminantTwelfthRootOfIdealLattice(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
