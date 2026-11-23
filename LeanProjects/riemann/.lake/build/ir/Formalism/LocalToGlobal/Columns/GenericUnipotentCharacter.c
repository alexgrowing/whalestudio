// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.Tuples public import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_toGroup___redArg(lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_det(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toBlock___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_toHomUnits___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_instCommMonoid___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_inclusion___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_divInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_negAddMonoidHom___redArg(lean_object*);
lean_object* lp_mathlib_AddChar_compAddMonoidHom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_ring___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_coarse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_coarse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter_0__Formalism_L2_Col_blkIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter_0__Formalism_L2_Col_blkIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_btG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_btG___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_blkHom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_blkHom___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_blkHom___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_blkHom___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_blkDet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkDet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_blkDet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_blkDet___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_blkDet___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkDet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkDet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockUT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockUT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uniUT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uniUT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supChar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_inclusion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagEmb___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagEmb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fixCol(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fixCol___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_restr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_restr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_restr___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_restr___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HU(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HU___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HX___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_SX___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SX___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SX(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HVsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HVsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKJ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_SPsym___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SPsym___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SPsym(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SPsym___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UpperUnipotentProduct(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UpperUnipotentProduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkIdx(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(0u);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_head_4_ = lean_ctor_get(v_x_1_, 0);
v_tail_5_ = lean_ctor_get(v_x_1_, 1);
v___x_6_ = lean_nat_dec_lt(v_x_2_, v_head_4_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_nat_sub(v_x_2_, v_head_4_);
v___x_8_ = lp_tree_Formalism_L2_Col_blkIdx(v_tail_5_, v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_add(v___x_8_, v___x_9_);
lean_dec(v___x_8_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(0u);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkIdx___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_L2_Col_blkIdx(v_x_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec(v_x_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_coarse(lean_object* v_a_15_, lean_object* v_bl_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v_a_15_);
lean_ctor_set(v___x_18_, 1, v_bl_16_);
v___x_19_ = lp_tree_Formalism_L2_Col_blkIdx(v___x_18_, v_i_17_);
lean_dec_ref_known(v___x_18_, 2);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_coarse___boxed(lean_object* v_a_20_, lean_object* v_bl_21_, lean_object* v_i_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_Col_coarse(v_a_20_, v_bl_21_, v_i_22_);
lean_dec(v_i_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fine(lean_object* v_a_24_, lean_object* v_bl_25_, lean_object* v_i_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_lt(v_i_26_, v_a_24_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_nat_sub(v_i_26_, v_a_24_);
v___x_29_ = lp_tree_Formalism_L2_Col_blkIdx(v_bl_25_, v___x_28_);
lean_dec(v___x_28_);
v___x_30_ = lean_nat_add(v_a_24_, v___x_29_);
lean_dec(v___x_29_);
return v___x_30_;
}
else
{
lean_inc(v_i_26_);
return v_i_26_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fine___boxed(lean_object* v_a_31_, lean_object* v_bl_32_, lean_object* v_i_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_L2_Col_fine(v_a_31_, v_bl_32_, v_i_33_);
lean_dec(v_i_33_);
lean_dec(v_bl_32_);
lean_dec(v_a_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter_0__Formalism_L2_Col_blkIdx_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_object* v___x_39_; 
lean_dec(v_h__2_38_);
v___x_39_ = lean_apply_1(v_h__1_37_, v_x_36_);
return v___x_39_;
}
else
{
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___x_42_; 
lean_dec(v_h__1_37_);
v_head_40_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_head_40_);
v_tail_41_ = lean_ctor_get(v_x_35_, 1);
lean_inc(v_tail_41_);
lean_dec_ref_known(v_x_35_, 2);
v___x_42_ = lean_apply_3(v_h__2_38_, v_head_40_, v_tail_41_, v_x_36_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter_0__Formalism_L2_Col_blkIdx_match__1_splitter(lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_48_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_apply_1(v_h__1_46_, v_x_45_);
return v___x_48_;
}
else
{
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v_head_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_head_49_);
v_tail_50_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_tail_50_);
lean_dec_ref_known(v_x_44_, 2);
v___x_51_ = lean_apply_3(v_h__2_47_, v_head_49_, v_tail_50_, v_x_45_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_btG(lean_object* v_n_52_, lean_object* v_00_u03ba_53_, lean_object* v_inst_54_, lean_object* v_00_u03b2_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_btG___boxed(lean_object* v_n_57_, lean_object* v_00_u03ba_58_, lean_object* v_inst_59_, lean_object* v_00_u03b2_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_Col_btG(v_n_57_, v_00_u03ba_58_, v_inst_59_, v_00_u03b2_60_);
lean_dec_ref(v_00_u03b2_60_);
lean_dec_ref(v_inst_59_);
lean_dec(v_n_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___lam__0(lean_object* v_M_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_val_65_; lean_object* v___x_66_; 
v_val_65_ = lean_ctor_get(v_M_62_, 0);
lean_inc(v_val_65_);
lean_dec_ref(v_M_62_);
v___x_66_ = lp_mathlib_Matrix_toBlock___redArg(v_val_65_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom(lean_object* v_n_68_, lean_object* v_00_u03ba_69_, lean_object* v_inst_70_, lean_object* v_00_u03b2_71_, lean_object* v_c_72_){
_start:
{
lean_object* v___f_73_; 
v___f_73_ = ((lean_object*)(lp_tree_Formalism_L2_Col_blkHom___closed__0));
return v___f_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___boxed(lean_object* v_n_74_, lean_object* v_00_u03ba_75_, lean_object* v_inst_76_, lean_object* v_00_u03b2_77_, lean_object* v_c_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Formalism_L2_Col_blkHom(v_n_74_, v_00_u03ba_75_, v_inst_76_, v_00_u03b2_77_, v_c_78_);
lean_dec(v_c_78_);
lean_dec_ref(v_00_u03b2_77_);
lean_dec_ref(v_inst_76_);
lean_dec(v_n_74_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_blkDet___redArg___lam__0(lean_object* v_00_u03b2_80_, lean_object* v_c_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_apply_1(v_00_u03b2_80_, v_a_82_);
v___x_84_ = lean_nat_dec_eq(v___x_83_, v_c_81_);
lean_dec(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkDet___redArg___lam__0___boxed(lean_object* v_00_u03b2_85_, lean_object* v_c_86_, lean_object* v_a_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = lp_tree_Formalism_L2_Col_blkDet___redArg___lam__0(v_00_u03b2_85_, v_c_86_, v_a_87_);
lean_dec(v_c_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkDet___redArg(lean_object* v_n_91_, lean_object* v_inst_92_, lean_object* v_00_u03b2_93_, lean_object* v_c_94_){
_start:
{
lean_object* v_toSemiring_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_toMonoid_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v_toSemiring_95_ = lean_ctor_get(v_inst_92_, 0);
lean_inc(v_n_91_);
v___x_96_ = l_List_finRange(v_n_91_);
v___x_97_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_97_, 0, v_n_91_);
lean_inc(v___x_96_);
lean_inc_ref(v_toSemiring_95_);
v___x_98_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_95_, v___x_96_, v___x_97_);
v_toMonoid_99_ = lean_ctor_get(v___x_98_, 1);
lean_inc_ref(v_toMonoid_99_);
lean_dec_ref(v___x_98_);
v___f_100_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blkDet___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_100_, 0, v_00_u03b2_93_);
lean_closure_set(v___f_100_, 1, v_c_94_);
v___f_101_ = ((lean_object*)(lp_tree_Formalism_L2_Col_blkDet___redArg___closed__0));
v___x_102_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_99_);
v___x_103_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_102_);
v___x_104_ = lp_mathlib_Subtype_fintype___redArg(v___f_100_, v___x_96_);
v___x_105_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_det), 6, 5);
lean_closure_set(v___x_105_, 0, lean_box(0));
lean_closure_set(v___x_105_, 1, v___f_101_);
lean_closure_set(v___x_105_, 2, v___x_104_);
lean_closure_set(v___x_105_, 3, lean_box(0));
lean_closure_set(v___x_105_, 4, v_inst_92_);
v___f_106_ = ((lean_object*)(lp_tree_Formalism_L2_Col_blkHom___closed__0));
v___f_107_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_107_, 0, v___f_106_);
lean_closure_set(v___f_107_, 1, v___x_105_);
v___x_108_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_103_, v___f_107_);
lean_dec_ref(v___x_103_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkDet(lean_object* v_n_109_, lean_object* v_00_u03ba_110_, lean_object* v_inst_111_, lean_object* v_00_u03b2_112_, lean_object* v_c_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lp_tree_Formalism_L2_Col_blkDet___redArg(v_n_109_, v_inst_111_, v_00_u03b2_112_, v_c_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockUT(lean_object* v_n_115_, lean_object* v_00_u03ba_116_, lean_object* v_inst_117_, lean_object* v_a_118_, lean_object* v_bl_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockUT___boxed(lean_object* v_n_121_, lean_object* v_00_u03ba_122_, lean_object* v_inst_123_, lean_object* v_a_124_, lean_object* v_bl_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_tree_Formalism_L2_Col_blockUT(v_n_121_, v_00_u03ba_122_, v_inst_123_, v_a_124_, v_bl_125_);
lean_dec(v_bl_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_inst_123_);
lean_dec(v_n_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uniUT(lean_object* v_n_127_, lean_object* v_00_u03ba_128_, lean_object* v_inst_129_, lean_object* v_a_130_, lean_object* v_bl_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_box(0);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_uniUT___boxed(lean_object* v_n_133_, lean_object* v_00_u03ba_134_, lean_object* v_inst_135_, lean_object* v_a_136_, lean_object* v_bl_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_tree_Formalism_L2_Col_uniUT(v_n_133_, v_00_u03ba_134_, v_inst_135_, v_a_136_, v_bl_137_);
lean_dec(v_bl_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_inst_135_);
lean_dec(v_n_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__0(lean_object* v_toSemiring_139_, lean_object* v_i_140_, lean_object* v_a_141_, lean_object* v_S_142_, lean_object* v_M_143_, lean_object* v_j_144_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_i_140_, v___x_148_);
v___x_150_ = lean_nat_dec_eq(v___x_149_, v_j_144_);
lean_dec(v___x_149_);
if (v___x_150_ == 0)
{
lean_dec(v_j_144_);
lean_dec(v_M_143_);
lean_dec(v_S_142_);
lean_dec(v_i_140_);
goto v___jp_145_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_lt(v_j_144_, v_a_141_);
if (v___x_151_ == 0)
{
lean_dec(v_j_144_);
lean_dec(v_M_143_);
lean_dec(v_S_142_);
lean_dec(v_i_140_);
goto v___jp_145_;
}
else
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc(v_i_140_);
v___x_153_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_152_, v_i_140_, v_S_142_);
if (v___x_153_ == 0)
{
lean_dec(v_j_144_);
lean_dec(v_M_143_);
lean_dec(v_i_140_);
goto v___jp_145_;
}
else
{
lean_object* v___x_154_; 
lean_dec_ref(v_toSemiring_139_);
v___x_154_ = lean_apply_2(v_M_143_, v_i_140_, v_j_144_);
return v___x_154_;
}
}
}
v___jp_145_:
{
lean_object* v___x_146_; lean_object* v_toZero_147_; 
v___x_146_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_139_);
v_toZero_147_ = lean_ctor_get(v___x_146_, 1);
lean_inc(v_toZero_147_);
lean_dec_ref(v___x_146_);
return v_toZero_147_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__0___boxed(lean_object* v_toSemiring_155_, lean_object* v_i_156_, lean_object* v_a_157_, lean_object* v_S_158_, lean_object* v_M_159_, lean_object* v_j_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_tree_Formalism_L2_Col_supSum___redArg___lam__0(v_toSemiring_155_, v_i_156_, v_a_157_, v_S_158_, v_M_159_, v_j_160_);
lean_dec(v_a_157_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__1(lean_object* v_toSemiring_162_, lean_object* v_a_163_, lean_object* v_S_164_, lean_object* v_M_165_, lean_object* v_toAddCommMonoid_166_, lean_object* v___x_167_, lean_object* v_i_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; 
v___f_169_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_supSum___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_169_, 0, v_toSemiring_162_);
lean_closure_set(v___f_169_, 1, v_i_168_);
lean_closure_set(v___f_169_, 2, v_a_163_);
lean_closure_set(v___f_169_, 3, v_S_164_);
lean_closure_set(v___f_169_, 4, v_M_165_);
v___x_170_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_166_, v___x_167_, v___f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg___lam__1___boxed(lean_object* v_toSemiring_171_, lean_object* v_a_172_, lean_object* v_S_173_, lean_object* v_M_174_, lean_object* v_toAddCommMonoid_175_, lean_object* v___x_176_, lean_object* v_i_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_tree_Formalism_L2_Col_supSum___redArg___lam__1(v_toSemiring_171_, v_a_172_, v_S_173_, v_M_174_, v_toAddCommMonoid_175_, v___x_176_, v_i_177_);
lean_dec_ref(v_toAddCommMonoid_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum___redArg(lean_object* v_n_179_, lean_object* v_inst_180_, lean_object* v_a_181_, lean_object* v_S_182_, lean_object* v_M_183_){
_start:
{
lean_object* v_toSemiring_184_; lean_object* v_toAddCommMonoid_185_; lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___x_188_; 
v_toSemiring_184_ = lean_ctor_get(v_inst_180_, 0);
lean_inc_ref(v_toSemiring_184_);
lean_dec_ref(v_inst_180_);
v_toAddCommMonoid_185_ = lean_ctor_get(v_toSemiring_184_, 0);
lean_inc_ref_n(v_toAddCommMonoid_185_, 2);
v___x_186_ = l_List_finRange(v_n_179_);
lean_inc(v___x_186_);
v___f_187_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_supSum___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_187_, 0, v_toSemiring_184_);
lean_closure_set(v___f_187_, 1, v_a_181_);
lean_closure_set(v___f_187_, 2, v_S_182_);
lean_closure_set(v___f_187_, 3, v_M_183_);
lean_closure_set(v___f_187_, 4, v_toAddCommMonoid_185_);
lean_closure_set(v___f_187_, 5, v___x_186_);
v___x_188_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_185_, v___x_186_, v___f_187_);
lean_dec_ref(v_toAddCommMonoid_185_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supSum(lean_object* v_n_189_, lean_object* v_00_u03ba_190_, lean_object* v_inst_191_, lean_object* v_a_192_, lean_object* v_S_193_, lean_object* v_M_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lp_tree_Formalism_L2_Col_supSum___redArg(v_n_189_, v_inst_191_, v_a_192_, v_S_193_, v_M_194_);
return v___x_195_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom___redArg___lam__0(lean_object* v_n_197_, lean_object* v_inst_198_, lean_object* v_a_199_, lean_object* v_S_200_, lean_object* v_M_201_){
_start:
{
lean_object* v_val_202_; lean_object* v___x_203_; lean_object* v_toFun_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_val_202_ = lean_ctor_get(v_M_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref(v_M_201_);
v___x_203_ = lean_obj_once(&lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0);
v_toFun_204_ = lean_ctor_get(v___x_203_, 0);
v___x_205_ = lp_tree_Formalism_L2_Col_supSum___redArg(v_n_197_, v_inst_198_, v_a_199_, v_S_200_, v_val_202_);
lean_inc(v_toFun_204_);
v___x_206_ = lean_apply_1(v_toFun_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom___redArg(lean_object* v_n_207_, lean_object* v_inst_208_, lean_object* v_a_209_, lean_object* v_S_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_supHom___redArg___lam__0), 5, 4);
lean_closure_set(v___f_211_, 0, v_n_207_);
lean_closure_set(v___f_211_, 1, v_inst_208_);
lean_closure_set(v___f_211_, 2, v_a_209_);
lean_closure_set(v___f_211_, 3, v_S_210_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom(lean_object* v_n_212_, lean_object* v_00_u03ba_213_, lean_object* v_inst_214_, lean_object* v_a_215_, lean_object* v_bl_216_, lean_object* v_S_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_supHom___redArg___lam__0), 5, 4);
lean_closure_set(v___f_218_, 0, v_n_212_);
lean_closure_set(v___f_218_, 1, v_inst_214_);
lean_closure_set(v___f_218_, 2, v_a_215_);
lean_closure_set(v___f_218_, 3, v_S_217_);
return v___f_218_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supHom___boxed(lean_object* v_n_219_, lean_object* v_00_u03ba_220_, lean_object* v_inst_221_, lean_object* v_a_222_, lean_object* v_bl_223_, lean_object* v_S_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = lp_tree_Formalism_L2_Col_supHom(v_n_219_, v_00_u03ba_220_, v_inst_221_, v_a_222_, v_bl_223_, v_S_224_);
lean_dec(v_bl_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supChar___redArg(lean_object* v_inst_226_, lean_object* v_00_u03c8_227_, lean_object* v_n_228_, lean_object* v_a_229_, lean_object* v_S_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___f_236_; 
lean_inc_ref(v_inst_226_);
v___x_231_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_226_);
v___x_232_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = lp_mathlib_Multiplicative_divInvMonoid___redArg(v___x_232_);
v___x_234_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_233_, v_00_u03c8_227_);
lean_dec_ref(v___x_233_);
v___f_235_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_supHom___redArg___lam__0), 5, 4);
lean_closure_set(v___f_235_, 0, v_n_228_);
lean_closure_set(v___f_235_, 1, v_inst_226_);
lean_closure_set(v___f_235_, 2, v_a_229_);
lean_closure_set(v___f_235_, 3, v_S_230_);
v___f_236_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_236_, 0, v___f_235_);
lean_closure_set(v___f_236_, 1, v___x_234_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supChar(lean_object* v_00_u03ba_237_, lean_object* v_inst_238_, lean_object* v_K_239_, lean_object* v_inst_240_, lean_object* v_00_u03c8_241_, lean_object* v_n_242_, lean_object* v_a_243_, lean_object* v_bl_244_, lean_object* v_S_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lp_tree_Formalism_L2_Col_supChar___redArg(v_inst_238_, v_00_u03c8_241_, v_n_242_, v_a_243_, v_S_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_supChar___boxed(lean_object* v_00_u03ba_247_, lean_object* v_inst_248_, lean_object* v_K_249_, lean_object* v_inst_250_, lean_object* v_00_u03c8_251_, lean_object* v_n_252_, lean_object* v_a_253_, lean_object* v_bl_254_, lean_object* v_S_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = lp_tree_Formalism_L2_Col_supChar(v_00_u03ba_247_, v_inst_248_, v_K_249_, v_inst_250_, v_00_u03c8_251_, v_n_252_, v_a_253_, v_bl_254_, v_S_255_);
lean_dec(v_bl_254_);
lean_dec_ref(v_inst_250_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___redArg___lam__0(lean_object* v_00_u03c7_257_, lean_object* v_n_258_, lean_object* v_inst_259_, lean_object* v___x_260_, lean_object* v_s_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc(v_s_261_);
v___x_263_ = lean_apply_1(v_00_u03c7_257_, v_s_261_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_s_261_, v___x_264_);
lean_dec(v_s_261_);
v___x_266_ = lp_tree_Formalism_L2_Col_blkDet___redArg(v_n_258_, v_inst_259_, v___x_260_, v___x_265_);
v___x_267_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___x_266_, v___x_263_, v___y_262_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_00_u03c7_270_, lean_object* v_n_271_, lean_object* v_a_272_, lean_object* v_bl_273_){
_start:
{
lean_object* v_toCommRing_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_toMonoid_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_toCommRing_274_ = lean_ctor_get(v_inst_269_, 0);
v___x_275_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_274_);
v___x_276_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_275_);
v_toMonoid_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref(v_toMonoid_277_);
lean_dec_ref(v___x_276_);
lean_inc(v_bl_273_);
v___x_278_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_coarse___boxed), 3, 2);
lean_closure_set(v___x_278_, 0, v_a_272_);
lean_closure_set(v___x_278_, 1, v_bl_273_);
v___f_279_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_detChar___redArg___lam__0), 6, 4);
lean_closure_set(v___f_279_, 0, v_00_u03c7_270_);
lean_closure_set(v___f_279_, 1, v_n_271_);
lean_closure_set(v___f_279_, 2, v_inst_268_);
lean_closure_set(v___f_279_, 3, v___x_278_);
v___x_280_ = lp_mathlib_MonoidHom_instCommMonoid___redArg(v_toMonoid_277_);
v___x_281_ = l_List_lengthTR___redArg(v_bl_273_);
lean_dec(v_bl_273_);
v___x_282_ = l_List_range(v___x_281_);
v___x_283_ = lp_mathlib_Finset_prod___redArg(v___x_280_, v___x_282_, v___f_279_);
lean_dec_ref(v___x_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___redArg___boxed(lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_00_u03c7_286_, lean_object* v_n_287_, lean_object* v_a_288_, lean_object* v_bl_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = lp_tree_Formalism_L2_Col_detChar___redArg(v_inst_284_, v_inst_285_, v_00_u03c7_286_, v_n_287_, v_a_288_, v_bl_289_);
lean_dec_ref(v_inst_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar(lean_object* v_00_u03ba_291_, lean_object* v_inst_292_, lean_object* v_K_293_, lean_object* v_inst_294_, lean_object* v_00_u03c7_295_, lean_object* v_n_296_, lean_object* v_a_297_, lean_object* v_bl_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lp_tree_Formalism_L2_Col_detChar___redArg(v_inst_292_, v_inst_294_, v_00_u03c7_295_, v_n_296_, v_a_297_, v_bl_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___boxed(lean_object* v_00_u03ba_300_, lean_object* v_inst_301_, lean_object* v_K_302_, lean_object* v_inst_303_, lean_object* v_00_u03c7_304_, lean_object* v_n_305_, lean_object* v_a_306_, lean_object* v_bl_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_tree_Formalism_L2_Col_detChar(v_00_u03ba_300_, v_inst_301_, v_K_302_, v_inst_303_, v_00_u03c7_304_, v_n_305_, v_a_306_, v_bl_307_);
lean_dec_ref(v_inst_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___lam__0(lean_object* v___x_309_, lean_object* v_inst_310_, lean_object* v_00_u03c8_311_, lean_object* v_n_312_, lean_object* v_a_313_, lean_object* v_S_314_, lean_object* v___f_315_, lean_object* v___x_316_, lean_object* v_m_317_){
_start:
{
lean_object* v___x_318_; lean_object* v_toMul_319_; lean_object* v___x_215__overap_320_; lean_object* v___x_321_; lean_object* v_val_322_; lean_object* v_inv_323_; lean_object* v___x_324_; lean_object* v_val_325_; lean_object* v_inv_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_335_; 
v___x_318_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_309_);
v_toMul_319_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_toMul_319_);
lean_dec_ref(v___x_318_);
v___x_215__overap_320_ = lp_tree_Formalism_L2_Col_supChar___redArg(v_inst_310_, v_00_u03c8_311_, v_n_312_, v_a_313_, v_S_314_);
lean_inc_ref(v_m_317_);
v___x_321_ = lean_apply_1(v___x_215__overap_320_, v_m_317_);
v_val_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_322_);
v_inv_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_inv_323_);
lean_dec_ref(v___x_321_);
v___x_324_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_315_, v___x_316_, v_m_317_);
v_val_325_ = lean_ctor_get(v___x_324_, 0);
v_inv_326_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_335_ == 0)
{
v___x_328_ = v___x_324_;
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_inv_326_);
lean_inc(v_val_325_);
lean_dec(v___x_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_inc(v_toMul_319_);
v___x_330_ = lean_apply_2(v_toMul_319_, v_val_322_, v_val_325_);
v___x_331_ = lean_apply_2(v_toMul_319_, v_inv_326_, v_inv_323_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_331_);
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___lam__0___boxed(lean_object* v___x_336_, lean_object* v_inst_337_, lean_object* v_00_u03c8_338_, lean_object* v_n_339_, lean_object* v_a_340_, lean_object* v_S_341_, lean_object* v___f_342_, lean_object* v___x_343_, lean_object* v_m_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = lp_tree_Formalism_L2_Col_lamGen___redArg___lam__0(v___x_336_, v_inst_337_, v_00_u03c8_338_, v_n_339_, v_a_340_, v_S_341_, v___f_342_, v___x_343_, v_m_344_);
lean_dec_ref(v___x_336_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_00_u03c8_349_, lean_object* v_00_u03c7_350_, lean_object* v_n_351_, lean_object* v_a_352_, lean_object* v_bl_353_, lean_object* v_S_354_){
_start:
{
lean_object* v_toCommRing_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___f_358_; lean_object* v___f_359_; 
v_toCommRing_355_ = lean_ctor_get(v_inst_348_, 0);
v___x_356_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_355_);
lean_inc(v_a_352_);
lean_inc(v_n_351_);
lean_inc_ref(v_inst_347_);
v___x_357_ = lp_tree_Formalism_L2_Col_detChar___redArg(v_inst_347_, v_inst_348_, v_00_u03c7_350_, v_n_351_, v_a_352_, v_bl_353_);
v___f_358_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_359_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_lamGen___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_359_, 0, v___x_356_);
lean_closure_set(v___f_359_, 1, v_inst_347_);
lean_closure_set(v___f_359_, 2, v_00_u03c8_349_);
lean_closure_set(v___f_359_, 3, v_n_351_);
lean_closure_set(v___f_359_, 4, v_a_352_);
lean_closure_set(v___f_359_, 5, v_S_354_);
lean_closure_set(v___f_359_, 6, v___f_358_);
lean_closure_set(v___f_359_, 7, v___x_357_);
return v___f_359_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___redArg___boxed(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_00_u03c8_362_, lean_object* v_00_u03c7_363_, lean_object* v_n_364_, lean_object* v_a_365_, lean_object* v_bl_366_, lean_object* v_S_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = lp_tree_Formalism_L2_Col_lamGen___redArg(v_inst_360_, v_inst_361_, v_00_u03c8_362_, v_00_u03c7_363_, v_n_364_, v_a_365_, v_bl_366_, v_S_367_);
lean_dec_ref(v_inst_361_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen(lean_object* v_00_u03ba_369_, lean_object* v_inst_370_, lean_object* v_K_371_, lean_object* v_inst_372_, lean_object* v_00_u03c8_373_, lean_object* v_00_u03c7_374_, lean_object* v_n_375_, lean_object* v_a_376_, lean_object* v_bl_377_, lean_object* v_S_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lp_tree_Formalism_L2_Col_lamGen___redArg(v_inst_370_, v_inst_372_, v_00_u03c8_373_, v_00_u03c7_374_, v_n_375_, v_a_376_, v_bl_377_, v_S_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamGen___boxed(lean_object* v_00_u03ba_380_, lean_object* v_inst_381_, lean_object* v_K_382_, lean_object* v_inst_383_, lean_object* v_00_u03c8_384_, lean_object* v_00_u03c7_385_, lean_object* v_n_386_, lean_object* v_a_387_, lean_object* v_bl_388_, lean_object* v_S_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = lp_tree_Formalism_L2_Col_lamGen(v_00_u03ba_380_, v_inst_381_, v_K_382_, v_inst_383_, v_00_u03c8_384_, v_00_u03c7_385_, v_n_386_, v_a_387_, v_bl_388_, v_S_389_);
lean_dec_ref(v_inst_383_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg___lam__0(lean_object* v_toMonoid_391_, lean_object* v_x_392_){
_start:
{
lean_object* v___x_393_; lean_object* v_toOne_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v___x_393_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_391_);
v_toOne_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v___x_393_, 1);
lean_dec(v_unused_402_);
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_toOne_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
lean_inc(v_toOne_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v_toOne_394_);
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_toOne_394_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_toOne_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg___lam__0___boxed(lean_object* v_toMonoid_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = lp_tree_Formalism_L2_Col_extChi___redArg___lam__0(v_toMonoid_403_, v_x_404_);
lean_dec_ref(v_x_404_);
lean_dec_ref(v_toMonoid_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg(lean_object* v_inst_406_, lean_object* v_m_407_, lean_object* v_00_u03c7_408_, lean_object* v_s_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_lt(v_s_409_, v_m_407_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_toSemiring_413_; lean_object* v_toMonoid_414_; lean_object* v___f_415_; 
lean_dec(v_s_409_);
lean_dec_ref(v_00_u03c7_408_);
v___x_411_ = lp_mathlib_Field_toSemifield___redArg(v_inst_406_);
v___x_412_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_411_);
v_toSemiring_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_toSemiring_413_);
lean_dec_ref(v___x_412_);
v_toMonoid_414_ = lean_ctor_get(v_toSemiring_413_, 1);
lean_inc_ref(v_toMonoid_414_);
lean_dec_ref(v_toSemiring_413_);
v___f_415_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extChi___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_415_, 0, v_toMonoid_414_);
return v___f_415_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_apply_1(v_00_u03c7_408_, v_s_409_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___redArg___boxed(lean_object* v_inst_417_, lean_object* v_m_418_, lean_object* v_00_u03c7_419_, lean_object* v_s_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = lp_tree_Formalism_L2_Col_extChi___redArg(v_inst_417_, v_m_418_, v_00_u03c7_419_, v_s_420_);
lean_dec(v_m_418_);
lean_dec_ref(v_inst_417_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi(lean_object* v_00_u03ba_422_, lean_object* v_inst_423_, lean_object* v_K_424_, lean_object* v_inst_425_, lean_object* v_m_426_, lean_object* v_00_u03c7_427_, lean_object* v_s_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lp_tree_Formalism_L2_Col_extChi___redArg(v_inst_425_, v_m_426_, v_00_u03c7_427_, v_s_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extChi___boxed(lean_object* v_00_u03ba_430_, lean_object* v_inst_431_, lean_object* v_K_432_, lean_object* v_inst_433_, lean_object* v_m_434_, lean_object* v_00_u03c7_435_, lean_object* v_s_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = lp_tree_Formalism_L2_Col_extChi(v_00_u03ba_430_, v_inst_431_, v_K_432_, v_inst_433_, v_m_434_, v_00_u03c7_435_, v_s_436_);
lean_dec(v_m_434_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_inst_431_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg___lam__0(lean_object* v_toOne_438_, lean_object* v_x_439_){
_start:
{
lean_inc(v_toOne_438_);
return v_toOne_438_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg___lam__0___boxed(lean_object* v_toOne_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = lp_tree_Formalism_L2_Col_diagMat___redArg___lam__0(v_toOne_440_, v_x_441_);
lean_dec(v_x_441_);
lean_dec(v_toOne_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg(lean_object* v_inst_443_, lean_object* v_r_444_, lean_object* v_n_445_, lean_object* v_g_446_, lean_object* v_i_447_, lean_object* v_j_448_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_nat_dec_lt(v_i_447_, v_r_444_);
if (v___x_459_ == 0)
{
lean_dec(v_g_446_);
goto v___jp_449_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_lt(v_j_448_, v_r_444_);
if (v___x_460_ == 0)
{
lean_dec(v_g_446_);
goto v___jp_449_;
}
else
{
lean_object* v___x_461_; 
lean_dec(v_n_445_);
lean_dec_ref(v_inst_443_);
v___x_461_ = lean_apply_2(v_g_446_, v_i_447_, v_j_448_);
return v___x_461_;
}
}
v___jp_449_:
{
lean_object* v_toSemiring_450_; lean_object* v___x_451_; lean_object* v_toZero_452_; lean_object* v___x_453_; lean_object* v_toAddMonoidWithOne_454_; lean_object* v_toOne_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_toSemiring_450_ = lean_ctor_get(v_inst_443_, 0);
lean_inc_ref(v_toSemiring_450_);
v___x_451_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_450_);
v_toZero_452_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_toZero_452_);
lean_dec_ref(v___x_451_);
v___x_453_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_443_);
v_toAddMonoidWithOne_454_ = lean_ctor_get(v___x_453_, 1);
lean_inc_ref(v_toAddMonoidWithOne_454_);
lean_dec_ref(v___x_453_);
v_toOne_455_ = lean_ctor_get(v_toAddMonoidWithOne_454_, 2);
lean_inc(v_toOne_455_);
lean_dec_ref(v_toAddMonoidWithOne_454_);
v___x_456_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_456_, 0, v_n_445_);
v___f_457_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_diagMat___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_457_, 0, v_toOne_455_);
v___x_458_ = lp_mathlib_Matrix_diagonal___redArg(v___x_456_, v_toZero_452_, v___f_457_, v_i_447_, v_j_448_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___redArg___boxed(lean_object* v_inst_462_, lean_object* v_r_463_, lean_object* v_n_464_, lean_object* v_g_465_, lean_object* v_i_466_, lean_object* v_j_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = lp_tree_Formalism_L2_Col_diagMat___redArg(v_inst_462_, v_r_463_, v_n_464_, v_g_465_, v_i_466_, v_j_467_);
lean_dec(v_r_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat(lean_object* v_00_u03ba_469_, lean_object* v_inst_470_, lean_object* v_r_471_, lean_object* v_n_472_, lean_object* v_g_473_, lean_object* v_i_474_, lean_object* v_j_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lp_tree_Formalism_L2_Col_diagMat___redArg(v_inst_470_, v_r_471_, v_n_472_, v_g_473_, v_i_474_, v_j_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagMat___boxed(lean_object* v_00_u03ba_477_, lean_object* v_inst_478_, lean_object* v_r_479_, lean_object* v_n_480_, lean_object* v_g_481_, lean_object* v_i_482_, lean_object* v_j_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = lp_tree_Formalism_L2_Col_diagMat(v_00_u03ba_477_, v_inst_478_, v_r_479_, v_n_480_, v_g_481_, v_i_482_, v_j_483_);
lean_dec(v_r_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagEmb___redArg(lean_object* v_inst_485_, lean_object* v_r_486_, lean_object* v_n_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___f_489_; 
v___x_488_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_diagMat___boxed), 7, 4);
lean_closure_set(v___x_488_, 0, lean_box(0));
lean_closure_set(v___x_488_, 1, v_inst_485_);
lean_closure_set(v___x_488_, 2, v_r_486_);
lean_closure_set(v___x_488_, 3, v_n_487_);
v___f_489_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_489_, 0, v___x_488_);
return v___f_489_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagEmb(lean_object* v_00_u03ba_490_, lean_object* v_inst_491_, lean_object* v_r_492_, lean_object* v_n_493_, lean_object* v_h_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lp_tree_Formalism_L2_Col_diagEmb___redArg(v_inst_491_, v_r_492_, v_n_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fixCol(lean_object* v_n_496_, lean_object* v_00_u03ba_497_, lean_object* v_inst_498_, lean_object* v_c_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = lean_box(0);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fixCol___boxed(lean_object* v_n_501_, lean_object* v_00_u03ba_502_, lean_object* v_inst_503_, lean_object* v_c_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = lp_tree_Formalism_L2_Col_fixCol(v_n_501_, v_00_u03ba_502_, v_inst_503_, v_c_504_);
lean_dec(v_c_504_);
lean_dec_ref(v_inst_503_);
lean_dec(v_n_501_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK(lean_object* v_n_506_, lean_object* v_00_u03ba_507_, lean_object* v_inst_508_, lean_object* v_r_509_, lean_object* v_bl_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_box(0);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK___boxed(lean_object* v_n_512_, lean_object* v_00_u03ba_513_, lean_object* v_inst_514_, lean_object* v_r_515_, lean_object* v_bl_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = lp_tree_Formalism_L2_Col_HK(v_n_512_, v_00_u03ba_513_, v_inst_514_, v_r_515_, v_bl_516_);
lean_dec(v_bl_516_);
lean_dec(v_r_515_);
lean_dec_ref(v_inst_514_);
lean_dec(v_n_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___redArg(lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_00_u03c7_520_, lean_object* v_n_521_, lean_object* v_r_522_, lean_object* v_bl_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___f_525_; lean_object* v___f_526_; 
v___x_524_ = lp_tree_Formalism_L2_Col_detChar___redArg(v_inst_518_, v_inst_519_, v_00_u03c7_520_, v_n_521_, v_r_522_, v_bl_523_);
v___f_525_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_526_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_526_, 0, v___f_525_);
lean_closure_set(v___f_526_, 1, v___x_524_);
return v___f_526_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___redArg___boxed(lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_00_u03c7_529_, lean_object* v_n_530_, lean_object* v_r_531_, lean_object* v_bl_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = lp_tree_Formalism_L2_Col_lamK___redArg(v_inst_527_, v_inst_528_, v_00_u03c7_529_, v_n_530_, v_r_531_, v_bl_532_);
lean_dec_ref(v_inst_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK(lean_object* v_00_u03ba_534_, lean_object* v_inst_535_, lean_object* v_K_536_, lean_object* v_inst_537_, lean_object* v_00_u03c7_538_, lean_object* v_n_539_, lean_object* v_r_540_, lean_object* v_bl_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lp_tree_Formalism_L2_Col_lamK___redArg(v_inst_535_, v_inst_537_, v_00_u03c7_538_, v_n_539_, v_r_540_, v_bl_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___boxed(lean_object* v_00_u03ba_543_, lean_object* v_inst_544_, lean_object* v_K_545_, lean_object* v_inst_546_, lean_object* v_00_u03c7_547_, lean_object* v_n_548_, lean_object* v_r_549_, lean_object* v_bl_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = lp_tree_Formalism_L2_Col_lamK(v_00_u03ba_543_, v_inst_544_, v_K_545_, v_inst_546_, v_00_u03c7_547_, v_n_548_, v_r_549_, v_bl_550_);
lean_dec_ref(v_inst_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___redArg___lam__0(lean_object* v___y_552_){
_start:
{
lean_inc(v___y_552_);
return v___y_552_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___redArg___lam__0___boxed(lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = lp_tree_Formalism_L2_Col_restr___redArg___lam__0(v___y_553_);
lean_dec(v___y_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___redArg(lean_object* v_A_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___f_559_; lean_object* v___x_560_; 
v___f_559_ = ((lean_object*)(lp_tree_Formalism_L2_Col_restr___redArg___closed__0));
v___x_560_ = lp_mathlib_Matrix_submatrix___redArg(v_A_556_, v___f_559_, v___f_559_, v_a_557_, v_a_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr(lean_object* v_n_561_, lean_object* v_00_u03ba_562_, lean_object* v_r_563_, lean_object* v_h_564_, lean_object* v_A_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lp_tree_Formalism_L2_Col_restr___redArg(v_A_565_, v_a_566_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_restr___boxed(lean_object* v_n_569_, lean_object* v_00_u03ba_570_, lean_object* v_r_571_, lean_object* v_h_572_, lean_object* v_A_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = lp_tree_Formalism_L2_Col_restr(v_n_569_, v_00_u03ba_570_, v_r_571_, v_h_572_, v_A_573_, v_a_574_, v_a_575_);
lean_dec(v_r_571_);
lean_dec(v_n_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___redArg___lam__0(lean_object* v_n_577_, lean_object* v_r_578_, lean_object* v_M_579_){
_start:
{
lean_object* v_val_580_; lean_object* v_inv_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_590_; 
v_val_580_ = lean_ctor_get(v_M_579_, 0);
v_inv_581_ = lean_ctor_get(v_M_579_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_M_579_);
if (v_isSharedCheck_590_ == 0)
{
v___x_583_ = v_M_579_;
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_inv_581_);
lean_inc(v_val_580_);
lean_dec(v_M_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
lean_inc(v_r_578_);
lean_inc(v_n_577_);
v___x_585_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_restr___boxed), 7, 5);
lean_closure_set(v___x_585_, 0, v_n_577_);
lean_closure_set(v___x_585_, 1, lean_box(0));
lean_closure_set(v___x_585_, 2, v_r_578_);
lean_closure_set(v___x_585_, 3, lean_box(0));
lean_closure_set(v___x_585_, 4, v_val_580_);
v___x_586_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_restr___boxed), 7, 5);
lean_closure_set(v___x_586_, 0, v_n_577_);
lean_closure_set(v___x_586_, 1, lean_box(0));
lean_closure_set(v___x_586_, 2, v_r_578_);
lean_closure_set(v___x_586_, 3, lean_box(0));
lean_closure_set(v___x_586_, 4, v_inv_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v___x_586_);
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___redArg(lean_object* v_n_591_, lean_object* v_r_592_){
_start:
{
lean_object* v___f_593_; 
v___f_593_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blk0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_593_, 0, v_n_591_);
lean_closure_set(v___f_593_, 1, v_r_592_);
return v___f_593_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0(lean_object* v_n_594_, lean_object* v_00_u03ba_595_, lean_object* v_inst_596_, lean_object* v_r_597_, lean_object* v_h_598_, lean_object* v_bl_599_){
_start:
{
lean_object* v___f_600_; 
v___f_600_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blk0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_600_, 0, v_n_594_);
lean_closure_set(v___f_600_, 1, v_r_597_);
return v___f_600_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___boxed(lean_object* v_n_601_, lean_object* v_00_u03ba_602_, lean_object* v_inst_603_, lean_object* v_r_604_, lean_object* v_h_605_, lean_object* v_bl_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = lp_tree_Formalism_L2_Col_blk0(v_n_601_, v_00_u03ba_602_, v_inst_603_, v_r_604_, v_h_605_, v_bl_606_);
lean_dec(v_bl_606_);
lean_dec_ref(v_inst_603_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar(lean_object* v_n_608_, lean_object* v_00_u03ba_609_, lean_object* v_inst_610_, lean_object* v_r_611_, lean_object* v_h_612_, lean_object* v_bl_613_, lean_object* v_H_u2080_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(0);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___boxed(lean_object* v_n_616_, lean_object* v_00_u03ba_617_, lean_object* v_inst_618_, lean_object* v_r_619_, lean_object* v_h_620_, lean_object* v_bl_621_, lean_object* v_H_u2080_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = lp_tree_Formalism_L2_Col_HPar(v_n_616_, v_00_u03ba_617_, v_inst_618_, v_r_619_, v_h_620_, v_bl_621_, v_H_u2080_622_);
lean_dec(v_bl_621_);
lean_dec(v_r_619_);
lean_dec_ref(v_inst_618_);
lean_dec(v_n_616_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___redArg(lean_object* v_n_624_, lean_object* v_r_625_){
_start:
{
lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___f_629_; 
v___f_626_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blk0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_626_, 0, v_n_624_);
lean_closure_set(v___f_626_, 1, v_r_625_);
v___f_627_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_628_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_628_, 0, v___f_627_);
lean_closure_set(v___f_628_, 1, v___f_626_);
v___f_629_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_629_, 0, v___f_628_);
return v___f_629_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0(lean_object* v_n_630_, lean_object* v_00_u03ba_631_, lean_object* v_inst_632_, lean_object* v_r_633_, lean_object* v_h_634_, lean_object* v_bl_635_, lean_object* v_H_u2080_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lp_tree_Formalism_L2_Col_HPar0___redArg(v_n_630_, v_r_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___boxed(lean_object* v_n_638_, lean_object* v_00_u03ba_639_, lean_object* v_inst_640_, lean_object* v_r_641_, lean_object* v_h_642_, lean_object* v_bl_643_, lean_object* v_H_u2080_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = lp_tree_Formalism_L2_Col_HPar0(v_n_638_, v_00_u03ba_639_, v_inst_640_, v_r_641_, v_h_642_, v_bl_643_, v_H_u2080_644_);
lean_dec(v_bl_643_);
lean_dec_ref(v_inst_640_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg___lam__0(lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v_lam_u2080_648_, lean_object* v___f_649_, lean_object* v___x_650_, lean_object* v_m_651_){
_start:
{
lean_object* v___x_652_; lean_object* v_toMul_653_; lean_object* v___x_654_; lean_object* v_val_655_; lean_object* v_inv_656_; lean_object* v___x_657_; lean_object* v_val_658_; lean_object* v_inv_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
v___x_652_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_646_);
v_toMul_653_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_toMul_653_);
lean_dec_ref(v___x_652_);
lean_inc_ref(v_m_651_);
v___x_654_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___x_647_, v_lam_u2080_648_, v_m_651_);
v_val_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_655_);
v_inv_656_ = lean_ctor_get(v___x_654_, 1);
lean_inc(v_inv_656_);
lean_dec(v___x_654_);
v___x_657_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_649_, v___x_650_, v_m_651_);
v_val_658_ = lean_ctor_get(v___x_657_, 0);
v_inv_659_ = lean_ctor_get(v___x_657_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_668_ == 0)
{
v___x_661_ = v___x_657_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_inv_659_);
lean_inc(v_val_658_);
lean_dec(v___x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_toMul_653_);
v___x_663_ = lean_apply_2(v_toMul_653_, v_val_655_, v_val_658_);
v___x_664_ = lean_apply_2(v_toMul_653_, v_inv_659_, v_inv_656_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_664_);
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg___lam__0___boxed(lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_lam_u2080_671_, lean_object* v___f_672_, lean_object* v___x_673_, lean_object* v_m_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = lp_tree_Formalism_L2_Col_lamPar___redArg___lam__0(v___x_669_, v___x_670_, v_lam_u2080_671_, v___f_672_, v___x_673_, v_m_674_);
lean_dec_ref(v___x_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg(lean_object* v_n_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_r_679_, lean_object* v_bl_680_, lean_object* v_lam_u2080_681_, lean_object* v_00_u03c7_682_){
_start:
{
lean_object* v_toCommRing_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___f_687_; lean_object* v___f_688_; 
v_toCommRing_683_ = lean_ctor_get(v_inst_678_, 0);
v___x_684_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_683_);
lean_inc(v_r_679_);
lean_inc(v_n_676_);
v___x_685_ = lp_tree_Formalism_L2_Col_HPar0___redArg(v_n_676_, v_r_679_);
v___x_686_ = lp_tree_Formalism_L2_Col_detChar___redArg(v_inst_677_, v_inst_678_, v_00_u03c7_682_, v_n_676_, v_r_679_, v_bl_680_);
v___f_687_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_688_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_lamPar___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_688_, 0, v___x_684_);
lean_closure_set(v___f_688_, 1, v___x_685_);
lean_closure_set(v___f_688_, 2, v_lam_u2080_681_);
lean_closure_set(v___f_688_, 3, v___f_687_);
lean_closure_set(v___f_688_, 4, v___x_686_);
return v___f_688_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg___boxed(lean_object* v_n_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_r_692_, lean_object* v_bl_693_, lean_object* v_lam_u2080_694_, lean_object* v_00_u03c7_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = lp_tree_Formalism_L2_Col_lamPar___redArg(v_n_689_, v_inst_690_, v_inst_691_, v_r_692_, v_bl_693_, v_lam_u2080_694_, v_00_u03c7_695_);
lean_dec_ref(v_inst_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar(lean_object* v_n_697_, lean_object* v_00_u03ba_698_, lean_object* v_inst_699_, lean_object* v_K_700_, lean_object* v_inst_701_, lean_object* v_r_702_, lean_object* v_h_703_, lean_object* v_bl_704_, lean_object* v_H_u2080_705_, lean_object* v_lam_u2080_706_, lean_object* v_00_u03c7_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lp_tree_Formalism_L2_Col_lamPar___redArg(v_n_697_, v_inst_699_, v_inst_701_, v_r_702_, v_bl_704_, v_lam_u2080_706_, v_00_u03c7_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___boxed(lean_object* v_n_709_, lean_object* v_00_u03ba_710_, lean_object* v_inst_711_, lean_object* v_K_712_, lean_object* v_inst_713_, lean_object* v_r_714_, lean_object* v_h_715_, lean_object* v_bl_716_, lean_object* v_H_u2080_717_, lean_object* v_lam_u2080_718_, lean_object* v_00_u03c7_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = lp_tree_Formalism_L2_Col_lamPar(v_n_709_, v_00_u03ba_710_, v_inst_711_, v_K_712_, v_inst_713_, v_r_714_, v_h_715_, v_bl_716_, v_H_u2080_717_, v_lam_u2080_718_, v_00_u03c7_719_);
lean_dec_ref(v_inst_713_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HU(lean_object* v_00_u03ba_721_, lean_object* v_inst_722_, lean_object* v_k_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HU___boxed(lean_object* v_00_u03ba_725_, lean_object* v_inst_726_, lean_object* v_k_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = lp_tree_Formalism_L2_Col_HU(v_00_u03ba_725_, v_inst_726_, v_k_727_);
lean_dec(v_k_727_);
lean_dec_ref(v_inst_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU___redArg(lean_object* v_inst_729_, lean_object* v_00_u03c8_730_, lean_object* v_k_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_sub(v_k_731_, v___x_732_);
v___x_734_ = l_List_range(v___x_733_);
lean_inc(v_k_731_);
v___x_735_ = lp_tree_Formalism_L2_Col_supChar___redArg(v_inst_729_, v_00_u03c8_730_, v_k_731_, v_k_731_, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU(lean_object* v_00_u03ba_736_, lean_object* v_inst_737_, lean_object* v_K_738_, lean_object* v_inst_739_, lean_object* v_00_u03c8_740_, lean_object* v_k_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lp_tree_Formalism_L2_Col_psiU___redArg(v_inst_737_, v_00_u03c8_740_, v_k_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU___boxed(lean_object* v_00_u03ba_743_, lean_object* v_inst_744_, lean_object* v_K_745_, lean_object* v_inst_746_, lean_object* v_00_u03c8_747_, lean_object* v_k_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = lp_tree_Formalism_L2_Col_psiU(v_00_u03ba_743_, v_inst_744_, v_K_745_, v_inst_746_, v_00_u03c8_747_, v_k_748_);
lean_dec_ref(v_inst_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HX(lean_object* v_00_u03ba_750_, lean_object* v_inst_751_, lean_object* v_n_752_, lean_object* v_k_753_, lean_object* v_t_754_, lean_object* v_j_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_box(0);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HX___boxed(lean_object* v_00_u03ba_757_, lean_object* v_inst_758_, lean_object* v_n_759_, lean_object* v_k_760_, lean_object* v_t_761_, lean_object* v_j_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = lp_tree_Formalism_L2_Col_HX(v_00_u03ba_757_, v_inst_758_, v_n_759_, v_k_760_, v_t_761_, v_j_762_);
lean_dec(v_j_762_);
lean_dec(v_t_761_);
lean_dec(v_k_760_);
lean_dec(v_n_759_);
lean_dec_ref(v_inst_758_);
return v_res_763_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_SX___lam__0(lean_object* v_k_764_, lean_object* v_j_765_, lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_a_767_, v___x_768_);
v___x_770_ = lean_nat_dec_eq(v___x_769_, v_k_764_);
lean_dec(v___x_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = 1;
return v___x_771_;
}
else
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_nat_add(v_j_765_, v___x_768_);
v___x_773_ = lean_nat_dec_eq(v___x_772_, v_m_766_);
lean_dec(v___x_772_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SX___lam__0___boxed(lean_object* v_k_774_, lean_object* v_j_775_, lean_object* v_m_776_, lean_object* v_a_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = lp_tree_Formalism_L2_Col_SX___lam__0(v_k_774_, v_j_775_, v_m_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec(v_m_776_);
lean_dec(v_j_775_);
lean_dec(v_k_774_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SX(lean_object* v_k_780_, lean_object* v_m_781_, lean_object* v_j_782_){
_start:
{
lean_object* v___f_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc(v_j_782_);
lean_inc(v_k_780_);
v___f_783_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_SX___lam__0___boxed), 4, 3);
lean_closure_set(v___f_783_, 0, v_k_780_);
lean_closure_set(v___f_783_, 1, v_j_782_);
lean_closure_set(v___f_783_, 2, v_m_781_);
v___x_784_ = lean_nat_add(v_k_780_, v_j_782_);
lean_dec(v_j_782_);
lean_dec(v_k_780_);
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_sub(v___x_784_, v___x_785_);
lean_dec(v___x_784_);
v___x_787_ = l_List_range(v___x_786_);
v___x_788_ = lp_mathlib_Multiset_filter___redArg(v___f_783_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX___redArg(lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_00_u03c8_791_, lean_object* v_00_u03c7_792_, lean_object* v_n_793_, lean_object* v_k_794_, lean_object* v_m_795_, lean_object* v_t_796_, lean_object* v_j_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = lean_nat_add(v_k_794_, v_j_797_);
lean_inc(v_j_797_);
v___x_799_ = l_List_replicateTR___redArg(v_j_797_, v_t_796_);
v___x_800_ = lp_tree_Formalism_L2_Col_SX(v_k_794_, v_m_795_, v_j_797_);
v___x_801_ = lp_tree_Formalism_L2_Col_lamGen___redArg(v_inst_789_, v_inst_790_, v_00_u03c8_791_, v_00_u03c7_792_, v_n_793_, v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX___redArg___boxed(lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_00_u03c8_804_, lean_object* v_00_u03c7_805_, lean_object* v_n_806_, lean_object* v_k_807_, lean_object* v_m_808_, lean_object* v_t_809_, lean_object* v_j_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = lp_tree_Formalism_L2_Col_lamX___redArg(v_inst_802_, v_inst_803_, v_00_u03c8_804_, v_00_u03c7_805_, v_n_806_, v_k_807_, v_m_808_, v_t_809_, v_j_810_);
lean_dec_ref(v_inst_803_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX(lean_object* v_00_u03ba_812_, lean_object* v_inst_813_, lean_object* v_K_814_, lean_object* v_inst_815_, lean_object* v_00_u03c8_816_, lean_object* v_00_u03c7_817_, lean_object* v_n_818_, lean_object* v_k_819_, lean_object* v_m_820_, lean_object* v_t_821_, lean_object* v_j_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lp_tree_Formalism_L2_Col_lamX___redArg(v_inst_813_, v_inst_815_, v_00_u03c8_816_, v_00_u03c7_817_, v_n_818_, v_k_819_, v_m_820_, v_t_821_, v_j_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamX___boxed(lean_object* v_00_u03ba_824_, lean_object* v_inst_825_, lean_object* v_K_826_, lean_object* v_inst_827_, lean_object* v_00_u03c8_828_, lean_object* v_00_u03c7_829_, lean_object* v_n_830_, lean_object* v_k_831_, lean_object* v_m_832_, lean_object* v_t_833_, lean_object* v_j_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = lp_tree_Formalism_L2_Col_lamX(v_00_u03ba_824_, v_inst_825_, v_K_826_, v_inst_827_, v_00_u03c8_828_, v_00_u03c7_829_, v_n_830_, v_k_831_, v_m_832_, v_t_833_, v_j_834_);
lean_dec_ref(v_inst_827_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJ(lean_object* v_00_u03ba_836_, lean_object* v_inst_837_, lean_object* v_n_838_, lean_object* v_r_839_, lean_object* v_t_840_, lean_object* v_j_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_box(0);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJ___boxed(lean_object* v_00_u03ba_843_, lean_object* v_inst_844_, lean_object* v_n_845_, lean_object* v_r_846_, lean_object* v_t_847_, lean_object* v_j_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = lp_tree_Formalism_L2_Col_HJ(v_00_u03ba_843_, v_inst_844_, v_n_845_, v_r_846_, v_t_847_, v_j_848_);
lean_dec(v_j_848_);
lean_dec(v_t_847_);
lean_dec(v_r_846_);
lean_dec(v_n_845_);
lean_dec_ref(v_inst_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ___redArg(lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_00_u03c8_852_, lean_object* v_00_u03c7_853_, lean_object* v_n_854_, lean_object* v_r_855_, lean_object* v_t_856_, lean_object* v_j_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_858_ = l_List_replicateTR___redArg(v_j_857_, v_t_856_);
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = lean_nat_sub(v_r_855_, v___x_859_);
v___x_861_ = l_List_range(v___x_860_);
v___x_862_ = lp_tree_Formalism_L2_Col_lamGen___redArg(v_inst_850_, v_inst_851_, v_00_u03c8_852_, v_00_u03c7_853_, v_n_854_, v_r_855_, v___x_858_, v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ___redArg___boxed(lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_00_u03c8_865_, lean_object* v_00_u03c7_866_, lean_object* v_n_867_, lean_object* v_r_868_, lean_object* v_t_869_, lean_object* v_j_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = lp_tree_Formalism_L2_Col_lamJ___redArg(v_inst_863_, v_inst_864_, v_00_u03c8_865_, v_00_u03c7_866_, v_n_867_, v_r_868_, v_t_869_, v_j_870_);
lean_dec_ref(v_inst_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ(lean_object* v_00_u03ba_872_, lean_object* v_inst_873_, lean_object* v_K_874_, lean_object* v_inst_875_, lean_object* v_00_u03c8_876_, lean_object* v_00_u03c7_877_, lean_object* v_n_878_, lean_object* v_r_879_, lean_object* v_t_880_, lean_object* v_j_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lp_tree_Formalism_L2_Col_lamJ___redArg(v_inst_873_, v_inst_875_, v_00_u03c8_876_, v_00_u03c7_877_, v_n_878_, v_r_879_, v_t_880_, v_j_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJ___boxed(lean_object* v_00_u03ba_883_, lean_object* v_inst_884_, lean_object* v_K_885_, lean_object* v_inst_886_, lean_object* v_00_u03c8_887_, lean_object* v_00_u03c7_888_, lean_object* v_n_889_, lean_object* v_r_890_, lean_object* v_t_891_, lean_object* v_j_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = lp_tree_Formalism_L2_Col_lamJ(v_00_u03ba_883_, v_inst_884_, v_K_885_, v_inst_886_, v_00_u03c8_887_, v_00_u03c7_888_, v_n_889_, v_r_890_, v_t_891_, v_j_892_);
lean_dec_ref(v_inst_886_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsharp(lean_object* v_00_u03ba_894_, lean_object* v_inst_895_, lean_object* v_n_896_, lean_object* v_k_897_, lean_object* v_r_898_, lean_object* v_t_899_, lean_object* v_j_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_box(0);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsharp___boxed(lean_object* v_00_u03ba_902_, lean_object* v_inst_903_, lean_object* v_n_904_, lean_object* v_k_905_, lean_object* v_r_906_, lean_object* v_t_907_, lean_object* v_j_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = lp_tree_Formalism_L2_Col_HJsharp(v_00_u03ba_902_, v_inst_903_, v_n_904_, v_k_905_, v_r_906_, v_t_907_, v_j_908_);
lean_dec(v_j_908_);
lean_dec(v_t_907_);
lean_dec(v_r_906_);
lean_dec(v_k_905_);
lean_dec(v_n_904_);
lean_dec_ref(v_inst_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp___redArg(lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_00_u03c8_912_, lean_object* v_00_u03c7_913_, lean_object* v_n_914_, lean_object* v_r_915_, lean_object* v_t_916_, lean_object* v_j_917_){
_start:
{
lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___f_920_; 
v___x_918_ = lp_tree_Formalism_L2_Col_lamJ___redArg(v_inst_910_, v_inst_911_, v_00_u03c8_912_, v_00_u03c7_913_, v_n_914_, v_r_915_, v_t_916_, v_j_917_);
v___f_919_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_920_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_920_, 0, v___f_919_);
lean_closure_set(v___f_920_, 1, v___x_918_);
return v___f_920_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp___redArg___boxed(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_00_u03c8_923_, lean_object* v_00_u03c7_924_, lean_object* v_n_925_, lean_object* v_r_926_, lean_object* v_t_927_, lean_object* v_j_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = lp_tree_Formalism_L2_Col_lamJsharp___redArg(v_inst_921_, v_inst_922_, v_00_u03c8_923_, v_00_u03c7_924_, v_n_925_, v_r_926_, v_t_927_, v_j_928_);
lean_dec_ref(v_inst_922_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp(lean_object* v_00_u03ba_930_, lean_object* v_inst_931_, lean_object* v_K_932_, lean_object* v_inst_933_, lean_object* v_00_u03c8_934_, lean_object* v_00_u03c7_935_, lean_object* v_n_936_, lean_object* v_k_937_, lean_object* v_r_938_, lean_object* v_t_939_, lean_object* v_j_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lp_tree_Formalism_L2_Col_lamJsharp___redArg(v_inst_931_, v_inst_933_, v_00_u03c8_934_, v_00_u03c7_935_, v_n_936_, v_r_938_, v_t_939_, v_j_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsharp___boxed(lean_object* v_00_u03ba_942_, lean_object* v_inst_943_, lean_object* v_K_944_, lean_object* v_inst_945_, lean_object* v_00_u03c8_946_, lean_object* v_00_u03c7_947_, lean_object* v_n_948_, lean_object* v_k_949_, lean_object* v_r_950_, lean_object* v_t_951_, lean_object* v_j_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = lp_tree_Formalism_L2_Col_lamJsharp(v_00_u03ba_942_, v_inst_943_, v_K_944_, v_inst_945_, v_00_u03c8_946_, v_00_u03c7_947_, v_n_948_, v_k_949_, v_r_950_, v_t_951_, v_j_952_);
lean_dec(v_k_949_);
lean_dec_ref(v_inst_945_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXm(lean_object* v_00_u03ba_954_, lean_object* v_inst_955_, lean_object* v_n_956_, lean_object* v_r_957_, lean_object* v_t_958_, lean_object* v_m_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_box(0);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXm___boxed(lean_object* v_00_u03ba_961_, lean_object* v_inst_962_, lean_object* v_n_963_, lean_object* v_r_964_, lean_object* v_t_965_, lean_object* v_m_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = lp_tree_Formalism_L2_Col_HXm(v_00_u03ba_961_, v_inst_962_, v_n_963_, v_r_964_, v_t_965_, v_m_966_);
lean_dec(v_m_966_);
lean_dec(v_t_965_);
lean_dec(v_r_964_);
lean_dec(v_n_963_);
lean_dec_ref(v_inst_962_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm___redArg(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_00_u03c8_970_, lean_object* v_00_u03c7_971_, lean_object* v_n_972_, lean_object* v_r_973_, lean_object* v_t_974_, lean_object* v_m_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___f_977_; lean_object* v___f_978_; 
v___x_976_ = lp_tree_Formalism_L2_Col_lamJ___redArg(v_inst_968_, v_inst_969_, v_00_u03c8_970_, v_00_u03c7_971_, v_n_972_, v_r_973_, v_t_974_, v_m_975_);
v___f_977_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_978_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_978_, 0, v___f_977_);
lean_closure_set(v___f_978_, 1, v___x_976_);
return v___f_978_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm___redArg___boxed(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_00_u03c8_981_, lean_object* v_00_u03c7_982_, lean_object* v_n_983_, lean_object* v_r_984_, lean_object* v_t_985_, lean_object* v_m_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = lp_tree_Formalism_L2_Col_lamXm___redArg(v_inst_979_, v_inst_980_, v_00_u03c8_981_, v_00_u03c7_982_, v_n_983_, v_r_984_, v_t_985_, v_m_986_);
lean_dec_ref(v_inst_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm(lean_object* v_00_u03ba_988_, lean_object* v_inst_989_, lean_object* v_K_990_, lean_object* v_inst_991_, lean_object* v_00_u03c8_992_, lean_object* v_00_u03c7_993_, lean_object* v_n_994_, lean_object* v_r_995_, lean_object* v_t_996_, lean_object* v_m_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lp_tree_Formalism_L2_Col_lamXm___redArg(v_inst_989_, v_inst_991_, v_00_u03c8_992_, v_00_u03c7_993_, v_n_994_, v_r_995_, v_t_996_, v_m_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXm___boxed(lean_object* v_00_u03ba_999_, lean_object* v_inst_1000_, lean_object* v_K_1001_, lean_object* v_inst_1002_, lean_object* v_00_u03c8_1003_, lean_object* v_00_u03c7_1004_, lean_object* v_n_1005_, lean_object* v_r_1006_, lean_object* v_t_1007_, lean_object* v_m_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = lp_tree_Formalism_L2_Col_lamXm(v_00_u03ba_999_, v_inst_1000_, v_K_1001_, v_inst_1002_, v_00_u03c8_1003_, v_00_u03c7_1004_, v_n_1005_, v_r_1006_, v_t_1007_, v_m_1008_);
lean_dec_ref(v_inst_1002_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsharp(lean_object* v_00_u03ba_1010_, lean_object* v_inst_1011_, lean_object* v_n_1012_, lean_object* v_k_1013_, lean_object* v_r_1014_, lean_object* v_t_1015_, lean_object* v_m_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_box(0);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsharp___boxed(lean_object* v_00_u03ba_1018_, lean_object* v_inst_1019_, lean_object* v_n_1020_, lean_object* v_k_1021_, lean_object* v_r_1022_, lean_object* v_t_1023_, lean_object* v_m_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = lp_tree_Formalism_L2_Col_HXmsharp(v_00_u03ba_1018_, v_inst_1019_, v_n_1020_, v_k_1021_, v_r_1022_, v_t_1023_, v_m_1024_);
lean_dec(v_m_1024_);
lean_dec(v_t_1023_);
lean_dec(v_r_1022_);
lean_dec(v_k_1021_);
lean_dec(v_n_1020_);
lean_dec_ref(v_inst_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_00_u03c8_1028_, lean_object* v_00_u03c7_1029_, lean_object* v_n_1030_, lean_object* v_r_1031_, lean_object* v_t_1032_, lean_object* v_m_1033_){
_start:
{
lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; 
v___x_1034_ = lp_tree_Formalism_L2_Col_lamXm___redArg(v_inst_1026_, v_inst_1027_, v_00_u03c8_1028_, v_00_u03c7_1029_, v_n_1030_, v_r_1031_, v_t_1032_, v_m_1033_);
v___f_1035_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_1036_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1036_, 0, v___f_1035_);
lean_closure_set(v___f_1036_, 1, v___x_1034_);
return v___f_1036_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp___redArg___boxed(lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_00_u03c8_1039_, lean_object* v_00_u03c7_1040_, lean_object* v_n_1041_, lean_object* v_r_1042_, lean_object* v_t_1043_, lean_object* v_m_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = lp_tree_Formalism_L2_Col_lamXmsharp___redArg(v_inst_1037_, v_inst_1038_, v_00_u03c8_1039_, v_00_u03c7_1040_, v_n_1041_, v_r_1042_, v_t_1043_, v_m_1044_);
lean_dec_ref(v_inst_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp(lean_object* v_00_u03ba_1046_, lean_object* v_inst_1047_, lean_object* v_K_1048_, lean_object* v_inst_1049_, lean_object* v_00_u03c8_1050_, lean_object* v_00_u03c7_1051_, lean_object* v_n_1052_, lean_object* v_k_1053_, lean_object* v_r_1054_, lean_object* v_t_1055_, lean_object* v_m_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lp_tree_Formalism_L2_Col_lamXmsharp___redArg(v_inst_1047_, v_inst_1049_, v_00_u03c8_1050_, v_00_u03c7_1051_, v_n_1052_, v_r_1054_, v_t_1055_, v_m_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsharp___boxed(lean_object* v_00_u03ba_1058_, lean_object* v_inst_1059_, lean_object* v_K_1060_, lean_object* v_inst_1061_, lean_object* v_00_u03c8_1062_, lean_object* v_00_u03c7_1063_, lean_object* v_n_1064_, lean_object* v_k_1065_, lean_object* v_r_1066_, lean_object* v_t_1067_, lean_object* v_m_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = lp_tree_Formalism_L2_Col_lamXmsharp(v_00_u03ba_1058_, v_inst_1059_, v_K_1060_, v_inst_1061_, v_00_u03c8_1062_, v_00_u03c7_1063_, v_n_1064_, v_k_1065_, v_r_1066_, v_t_1067_, v_m_1068_);
lean_dec(v_k_1065_);
lean_dec_ref(v_inst_1061_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HV(lean_object* v_00_u03ba_1070_, lean_object* v_inst_1071_, lean_object* v_n_1072_, lean_object* v_r_1073_, lean_object* v_t_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HV___boxed(lean_object* v_00_u03ba_1076_, lean_object* v_inst_1077_, lean_object* v_n_1078_, lean_object* v_r_1079_, lean_object* v_t_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = lp_tree_Formalism_L2_Col_HV(v_00_u03ba_1076_, v_inst_1077_, v_n_1078_, v_r_1079_, v_t_1080_);
lean_dec(v_t_1080_);
lean_dec(v_r_1079_);
lean_dec(v_n_1078_);
lean_dec_ref(v_inst_1077_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg___lam__0(lean_object* v_00_u03c7j_1082_, lean_object* v_x_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v_val_1086_; lean_object* v_inv_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v___x_1085_ = lean_apply_1(v_00_u03c7j_1082_, v___y_1084_);
v_val_1086_ = lean_ctor_get(v___x_1085_, 0);
v_inv_1087_ = lean_ctor_get(v___x_1085_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_inv_1087_);
lean_inc(v_val_1086_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_val_1086_);
lean_ctor_set(v___x_1089_, 0, v_inv_1087_);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_inv_1087_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_val_1086_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg___lam__0___boxed(lean_object* v_00_u03c7j_1095_, lean_object* v_x_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = lp_tree_Formalism_L2_Col_lamV___redArg___lam__0(v_00_u03c7j_1095_, v_x_1096_, v___y_1097_);
lean_dec(v_x_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_00_u03c8_1101_, lean_object* v_00_u03c7j_1102_, lean_object* v_n_1103_, lean_object* v_r_1104_, lean_object* v_t_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v_toCommRing_1107_; lean_object* v___x_1108_; lean_object* v_toAddMonoid_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1106_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_1099_);
v_toCommRing_1107_ = lean_ctor_get(v_inst_1100_, 0);
v___x_1108_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_1107_);
v_toAddMonoid_1109_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_toAddMonoid_1109_);
v___f_1110_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_lamV___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1110_, 0, v_00_u03c7j_1102_);
v___x_1111_ = lp_mathlib_negAddMonoidHom___redArg(v___x_1106_);
lean_dec_ref(v___x_1106_);
v___x_1112_ = lp_mathlib_AddChar_compAddMonoidHom___redArg(v_toAddMonoid_1109_, v___x_1108_, v_00_u03c8_1101_, v___x_1111_);
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_toAddMonoid_1109_);
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_t_1105_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_sub(v_r_1104_, v___x_1115_);
v___x_1117_ = l_List_range(v___x_1116_);
v___x_1118_ = lp_tree_Formalism_L2_Col_lamGen___redArg(v_inst_1099_, v_inst_1100_, v___x_1112_, v___f_1110_, v_n_1103_, v_r_1104_, v___x_1114_, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___redArg___boxed(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_00_u03c8_1121_, lean_object* v_00_u03c7j_1122_, lean_object* v_n_1123_, lean_object* v_r_1124_, lean_object* v_t_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = lp_tree_Formalism_L2_Col_lamV___redArg(v_inst_1119_, v_inst_1120_, v_00_u03c8_1121_, v_00_u03c7j_1122_, v_n_1123_, v_r_1124_, v_t_1125_);
lean_dec_ref(v_inst_1120_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV(lean_object* v_00_u03ba_1127_, lean_object* v_inst_1128_, lean_object* v_K_1129_, lean_object* v_inst_1130_, lean_object* v_00_u03c8_1131_, lean_object* v_00_u03c7j_1132_, lean_object* v_n_1133_, lean_object* v_r_1134_, lean_object* v_t_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lp_tree_Formalism_L2_Col_lamV___redArg(v_inst_1128_, v_inst_1130_, v_00_u03c8_1131_, v_00_u03c7j_1132_, v_n_1133_, v_r_1134_, v_t_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamV___boxed(lean_object* v_00_u03ba_1137_, lean_object* v_inst_1138_, lean_object* v_K_1139_, lean_object* v_inst_1140_, lean_object* v_00_u03c8_1141_, lean_object* v_00_u03c7j_1142_, lean_object* v_n_1143_, lean_object* v_r_1144_, lean_object* v_t_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = lp_tree_Formalism_L2_Col_lamV(v_00_u03ba_1137_, v_inst_1138_, v_K_1139_, v_inst_1140_, v_00_u03c8_1141_, v_00_u03c7j_1142_, v_n_1143_, v_r_1144_, v_t_1145_);
lean_dec_ref(v_inst_1140_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HVsharp(lean_object* v_00_u03ba_1147_, lean_object* v_inst_1148_, lean_object* v_n_1149_, lean_object* v_k_1150_, lean_object* v_r_1151_, lean_object* v_t_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HVsharp___boxed(lean_object* v_00_u03ba_1154_, lean_object* v_inst_1155_, lean_object* v_n_1156_, lean_object* v_k_1157_, lean_object* v_r_1158_, lean_object* v_t_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = lp_tree_Formalism_L2_Col_HVsharp(v_00_u03ba_1154_, v_inst_1155_, v_n_1156_, v_k_1157_, v_r_1158_, v_t_1159_);
lean_dec(v_t_1159_);
lean_dec(v_r_1158_);
lean_dec(v_k_1157_);
lean_dec(v_n_1156_);
lean_dec_ref(v_inst_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_00_u03c8_1163_, lean_object* v_00_u03c7j_1164_, lean_object* v_n_1165_, lean_object* v_r_1166_, lean_object* v_t_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; 
v___x_1168_ = lp_tree_Formalism_L2_Col_lamV___redArg(v_inst_1161_, v_inst_1162_, v_00_u03c8_1163_, v_00_u03c7j_1164_, v_n_1165_, v_r_1166_, v_t_1167_);
v___f_1169_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___f_1170_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1170_, 0, v___f_1169_);
lean_closure_set(v___f_1170_, 1, v___x_1168_);
return v___f_1170_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp___redArg___boxed(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_00_u03c8_1173_, lean_object* v_00_u03c7j_1174_, lean_object* v_n_1175_, lean_object* v_r_1176_, lean_object* v_t_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = lp_tree_Formalism_L2_Col_lamVsharp___redArg(v_inst_1171_, v_inst_1172_, v_00_u03c8_1173_, v_00_u03c7j_1174_, v_n_1175_, v_r_1176_, v_t_1177_);
lean_dec_ref(v_inst_1172_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp(lean_object* v_00_u03ba_1179_, lean_object* v_inst_1180_, lean_object* v_K_1181_, lean_object* v_inst_1182_, lean_object* v_00_u03c8_1183_, lean_object* v_00_u03c7j_1184_, lean_object* v_n_1185_, lean_object* v_k_1186_, lean_object* v_r_1187_, lean_object* v_t_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lp_tree_Formalism_L2_Col_lamVsharp___redArg(v_inst_1180_, v_inst_1182_, v_00_u03c8_1183_, v_00_u03c7j_1184_, v_n_1185_, v_r_1187_, v_t_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamVsharp___boxed(lean_object* v_00_u03ba_1190_, lean_object* v_inst_1191_, lean_object* v_K_1192_, lean_object* v_inst_1193_, lean_object* v_00_u03c8_1194_, lean_object* v_00_u03c7j_1195_, lean_object* v_n_1196_, lean_object* v_k_1197_, lean_object* v_r_1198_, lean_object* v_t_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = lp_tree_Formalism_L2_Col_lamVsharp(v_00_u03ba_1190_, v_inst_1191_, v_K_1192_, v_inst_1193_, v_00_u03c8_1194_, v_00_u03c7j_1195_, v_n_1196_, v_k_1197_, v_r_1198_, v_t_1199_);
lean_dec(v_k_1197_);
lean_dec_ref(v_inst_1193_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKJ(lean_object* v_00_u03ba_1201_, lean_object* v_inst_1202_, lean_object* v_n_1203_, lean_object* v_r_1204_, lean_object* v_t_1205_, lean_object* v_j_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKJ___boxed(lean_object* v_00_u03ba_1208_, lean_object* v_inst_1209_, lean_object* v_n_1210_, lean_object* v_r_1211_, lean_object* v_t_1212_, lean_object* v_j_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = lp_tree_Formalism_L2_Col_HKJ(v_00_u03ba_1208_, v_inst_1209_, v_n_1210_, v_r_1211_, v_t_1212_, v_j_1213_);
lean_dec(v_j_1213_);
lean_dec(v_t_1212_);
lean_dec(v_r_1211_);
lean_dec(v_n_1210_);
lean_dec_ref(v_inst_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___redArg(lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_00_u03c7_1217_, lean_object* v_n_1218_, lean_object* v_r_1219_, lean_object* v_t_1220_, lean_object* v_j_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = l_List_replicateTR___redArg(v_j_1221_, v_t_1220_);
v___x_1223_ = lp_tree_Formalism_L2_Col_lamK___redArg(v_inst_1215_, v_inst_1216_, v_00_u03c7_1217_, v_n_1218_, v_r_1219_, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___redArg___boxed(lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_00_u03c7_1226_, lean_object* v_n_1227_, lean_object* v_r_1228_, lean_object* v_t_1229_, lean_object* v_j_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = lp_tree_Formalism_L2_Col_lamKJ___redArg(v_inst_1224_, v_inst_1225_, v_00_u03c7_1226_, v_n_1227_, v_r_1228_, v_t_1229_, v_j_1230_);
lean_dec_ref(v_inst_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ(lean_object* v_00_u03ba_1232_, lean_object* v_inst_1233_, lean_object* v_K_1234_, lean_object* v_inst_1235_, lean_object* v_00_u03c7_1236_, lean_object* v_n_1237_, lean_object* v_r_1238_, lean_object* v_t_1239_, lean_object* v_j_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = lp_tree_Formalism_L2_Col_lamKJ___redArg(v_inst_1233_, v_inst_1235_, v_00_u03c7_1236_, v_n_1237_, v_r_1238_, v_t_1239_, v_j_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___boxed(lean_object* v_00_u03ba_1242_, lean_object* v_inst_1243_, lean_object* v_K_1244_, lean_object* v_inst_1245_, lean_object* v_00_u03c7_1246_, lean_object* v_n_1247_, lean_object* v_r_1248_, lean_object* v_t_1249_, lean_object* v_j_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = lp_tree_Formalism_L2_Col_lamKJ(v_00_u03ba_1242_, v_inst_1243_, v_K_1244_, v_inst_1245_, v_00_u03c7_1246_, v_n_1247_, v_r_1248_, v_t_1249_, v_j_1250_);
lean_dec_ref(v_inst_1245_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKV(lean_object* v_00_u03ba_1252_, lean_object* v_inst_1253_, lean_object* v_n_1254_, lean_object* v_r_1255_, lean_object* v_t_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HKV___boxed(lean_object* v_00_u03ba_1258_, lean_object* v_inst_1259_, lean_object* v_n_1260_, lean_object* v_r_1261_, lean_object* v_t_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = lp_tree_Formalism_L2_Col_HKV(v_00_u03ba_1258_, v_inst_1259_, v_n_1260_, v_r_1261_, v_t_1262_);
lean_dec(v_t_1262_);
lean_dec(v_r_1261_);
lean_dec(v_n_1260_);
lean_dec_ref(v_inst_1259_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___redArg(lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_00_u03c7j_1266_, lean_object* v_n_1267_, lean_object* v_r_1268_, lean_object* v_t_1269_){
_start:
{
lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___f_1270_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_lamV___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1270_, 0, v_00_u03c7j_1266_);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_t_1269_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lp_tree_Formalism_L2_Col_lamK___redArg(v_inst_1264_, v_inst_1265_, v___f_1270_, v_n_1267_, v_r_1268_, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___redArg___boxed(lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_00_u03c7j_1276_, lean_object* v_n_1277_, lean_object* v_r_1278_, lean_object* v_t_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = lp_tree_Formalism_L2_Col_lamKV___redArg(v_inst_1274_, v_inst_1275_, v_00_u03c7j_1276_, v_n_1277_, v_r_1278_, v_t_1279_);
lean_dec_ref(v_inst_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV(lean_object* v_00_u03ba_1281_, lean_object* v_inst_1282_, lean_object* v_K_1283_, lean_object* v_inst_1284_, lean_object* v_00_u03c7j_1285_, lean_object* v_n_1286_, lean_object* v_r_1287_, lean_object* v_t_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = lp_tree_Formalism_L2_Col_lamKV___redArg(v_inst_1282_, v_inst_1284_, v_00_u03c7j_1285_, v_n_1286_, v_r_1287_, v_t_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___boxed(lean_object* v_00_u03ba_1290_, lean_object* v_inst_1291_, lean_object* v_K_1292_, lean_object* v_inst_1293_, lean_object* v_00_u03c7j_1294_, lean_object* v_n_1295_, lean_object* v_r_1296_, lean_object* v_t_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = lp_tree_Formalism_L2_Col_lamKV(v_00_u03ba_1290_, v_inst_1291_, v_K_1292_, v_inst_1293_, v_00_u03c7j_1294_, v_n_1295_, v_r_1296_, v_t_1297_);
lean_dec_ref(v_inst_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym(lean_object* v_00_u03ba_1299_, lean_object* v_inst_1300_, lean_object* v_n_1301_, lean_object* v_k_1302_, lean_object* v_rS_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_box(0);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym___boxed(lean_object* v_00_u03ba_1305_, lean_object* v_inst_1306_, lean_object* v_n_1307_, lean_object* v_k_1308_, lean_object* v_rS_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = lp_tree_Formalism_L2_Col_HPsym(v_00_u03ba_1305_, v_inst_1306_, v_n_1307_, v_k_1308_, v_rS_1309_);
lean_dec(v_rS_1309_);
lean_dec(v_k_1308_);
lean_dec(v_n_1307_);
lean_dec_ref(v_inst_1306_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__0(lean_object* v_toSemiring_1311_, lean_object* v_i_1312_, lean_object* v_rS_1313_, lean_object* v_k_1314_, lean_object* v_M_1315_, lean_object* v_j_1316_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_i_1312_, v___x_1320_);
v___x_1322_ = lean_nat_dec_eq(v___x_1321_, v_rS_1313_);
lean_dec(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v_j_1316_);
lean_dec(v_M_1315_);
lean_dec(v_i_1312_);
goto v___jp_1317_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_nat_add(v_rS_1313_, v_k_1314_);
v___x_1324_ = lean_nat_dec_eq(v_j_1316_, v___x_1323_);
lean_dec(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec(v_j_1316_);
lean_dec(v_M_1315_);
lean_dec(v_i_1312_);
goto v___jp_1317_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v_toSemiring_1311_);
v___x_1325_ = lean_apply_2(v_M_1315_, v_i_1312_, v_j_1316_);
return v___x_1325_;
}
}
v___jp_1317_:
{
lean_object* v___x_1318_; lean_object* v_toZero_1319_; 
v___x_1318_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_1311_);
v_toZero_1319_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_toZero_1319_);
lean_dec_ref(v___x_1318_);
return v_toZero_1319_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__0___boxed(lean_object* v_toSemiring_1326_, lean_object* v_i_1327_, lean_object* v_rS_1328_, lean_object* v_k_1329_, lean_object* v_M_1330_, lean_object* v_j_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = lp_tree_Formalism_L2_Col_offSum___redArg___lam__0(v_toSemiring_1326_, v_i_1327_, v_rS_1328_, v_k_1329_, v_M_1330_, v_j_1331_);
lean_dec(v_k_1329_);
lean_dec(v_rS_1328_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__1(lean_object* v_toSemiring_1333_, lean_object* v_rS_1334_, lean_object* v_k_1335_, lean_object* v_M_1336_, lean_object* v_toAddCommMonoid_1337_, lean_object* v___x_1338_, lean_object* v_i_1339_){
_start:
{
lean_object* v___f_1340_; lean_object* v___x_1341_; 
v___f_1340_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offSum___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1340_, 0, v_toSemiring_1333_);
lean_closure_set(v___f_1340_, 1, v_i_1339_);
lean_closure_set(v___f_1340_, 2, v_rS_1334_);
lean_closure_set(v___f_1340_, 3, v_k_1335_);
lean_closure_set(v___f_1340_, 4, v_M_1336_);
v___x_1341_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_1337_, v___x_1338_, v___f_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg___lam__1___boxed(lean_object* v_toSemiring_1342_, lean_object* v_rS_1343_, lean_object* v_k_1344_, lean_object* v_M_1345_, lean_object* v_toAddCommMonoid_1346_, lean_object* v___x_1347_, lean_object* v_i_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = lp_tree_Formalism_L2_Col_offSum___redArg___lam__1(v_toSemiring_1342_, v_rS_1343_, v_k_1344_, v_M_1345_, v_toAddCommMonoid_1346_, v___x_1347_, v_i_1348_);
lean_dec_ref(v_toAddCommMonoid_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___redArg(lean_object* v_inst_1350_, lean_object* v_n_1351_, lean_object* v_k_1352_, lean_object* v_rS_1353_, lean_object* v_M_1354_){
_start:
{
lean_object* v_toSemiring_1355_; lean_object* v_toAddCommMonoid_1356_; lean_object* v___x_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; 
v_toSemiring_1355_ = lean_ctor_get(v_inst_1350_, 0);
lean_inc_ref(v_toSemiring_1355_);
lean_dec_ref(v_inst_1350_);
v_toAddCommMonoid_1356_ = lean_ctor_get(v_toSemiring_1355_, 0);
lean_inc_ref_n(v_toAddCommMonoid_1356_, 2);
v___x_1357_ = l_List_finRange(v_n_1351_);
lean_inc(v___x_1357_);
v___f_1358_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offSum___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1358_, 0, v_toSemiring_1355_);
lean_closure_set(v___f_1358_, 1, v_rS_1353_);
lean_closure_set(v___f_1358_, 2, v_k_1352_);
lean_closure_set(v___f_1358_, 3, v_M_1354_);
lean_closure_set(v___f_1358_, 4, v_toAddCommMonoid_1356_);
lean_closure_set(v___f_1358_, 5, v___x_1357_);
v___x_1359_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_1356_, v___x_1357_, v___f_1358_);
lean_dec_ref(v_toAddCommMonoid_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum(lean_object* v_00_u03ba_1360_, lean_object* v_inst_1361_, lean_object* v_n_1362_, lean_object* v_k_1363_, lean_object* v_rS_1364_, lean_object* v_M_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lp_tree_Formalism_L2_Col_offSum___redArg(v_inst_1361_, v_n_1362_, v_k_1363_, v_rS_1364_, v_M_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___redArg___lam__0(lean_object* v_inst_1367_, lean_object* v_n_1368_, lean_object* v_k_1369_, lean_object* v_rS_1370_, lean_object* v_M_1371_){
_start:
{
lean_object* v_val_1372_; lean_object* v___x_1373_; lean_object* v_toFun_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_val_1372_ = lean_ctor_get(v_M_1371_, 0);
lean_inc(v_val_1372_);
lean_dec_ref(v_M_1371_);
v___x_1373_ = lean_obj_once(&lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_Col_supHom___redArg___lam__0___closed__0);
v_toFun_1374_ = lean_ctor_get(v___x_1373_, 0);
v___x_1375_ = lp_tree_Formalism_L2_Col_offSum___redArg(v_inst_1367_, v_n_1368_, v_k_1369_, v_rS_1370_, v_val_1372_);
lean_inc(v_toFun_1374_);
v___x_1376_ = lean_apply_1(v_toFun_1374_, v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___redArg(lean_object* v_inst_1377_, lean_object* v_n_1378_, lean_object* v_k_1379_, lean_object* v_rS_1380_){
_start:
{
lean_object* v___f_1381_; 
v___f_1381_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offHom___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1381_, 0, v_inst_1377_);
lean_closure_set(v___f_1381_, 1, v_n_1378_);
lean_closure_set(v___f_1381_, 2, v_k_1379_);
lean_closure_set(v___f_1381_, 3, v_rS_1380_);
return v___f_1381_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom(lean_object* v_00_u03ba_1382_, lean_object* v_inst_1383_, lean_object* v_n_1384_, lean_object* v_k_1385_, lean_object* v_rS_1386_){
_start:
{
lean_object* v___f_1387_; 
v___f_1387_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offHom___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1387_, 0, v_inst_1383_);
lean_closure_set(v___f_1387_, 1, v_n_1384_);
lean_closure_set(v___f_1387_, 2, v_k_1385_);
lean_closure_set(v___f_1387_, 3, v_rS_1386_);
return v___f_1387_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_SPsym___lam__0(lean_object* v_rS_1388_, lean_object* v_k_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_a_1390_, v___x_1391_);
v___x_1393_ = lean_nat_dec_eq(v___x_1392_, v_rS_1388_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_nat_add(v_rS_1388_, v_k_1389_);
v___x_1395_ = lean_nat_dec_eq(v___x_1392_, v___x_1394_);
lean_dec(v___x_1394_);
lean_dec(v___x_1392_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 1;
return v___x_1396_;
}
else
{
return v___x_1393_;
}
}
else
{
uint8_t v___x_1397_; 
lean_dec(v___x_1392_);
v___x_1397_ = 0;
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SPsym___lam__0___boxed(lean_object* v_rS_1398_, lean_object* v_k_1399_, lean_object* v_a_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = lp_tree_Formalism_L2_Col_SPsym___lam__0(v_rS_1398_, v_k_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec(v_k_1399_);
lean_dec(v_rS_1398_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SPsym(lean_object* v_n_1403_, lean_object* v_k_1404_, lean_object* v_rS_1405_){
_start:
{
lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___f_1406_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_SPsym___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1406_, 0, v_rS_1405_);
lean_closure_set(v___f_1406_, 1, v_k_1404_);
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_sub(v_n_1403_, v___x_1407_);
v___x_1409_ = l_List_range(v___x_1408_);
v___x_1410_ = lp_mathlib_Multiset_filter___redArg(v___f_1406_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_SPsym___boxed(lean_object* v_n_1411_, lean_object* v_k_1412_, lean_object* v_rS_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = lp_tree_Formalism_L2_Col_SPsym(v_n_1411_, v_k_1412_, v_rS_1413_);
lean_dec(v_n_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg___lam__0(lean_object* v___x_1415_, lean_object* v___f_1416_, lean_object* v___x_1417_, lean_object* v___f_1418_, lean_object* v___x_1419_, lean_object* v_m_1420_){
_start:
{
lean_object* v___x_1421_; lean_object* v_toMul_1422_; lean_object* v___x_1423_; lean_object* v_val_1424_; lean_object* v_inv_1425_; lean_object* v___x_1426_; lean_object* v_val_1427_; lean_object* v_inv_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v___x_1421_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_1415_);
v_toMul_1422_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_toMul_1422_);
lean_dec_ref(v___x_1421_);
lean_inc_ref(v_m_1420_);
v___x_1423_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_1416_, v___x_1417_, v_m_1420_);
v_val_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1424_);
v_inv_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc(v_inv_1425_);
lean_dec(v___x_1423_);
v___x_1426_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_1418_, v___x_1419_, v_m_1420_);
v_val_1427_ = lean_ctor_get(v___x_1426_, 0);
v_inv_1428_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v___x_1426_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_inv_1428_);
lean_inc(v_val_1427_);
lean_dec(v___x_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_inc(v_toMul_1422_);
v___x_1432_ = lean_apply_2(v_toMul_1422_, v_val_1424_, v_val_1427_);
v___x_1433_ = lean_apply_2(v_toMul_1422_, v_inv_1428_, v_inv_1425_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1433_);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg___lam__0___boxed(lean_object* v___x_1438_, lean_object* v___f_1439_, lean_object* v___x_1440_, lean_object* v___f_1441_, lean_object* v___x_1442_, lean_object* v_m_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = lp_tree_Formalism_L2_Col_chiSym___redArg___lam__0(v___x_1438_, v___f_1439_, v___x_1440_, v___f_1441_, v___x_1442_, v_m_1443_);
lean_dec_ref(v___x_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg(lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_00_u03c8_1447_, lean_object* v_n_1448_, lean_object* v_k_1449_, lean_object* v_rS_1450_){
_start:
{
lean_object* v_toCommRing_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; 
v_toCommRing_1451_ = lean_ctor_get(v_inst_1446_, 0);
v___x_1452_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_1451_);
lean_inc(v_rS_1450_);
lean_inc(v_k_1449_);
v___x_1453_ = lp_tree_Formalism_L2_Col_SPsym(v_n_1448_, v_k_1449_, v_rS_1450_);
lean_inc_n(v_n_1448_, 2);
lean_inc(v_00_u03c8_1447_);
lean_inc_ref_n(v_inst_1445_, 2);
v___x_1454_ = lp_tree_Formalism_L2_Col_supChar___redArg(v_inst_1445_, v_00_u03c8_1447_, v_n_1448_, v_n_1448_, v___x_1453_);
v___f_1455_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamGen___redArg___closed__0));
v___x_1456_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1445_);
v___x_1457_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_1456_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = lp_mathlib_Multiplicative_divInvMonoid___redArg(v___x_1457_);
v___x_1459_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_1458_, v_00_u03c8_1447_);
lean_dec_ref(v___x_1458_);
v___f_1460_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offHom___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1460_, 0, v_inst_1445_);
lean_closure_set(v___f_1460_, 1, v_n_1448_);
lean_closure_set(v___f_1460_, 2, v_k_1449_);
lean_closure_set(v___f_1460_, 3, v_rS_1450_);
v___f_1461_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_chiSym___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1461_, 0, v___x_1452_);
lean_closure_set(v___f_1461_, 1, v___f_1455_);
lean_closure_set(v___f_1461_, 2, v___x_1454_);
lean_closure_set(v___f_1461_, 3, v___f_1460_);
lean_closure_set(v___f_1461_, 4, v___x_1459_);
return v___f_1461_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg___boxed(lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_00_u03c8_1464_, lean_object* v_n_1465_, lean_object* v_k_1466_, lean_object* v_rS_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = lp_tree_Formalism_L2_Col_chiSym___redArg(v_inst_1462_, v_inst_1463_, v_00_u03c8_1464_, v_n_1465_, v_k_1466_, v_rS_1467_);
lean_dec_ref(v_inst_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym(lean_object* v_00_u03ba_1469_, lean_object* v_inst_1470_, lean_object* v_K_1471_, lean_object* v_inst_1472_, lean_object* v_00_u03c8_1473_, lean_object* v_n_1474_, lean_object* v_k_1475_, lean_object* v_rS_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = lp_tree_Formalism_L2_Col_chiSym___redArg(v_inst_1470_, v_inst_1472_, v_00_u03c8_1473_, v_n_1474_, v_k_1475_, v_rS_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___boxed(lean_object* v_00_u03ba_1478_, lean_object* v_inst_1479_, lean_object* v_K_1480_, lean_object* v_inst_1481_, lean_object* v_00_u03c8_1482_, lean_object* v_n_1483_, lean_object* v_k_1484_, lean_object* v_rS_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = lp_tree_Formalism_L2_Col_chiSym(v_00_u03ba_1478_, v_inst_1479_, v_K_1480_, v_inst_1481_, v_00_u03c8_1482_, v_n_1483_, v_k_1484_, v_rS_1485_);
lean_dec_ref(v_inst_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HQ(lean_object* v_00_u03ba_1487_, lean_object* v_inst_1488_, lean_object* v_n_1489_, lean_object* v_a_1490_, lean_object* v_b_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_box(0);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HQ___boxed(lean_object* v_00_u03ba_1493_, lean_object* v_inst_1494_, lean_object* v_n_1495_, lean_object* v_a_1496_, lean_object* v_b_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = lp_tree_Formalism_L2_Col_HQ(v_00_u03ba_1493_, v_inst_1494_, v_n_1495_, v_a_1496_, v_b_1497_);
lean_dec(v_b_1497_);
lean_dec(v_a_1496_);
lean_dec(v_n_1495_);
lean_dec_ref(v_inst_1494_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg___lam__0(lean_object* v_00_u03be_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_apply_1(v_00_u03be_1499_, v___y_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg___lam__0___boxed(lean_object* v_00_u03be_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = lp_tree_Formalism_L2_Col_lamQ___redArg___lam__0(v_00_u03be_1503_, v_x_1504_, v___y_1505_);
lean_dec(v_x_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg(lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_00_u03be_1509_, lean_object* v_n_1510_, lean_object* v_a_1511_, lean_object* v_b_1512_){
_start:
{
lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___f_1513_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_lamQ___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1513_, 0, v_00_u03be_1509_);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_b_1512_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = lp_tree_Formalism_L2_Col_detChar___redArg(v_inst_1507_, v_inst_1508_, v___f_1513_, v_n_1510_, v_a_1511_, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___redArg___boxed(lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_00_u03be_1519_, lean_object* v_n_1520_, lean_object* v_a_1521_, lean_object* v_b_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = lp_tree_Formalism_L2_Col_lamQ___redArg(v_inst_1517_, v_inst_1518_, v_00_u03be_1519_, v_n_1520_, v_a_1521_, v_b_1522_);
lean_dec_ref(v_inst_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ(lean_object* v_00_u03ba_1524_, lean_object* v_inst_1525_, lean_object* v_K_1526_, lean_object* v_inst_1527_, lean_object* v_00_u03be_1528_, lean_object* v_n_1529_, lean_object* v_a_1530_, lean_object* v_b_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lp_tree_Formalism_L2_Col_lamQ___redArg(v_inst_1525_, v_inst_1527_, v_00_u03be_1528_, v_n_1529_, v_a_1530_, v_b_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamQ___boxed(lean_object* v_00_u03ba_1533_, lean_object* v_inst_1534_, lean_object* v_K_1535_, lean_object* v_inst_1536_, lean_object* v_00_u03be_1537_, lean_object* v_n_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = lp_tree_Formalism_L2_Col_lamQ(v_00_u03ba_1533_, v_inst_1534_, v_K_1535_, v_inst_1536_, v_00_u03be_1537_, v_n_1538_, v_a_1539_, v_b_1540_);
lean_dec_ref(v_inst_1536_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj___redArg___lam__0(lean_object* v_i_1542_, lean_object* v_x_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_apply_1(v_x_1543_, v_i_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj___redArg(lean_object* v_i_1545_){
_start:
{
lean_object* v___f_1546_; 
v___f_1546_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_piProj___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1546_, 0, v_i_1545_);
return v___f_1546_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj(lean_object* v_00_u03b9_1547_, lean_object* v_G_1548_, lean_object* v_inst_1549_, lean_object* v_H_1550_, lean_object* v_i_1551_){
_start:
{
lean_object* v___f_1552_; 
v___f_1552_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_piProj___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1552_, 0, v_i_1551_);
return v___f_1552_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piProj___boxed(lean_object* v_00_u03b9_1553_, lean_object* v_G_1554_, lean_object* v_inst_1555_, lean_object* v_H_1556_, lean_object* v_i_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = lp_tree_Formalism_L2_Col_piProj(v_00_u03b9_1553_, v_G_1554_, v_inst_1555_, v_H_1556_, v_i_1557_);
lean_dec_ref(v_H_1556_);
lean_dec_ref(v_inst_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___redArg___lam__0(lean_object* v_lam_1559_, lean_object* v_i_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; 
lean_inc(v_i_1560_);
v___x_1562_ = lean_apply_1(v_lam_1559_, v_i_1560_);
v___f_1563_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_piProj___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1563_, 0, v_i_1560_);
v___x_1564_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_1563_, v___x_1562_, v___y_1561_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___redArg(lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v_lam_1567_){
_start:
{
lean_object* v_toCommRing_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_toMonoid_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_toCommRing_1568_ = lean_ctor_get(v_inst_1565_, 0);
v___x_1569_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_1568_);
v___x_1570_ = lp_mathlib_Units_instDivInvMonoid___redArg(v___x_1569_);
v_toMonoid_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_toMonoid_1571_);
lean_dec_ref(v___x_1570_);
v___f_1572_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_piChar___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1572_, 0, v_lam_1567_);
v___x_1573_ = lp_mathlib_MonoidHom_instCommMonoid___redArg(v_toMonoid_1571_);
v___x_1574_ = lp_mathlib_Finset_prod___redArg(v___x_1573_, v_inst_1566_, v___f_1572_);
lean_dec_ref(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___redArg___boxed(lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_lam_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = lp_tree_Formalism_L2_Col_piChar___redArg(v_inst_1575_, v_inst_1576_, v_lam_1577_);
lean_dec_ref(v_inst_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar(lean_object* v_K_1579_, lean_object* v_inst_1580_, lean_object* v_00_u03b9_1581_, lean_object* v_inst_1582_, lean_object* v_G_1583_, lean_object* v_inst_1584_, lean_object* v_H_1585_, lean_object* v_lam_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = lp_tree_Formalism_L2_Col_piChar___redArg(v_inst_1580_, v_inst_1582_, v_lam_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_piChar___boxed(lean_object* v_K_1588_, lean_object* v_inst_1589_, lean_object* v_00_u03b9_1590_, lean_object* v_inst_1591_, lean_object* v_G_1592_, lean_object* v_inst_1593_, lean_object* v_H_1594_, lean_object* v_lam_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = lp_tree_Formalism_L2_Col_piChar(v_K_1588_, v_inst_1589_, v_00_u03b9_1590_, v_inst_1591_, v_G_1592_, v_inst_1593_, v_H_1594_, v_lam_1595_);
lean_dec_ref(v_H_1594_);
lean_dec_ref(v_inst_1593_);
lean_dec_ref(v_inst_1589_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___redArg___lam__0(lean_object* v___x_1597_, lean_object* v_r_1598_, lean_object* v_n_1599_, lean_object* v_g_1600_, lean_object* v_w_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_82__overap_1604_; lean_object* v___x_1605_; 
v___x_1602_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_1597_, v_w_1601_);
v___x_1603_ = lean_apply_1(v_g_1600_, v_w_1601_);
v___x_82__overap_1604_ = lp_tree_Formalism_L2_Col_diagEmb___redArg(v___x_1602_, v_r_1598_, v_n_1599_);
v___x_1605_ = lean_apply_1(v___x_82__overap_1604_, v___x_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___redArg(lean_object* v_inst_1606_, lean_object* v_r_1607_, lean_object* v_n_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___f_1610_; 
v___x_1609_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_1606_);
v___f_1610_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1610_, 0, v___x_1609_);
lean_closure_set(v___f_1610_, 1, v_r_1607_);
lean_closure_set(v___f_1610_, 2, v_n_1608_);
return v___f_1610_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct(lean_object* v_E_1611_, lean_object* v_inst_1612_, lean_object* v_SG_1613_, lean_object* v_r_1614_, lean_object* v_n_1615_, lean_object* v_h_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___redArg(v_inst_1612_, v_r_1614_, v_n_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct___boxed(lean_object* v_E_1618_, lean_object* v_inst_1619_, lean_object* v_SG_1620_, lean_object* v_r_1621_, lean_object* v_n_1622_, lean_object* v_h_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = lp_tree_Formalism_L2_Col_diagonalEmbeddingProduct(v_E_1618_, v_inst_1619_, v_SG_1620_, v_r_1621_, v_n_1622_, v_h_1623_);
lean_dec(v_SG_1620_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UpperUnipotentProduct(lean_object* v_E_1625_, lean_object* v_inst_1626_, lean_object* v_SG_1627_, lean_object* v_r_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_box(0);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_UpperUnipotentProduct___boxed(lean_object* v_E_1630_, lean_object* v_inst_1631_, lean_object* v_SG_1632_, lean_object* v_r_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = lp_tree_Formalism_L2_Col_UpperUnipotentProduct(v_E_1630_, v_inst_1631_, v_SG_1632_, v_r_1633_);
lean_dec(v_r_1633_);
lean_dec(v_SG_1632_);
lean_dec_ref(v_inst_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg___lam__0(lean_object* v___x_1635_, lean_object* v_00_u03c8_1636_, lean_object* v_r_1637_, lean_object* v_w_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_46__overap_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lp_mathlib_Ideal_Quotient_ring___redArg(v___x_1635_, v_w_1638_);
v___x_1641_ = lean_apply_1(v_00_u03c8_1636_, v_w_1638_);
v___x_46__overap_1642_ = lp_tree_Formalism_L2_Col_psiU___redArg(v___x_1640_, v___x_1641_, v_r_1637_);
v___x_1643_ = lean_apply_1(v___x_46__overap_1642_, v___y_1639_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg(lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_SG_1646_, lean_object* v_00_u03c8_1647_, lean_object* v_r_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___f_1651_; lean_object* v___x_1652_; 
v___x_1649_ = lp_mathlib_Multiset_attach___redArg(v_SG_1646_);
v___x_1650_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_inst_1645_);
v___f_1651_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1651_, 0, v___x_1650_);
lean_closure_set(v___f_1651_, 1, v_00_u03c8_1647_);
lean_closure_set(v___f_1651_, 2, v_r_1648_);
v___x_1652_ = lp_tree_Formalism_L2_Col_piChar___redArg(v_inst_1644_, v___x_1649_, v___f_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg___boxed(lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_SG_1655_, lean_object* v_00_u03c8_1656_, lean_object* v_r_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg(v_inst_1653_, v_inst_1654_, v_SG_1655_, v_00_u03c8_1656_, v_r_1657_);
lean_dec_ref(v_inst_1653_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter(lean_object* v_K_1659_, lean_object* v_inst_1660_, lean_object* v_E_1661_, lean_object* v_inst_1662_, lean_object* v_SG_1663_, lean_object* v_00_u03c8_1664_, lean_object* v_r_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = lp_tree_Formalism_L2_Col_genericUnipotentCharacter___redArg(v_inst_1660_, v_inst_1662_, v_SG_1663_, v_00_u03c8_1664_, v_r_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_genericUnipotentCharacter___boxed(lean_object* v_K_1667_, lean_object* v_inst_1668_, lean_object* v_E_1669_, lean_object* v_inst_1670_, lean_object* v_SG_1671_, lean_object* v_00_u03c8_1672_, lean_object* v_r_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = lp_tree_Formalism_L2_Col_genericUnipotentCharacter(v_K_1667_, v_inst_1668_, v_E_1669_, v_inst_1670_, v_SG_1671_, v_00_u03c8_1672_, v_r_1673_);
lean_dec_ref(v_inst_1668_);
return v_res_1674_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Tuples(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Tuples(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
