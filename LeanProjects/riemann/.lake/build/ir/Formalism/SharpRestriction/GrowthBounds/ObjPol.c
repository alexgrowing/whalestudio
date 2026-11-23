// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.ObjPol
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Rat_mul___boxed(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_batteries_List_pwFilter___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_Module_End_instMul___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_npowBinRec_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lp_mathlib_List_elem___at___00List_diff___at___00Multiset_sub___at___00SSet_boundary_face_u03b9_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Fin_decLt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_erase___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Nat_multinomial_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_completeLattice___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Fin_natAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finsupp_prod___at___00Finsupp_multinomial_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_log(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_mathlib_List_diff___at___00Multiset_sub___at___00SSet_boundary_face_u03b9_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_multideg___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_multideg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_multideg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_G_expFact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_G_expFact___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_G_expFact___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fock___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cUnit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dUnit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dUnit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dUnit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOfL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOfL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOfL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOfL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_weightSp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_weightSp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dualWt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dualWt___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_rootW___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_rootW___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_rootW(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_rootW___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_deF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_deF___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_N0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_N0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Module_End_instMul___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_UZmon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_UZmon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Umon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Umon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_MQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_MQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Delta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Delta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_NablaSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_NablaSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_isoSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_isoSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_PPath_h___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_jointIsoSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_jointIsoSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_sumLetters___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_sumLetters(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pEnd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pEnd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_colH___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colH___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colH(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extOne(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_wedgeR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_wedgeR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_wedgeR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_contrR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_contrR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_contrR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_Ican___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ican___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_Ican___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ican___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ican(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tabCol(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plPart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plPart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plVar___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinI___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinI___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_G_joinI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_G_joinI___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_G_joinI___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_G_joinI___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_powC___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_powC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_powC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_multideg___redArg___lam__0(lean_object* v_m_1_, lean_object* v_i_2_, lean_object* v_c_3_){
_start:
{
lean_object* v_toFun_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_toFun_4_ = lean_ctor_get(v_m_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_m_1_);
if (v_isSharedCheck_12_ == 0)
{
lean_object* v_unused_13_; 
v_unused_13_ = lean_ctor_get(v_m_1_, 0);
lean_dec(v_unused_13_);
v___x_6_ = v_m_1_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_toFun_4_);
lean_dec(v_m_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v_c_3_);
lean_ctor_set(v___x_6_, 0, v_i_2_);
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_i_2_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v_c_3_);
v___x_9_ = v_reuseFailAlloc_11_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_1(v_toFun_4_, v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_multideg___redArg(lean_object* v_n_14_, lean_object* v_m_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_multideg___redArg___lam__0), 3, 2);
lean_closure_set(v___f_17_, 0, v_m_15_);
lean_closure_set(v___f_17_, 1, v_i_16_);
v___x_18_ = l_List_finRange(v_n_14_);
v___x_19_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_18_, v___f_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_multideg(lean_object* v_00_u03b9_20_, lean_object* v_n_21_, lean_object* v_m_22_, lean_object* v_i_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_tree_Formalism_MainNotions_G_multideg___redArg(v_n_21_, v_m_22_, v_i_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg___lam__0(lean_object* v_x_25_, lean_object* v_k_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_mathlib_Nat_factorialBinarySplitting(v_k_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg___lam__0___boxed(lean_object* v_x_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_MainNotions_G_expFact___redArg___lam__0(v_x_28_, v_k_29_);
lean_dec(v_k_29_);
lean_dec(v_x_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact___redArg(lean_object* v_m_32_){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; 
v___f_33_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_expFact___redArg___closed__0));
v___x_34_ = lp_mathlib_Finsupp_prod___at___00Finsupp_multinomial_spec__1___redArg(v_m_32_, v___f_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_expFact(lean_object* v_00_u03c3_35_, lean_object* v_m_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_Formalism_MainNotions_G_expFact___redArg(v_m_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fock___redArg___lam__0(lean_object* v_F_38_, lean_object* v_G_39_, lean_object* v_toMul_40_, lean_object* v_toNatCast_41_, lean_object* v_m_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_inc_ref_n(v_m_42_, 2);
v___x_43_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_42_, v_F_38_);
v___x_44_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_42_, v_G_39_);
lean_inc(v_toMul_40_);
v___x_45_ = lean_apply_2(v_toMul_40_, v___x_43_, v___x_44_);
v___x_46_ = lp_tree_Formalism_MainNotions_G_expFact___redArg(v_m_42_);
v___x_47_ = lean_apply_1(v_toNatCast_41_, v___x_46_);
v___x_48_ = lean_apply_2(v_toMul_40_, v___x_45_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fock___redArg(lean_object* v_inst_49_, lean_object* v_F_50_, lean_object* v_G_51_){
_start:
{
lean_object* v_toAddCommMonoid_52_; lean_object* v_support_53_; lean_object* v___x_54_; lean_object* v_toMul_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v_toNatCast_58_; lean_object* v___f_59_; lean_object* v___x_60_; 
v_toAddCommMonoid_52_ = lean_ctor_get(v_inst_49_, 0);
lean_inc_ref(v_toAddCommMonoid_52_);
v_support_53_ = lean_ctor_get(v_F_50_, 0);
lean_inc(v_support_53_);
lean_inc_ref(v_inst_49_);
v___x_54_ = lp_mathlib_instDistribOfSemiring___redArg(v_inst_49_);
v_toMul_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_toMul_55_);
lean_dec_ref(v___x_54_);
v___x_56_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_inst_49_);
v___x_57_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_56_);
v_toNatCast_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_toNatCast_58_);
lean_dec_ref(v___x_57_);
v___f_59_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_fock___redArg___lam__0), 5, 4);
lean_closure_set(v___f_59_, 0, v_F_50_);
lean_closure_set(v___f_59_, 1, v_G_51_);
lean_closure_set(v___f_59_, 2, v_toMul_55_);
lean_closure_set(v___f_59_, 3, v_toNatCast_58_);
v___x_60_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_52_, v_support_53_, v___f_59_);
lean_dec_ref(v_toAddCommMonoid_52_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fock(lean_object* v_R_61_, lean_object* v_inst_62_, lean_object* v_00_u03c3_63_, lean_object* v_F_64_, lean_object* v_G_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lp_tree_Formalism_MainNotions_G_fock___redArg(v_inst_62_, v_F_64_, v_G_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx___redArg(lean_object* v_n_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_sub(v_n_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx___redArg___boxed(lean_object* v_n_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_MainNotions_G_lastIdx___redArg(v_n_70_);
lean_dec(v_n_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx(lean_object* v_n_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_MainNotions_G_lastIdx___redArg(v_n_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lastIdx___boxed(lean_object* v_n_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_MainNotions_G_lastIdx(v_n_75_, v_inst_76_);
lean_dec(v_n_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf___redArg(lean_object* v_P_78_, lean_object* v_m_79_, lean_object* v_k_80_){
_start:
{
lean_object* v_toFun_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_toFun_81_ = lean_ctor_get(v_m_79_, 1);
lean_inc(v_toFun_81_);
lean_dec_ref(v_m_79_);
v___x_82_ = lean_apply_1(v_toFun_81_, v_k_80_);
v___x_83_ = lean_nat_mod(v___x_82_, v_P_78_);
lean_dec(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf___redArg___boxed(lean_object* v_P_84_, lean_object* v_m_85_, lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_MainNotions_G_digitOf___redArg(v_P_84_, v_m_85_, v_k_86_);
lean_dec(v_P_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf(lean_object* v_00_u03c3_88_, lean_object* v_P_89_, lean_object* v_m_90_, lean_object* v_k_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_tree_Formalism_MainNotions_G_digitOf___redArg(v_P_89_, v_m_90_, v_k_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOf___boxed(lean_object* v_00_u03c3_93_, lean_object* v_P_94_, lean_object* v_m_95_, lean_object* v_k_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_Formalism_MainNotions_G_digitOf(v_00_u03c3_93_, v_P_94_, v_m_95_, v_k_96_);
lean_dec(v_P_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf___redArg(lean_object* v_P_98_, lean_object* v_m_99_, lean_object* v_k_100_){
_start:
{
lean_object* v_toFun_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_toFun_101_ = lean_ctor_get(v_m_99_, 1);
lean_inc(v_toFun_101_);
lean_dec_ref(v_m_99_);
v___x_102_ = lean_apply_1(v_toFun_101_, v_k_100_);
v___x_103_ = lean_nat_div(v___x_102_, v_P_98_);
lean_dec(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf___redArg___boxed(lean_object* v_P_104_, lean_object* v_m_105_, lean_object* v_k_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_tree_Formalism_MainNotions_G_coarseOf___redArg(v_P_104_, v_m_105_, v_k_106_);
lean_dec(v_P_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf(lean_object* v_00_u03c3_108_, lean_object* v_P_109_, lean_object* v_m_110_, lean_object* v_k_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_tree_Formalism_MainNotions_G_coarseOf___redArg(v_P_109_, v_m_110_, v_k_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOf___boxed(lean_object* v_00_u03c3_113_, lean_object* v_P_114_, lean_object* v_m_115_, lean_object* v_k_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_tree_Formalism_MainNotions_G_coarseOf(v_00_u03c3_113_, v_P_114_, v_m_115_, v_k_116_);
lean_dec(v_P_114_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cUnit(lean_object* v_P_118_, lean_object* v_n_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_120_ = lean_nat_mul(v_P_118_, v_n_119_);
v___x_121_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_120_);
lean_dec(v___x_120_);
v___x_122_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_121_);
v___x_123_ = lp_mathlib_Nat_factorialBinarySplitting(v_P_118_);
v___x_124_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_123_);
v___x_125_ = l_Rat_pow(v___x_124_, v_n_119_);
v___x_126_ = lp_mathlib_Nat_factorialBinarySplitting(v_n_119_);
v___x_127_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_126_);
v___x_128_ = l_Rat_mul(v___x_125_, v___x_127_);
lean_dec_ref(v___x_125_);
v___x_129_ = l_Rat_div(v___x_122_, v___x_128_);
lean_dec_ref(v___x_122_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cUnit___boxed(lean_object* v_P_130_, lean_object* v_n_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = lp_tree_Formalism_MainNotions_G_cUnit(v_P_130_, v_n_131_);
lean_dec(v_n_131_);
lean_dec(v_P_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dUnit___lam__0(lean_object* v___x_133_, lean_object* v_P_134_, lean_object* v_n_135_, lean_object* v_y_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_137_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_133_);
v___x_138_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_P_134_);
v___x_139_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_n_135_);
v___x_140_ = l_Rat_mul(v___x_138_, v___x_139_);
lean_dec_ref(v___x_138_);
v___x_141_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_y_136_);
v___x_142_ = l_Rat_div(v___x_140_, v___x_141_);
lean_dec_ref(v___x_140_);
v___x_143_ = l_Rat_add(v___x_137_, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0(lean_object* v_s_147_){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___f_148_ = ((lean_object*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__0));
v___x_149_ = lean_obj_once(&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__1, &lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__1_once, _init_lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0___closed__1);
v___x_150_ = l_List_foldrTR___redArg(v___f_148_, v___x_149_, v_s_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0___redArg(lean_object* v_s_151_, lean_object* v_f_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lp_mathlib_Multiset_map___redArg(v_f_152_, v_s_151_);
v___x_154_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0_spec__0(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dUnit(lean_object* v_P_155_, lean_object* v_n_156_, lean_object* v_rho_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v___f_159_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_dUnit___lam__0), 4, 3);
lean_closure_set(v___f_159_, 0, v___x_158_);
lean_closure_set(v___f_159_, 1, v_P_155_);
lean_closure_set(v___f_159_, 2, v_n_156_);
v___x_160_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_158_, v_rho_157_);
v___x_161_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0___redArg(v___x_160_, v___f_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dUnit___boxed(lean_object* v_P_162_, lean_object* v_n_163_, lean_object* v_rho_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lp_tree_Formalism_MainNotions_G_dUnit(v_P_162_, v_n_163_, v_rho_164_);
lean_dec(v_rho_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0(lean_object* v_00_u03b9_166_, lean_object* v_s_167_, lean_object* v_f_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_G_dUnit_spec__0___redArg(v_s_167_, v_f_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOfL___redArg(lean_object* v_P_170_, lean_object* v_m_171_, lean_object* v_k_172_){
_start:
{
lean_object* v_toFun_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_toFun_173_ = lean_ctor_get(v_m_171_, 1);
lean_inc(v_toFun_173_);
lean_dec_ref(v_m_171_);
lean_inc(v_k_172_);
v___x_174_ = lean_apply_1(v_toFun_173_, v_k_172_);
v___x_175_ = lean_apply_1(v_P_170_, v_k_172_);
v___x_176_ = lean_nat_mod(v___x_174_, v___x_175_);
lean_dec(v___x_175_);
lean_dec(v___x_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_digitOfL(lean_object* v_00_u03c3_177_, lean_object* v_P_178_, lean_object* v_m_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lp_tree_Formalism_MainNotions_G_digitOfL___redArg(v_P_178_, v_m_179_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOfL___redArg(lean_object* v_P_182_, lean_object* v_m_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_toFun_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_toFun_185_ = lean_ctor_get(v_m_183_, 1);
lean_inc(v_toFun_185_);
lean_dec_ref(v_m_183_);
lean_inc(v_k_184_);
v___x_186_ = lean_apply_1(v_toFun_185_, v_k_184_);
v___x_187_ = lean_apply_1(v_P_182_, v_k_184_);
v___x_188_ = lean_nat_div(v___x_186_, v___x_187_);
lean_dec(v___x_187_);
lean_dec(v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_coarseOfL(lean_object* v_00_u03c3_189_, lean_object* v_P_190_, lean_object* v_m_191_, lean_object* v_k_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lp_tree_Formalism_MainNotions_G_coarseOfL___redArg(v_P_190_, v_m_191_, v_k_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_weightSp(lean_object* v_n_194_, lean_object* v_K_195_, lean_object* v_V_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_E_200_, lean_object* v_mu_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_weightSp___boxed(lean_object* v_n_203_, lean_object* v_K_204_, lean_object* v_V_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_E_209_, lean_object* v_mu_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_Formalism_MainNotions_G_weightSp(v_n_203_, v_K_204_, v_V_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_E_209_, v_mu_210_);
lean_dec_ref(v_mu_210_);
lean_dec(v_E_209_);
lean_dec(v_inst_208_);
lean_dec_ref(v_inst_207_);
lean_dec_ref(v_inst_206_);
lean_dec(v_n_203_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dualWt(lean_object* v_n_212_, lean_object* v_lam_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_a_214_, v___x_215_);
v___x_217_ = lean_nat_sub(v_n_212_, v___x_216_);
lean_dec(v___x_216_);
v___x_218_ = lean_apply_1(v_lam_213_, v___x_217_);
v___x_219_ = lean_int_neg(v___x_218_);
lean_dec(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_dualWt___boxed(lean_object* v_n_220_, lean_object* v_lam_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_tree_Formalism_MainNotions_G_dualWt(v_n_220_, v_lam_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec(v_n_220_);
return v_res_223_;
}
}
static lean_object* _init_lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_nat_to_int(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0(lean_object* v_x_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___closed__0, &lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___closed__0_once, _init_lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___closed__0);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___lam__0(v_x_228_);
lean_dec(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg(lean_object* v_i_231_, lean_object* v_x_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___f_234_; lean_object* v___x_235_; 
v___f_234_ = ((lean_object*)(lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___closed__0));
v___x_235_ = lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(v___f_234_, v_i_231_, v_x_232_, v_a_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg___boxed(lean_object* v_i_236_, lean_object* v_x_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg(v_i_236_, v_x_237_, v_a_238_);
lean_dec(v_x_237_);
lean_dec(v_i_236_);
return v_res_239_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_G_rootW___closed__0(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_to_int(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_rootW(lean_object* v_n_242_, lean_object* v_a_243_, lean_object* v_b_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_rootW___closed__0, &lp_tree_Formalism_MainNotions_G_rootW___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_rootW___closed__0);
lean_inc(v_a_245_);
v___x_247_ = lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg(v_a_243_, v___x_246_, v_a_245_);
v___x_248_ = lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg(v_b_244_, v___x_246_, v_a_245_);
v___x_249_ = lean_int_sub(v___x_247_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v___x_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_rootW___boxed(lean_object* v_n_250_, lean_object* v_a_251_, lean_object* v_b_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = lp_tree_Formalism_MainNotions_G_rootW(v_n_250_, v_a_251_, v_b_252_, v_a_253_);
lean_dec(v_b_252_);
lean_dec(v_a_251_);
lean_dec(v_n_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0(lean_object* v_n_255_, lean_object* v_i_256_, lean_object* v_x_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___redArg(v_i_256_, v_x_257_, v_a_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0___boxed(lean_object* v_n_260_, lean_object* v_i_261_, lean_object* v_x_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = lp_tree_Pi_single___at___00Formalism_MainNotions_G_rootW_spec__0(v_n_260_, v_i_261_, v_x_262_, v_a_263_);
lean_dec(v_x_262_);
lean_dec(v_i_261_);
lean_dec(v_n_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt___redArg(lean_object* v_n_265_, lean_object* v_lam_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_nat_mod(v___x_267_, v_n_265_);
lean_inc_ref(v_lam_266_);
v___x_269_ = lean_apply_1(v_lam_266_, v___x_268_);
v___x_270_ = lp_tree_Formalism_MainNotions_G_lastIdx___redArg(v_n_265_);
v___x_271_ = lean_apply_1(v_lam_266_, v___x_270_);
v___x_272_ = lean_int_sub(v___x_269_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_269_);
v___x_273_ = l_Int_toNat(v___x_272_);
lean_dec(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt___redArg___boxed(lean_object* v_n_274_, lean_object* v_lam_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = lp_tree_Formalism_MainNotions_G_ellWt___redArg(v_n_274_, v_lam_275_);
lean_dec(v_n_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt(lean_object* v_n_277_, lean_object* v_inst_278_, lean_object* v_lam_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lp_tree_Formalism_MainNotions_G_ellWt___redArg(v_n_277_, v_lam_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ellWt___boxed(lean_object* v_n_281_, lean_object* v_inst_282_, lean_object* v_lam_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_tree_Formalism_MainNotions_G_ellWt(v_n_281_, v_inst_282_, v_lam_283_);
lean_dec(v_n_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_deF(lean_object* v_p_285_, lean_object* v_n_286_, lean_object* v_k_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_nat_add(v_k_287_, v_n_286_);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_sub(v___x_288_, v___x_289_);
lean_dec(v___x_288_);
v___x_291_ = lp_mathlib_Nat_log(v_p_285_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_deF___boxed(lean_object* v_p_292_, lean_object* v_n_293_, lean_object* v_k_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = lp_tree_Formalism_MainNotions_G_deF(v_p_292_, v_n_293_, v_k_294_);
lean_dec(v_k_294_);
lean_dec(v_n_293_);
lean_dec(v_p_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_N0(lean_object* v_n_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_sub(v_n_296_, v___x_297_);
v___x_299_ = lean_nat_mul(v_n_296_, v___x_298_);
lean_dec(v___x_298_);
v___x_300_ = lean_nat_shiftr(v___x_299_, v___x_297_);
lean_dec(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_N0___boxed(lean_object* v_n_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = lp_tree_Formalism_MainNotions_G_N0(v_n_301_);
lean_dec(v_n_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg___lam__0(lean_object* v___f_303_, lean_object* v_k_304_, lean_object* v___f_305_, lean_object* v___x_306_, lean_object* v_inst_307_, lean_object* v___x_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_339__overap_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_339__overap_310_ = lp_mathlib_npowBinRec_go___redArg(v___f_303_, v_k_304_, v___f_305_, v___x_306_);
v___x_311_ = lean_apply_1(v___x_339__overap_310_, v___y_309_);
v___x_312_ = lean_apply_2(v_inst_307_, v___x_308_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg___lam__0___boxed(lean_object* v___f_313_, lean_object* v_k_314_, lean_object* v___f_315_, lean_object* v___x_316_, lean_object* v_inst_317_, lean_object* v___x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = lp_tree_Formalism_MainNotions_G_divPowE___redArg___lam__0(v___f_313_, v_k_314_, v___f_315_, v___x_316_, v_inst_317_, v___x_318_, v___y_319_);
lean_dec(v_k_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___redArg(lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_E_325_, lean_object* v_a_326_, lean_object* v_b_327_, lean_object* v_k_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_toInv_333_; lean_object* v___x_334_; lean_object* v_toRing_335_; lean_object* v___x_336_; lean_object* v_toAddMonoidWithOne_337_; lean_object* v_toNatCast_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___f_345_; 
v___x_329_ = lp_mathlib_Field_toSemifield___redArg(v_inst_323_);
v___x_330_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_329_);
lean_dec_ref(v___x_329_);
v___x_331_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_330_);
v___x_332_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_331_);
lean_dec_ref(v___x_331_);
v_toInv_333_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_toInv_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_323_);
v_toRing_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc_ref(v_toRing_335_);
lean_dec_ref(v___x_334_);
v___x_336_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_335_);
v_toAddMonoidWithOne_337_ = lean_ctor_get(v___x_336_, 1);
lean_inc_ref(v_toAddMonoidWithOne_337_);
lean_dec_ref(v___x_336_);
v_toNatCast_338_ = lean_ctor_get(v_toAddMonoidWithOne_337_, 0);
lean_inc(v_toNatCast_338_);
lean_dec_ref(v_toAddMonoidWithOne_337_);
v___x_339_ = lp_mathlib_Nat_factorialBinarySplitting(v_k_328_);
v___x_340_ = lean_apply_1(v_toNatCast_338_, v___x_339_);
v___x_341_ = lean_apply_1(v_toInv_333_, v___x_340_);
v___x_342_ = lean_apply_2(v_E_325_, v_a_326_, v_b_327_);
v___f_343_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__0));
v___f_344_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__1));
v___f_345_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_345_, 0, v___f_343_);
lean_closure_set(v___f_345_, 1, v_k_328_);
lean_closure_set(v___f_345_, 2, v___f_344_);
lean_closure_set(v___f_345_, 3, v___x_342_);
lean_closure_set(v___f_345_, 4, v_inst_324_);
lean_closure_set(v___f_345_, 5, v___x_341_);
return v___f_345_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE(lean_object* v_n_346_, lean_object* v_K_347_, lean_object* v_V_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_E_352_, lean_object* v_a_353_, lean_object* v_b_354_, lean_object* v_k_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lp_tree_Formalism_MainNotions_G_divPowE___redArg(v_inst_349_, v_inst_351_, v_E_352_, v_a_353_, v_b_354_, v_k_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_divPowE___boxed(lean_object* v_n_357_, lean_object* v_K_358_, lean_object* v_V_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_E_363_, lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v_k_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = lp_tree_Formalism_MainNotions_G_divPowE(v_n_357_, v_K_358_, v_V_359_, v_inst_360_, v_inst_361_, v_inst_362_, v_E_363_, v_a_364_, v_b_365_, v_k_366_);
lean_dec_ref(v_inst_361_);
lean_dec(v_n_357_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__0(lean_object* v_toNatCast_368_, lean_object* v_E_369_, lean_object* v_a_370_, lean_object* v_inst_371_, lean_object* v_toSub_372_, lean_object* v_j_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = lean_apply_1(v_toNatCast_368_, v_j_373_);
lean_inc(v___y_374_);
lean_inc(v_a_370_);
v___x_376_ = lean_apply_3(v_E_369_, v_a_370_, v_a_370_, v___y_374_);
v___x_377_ = lean_apply_2(v_inst_371_, v___x_375_, v___y_374_);
v___x_378_ = lean_apply_2(v_toSub_372_, v___x_376_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__1(lean_object* v___f_379_, lean_object* v___f_380_, lean_object* v___x_381_, lean_object* v_inst_382_, lean_object* v___x_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_542__overap_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_542__overap_385_ = l_List_prod___redArg(v___f_379_, v___f_380_, v___x_381_);
v___x_386_ = lean_apply_1(v___x_542__overap_385_, v___y_384_);
v___x_387_ = lean_apply_2(v_inst_382_, v___x_383_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__1___boxed(lean_object* v___f_388_, lean_object* v___f_389_, lean_object* v___x_390_, lean_object* v_inst_391_, lean_object* v___x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__1(v___f_388_, v___f_389_, v___x_390_, v_inst_391_, v___x_392_, v___y_393_);
lean_dec(v___f_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___redArg(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_E_398_, lean_object* v_a_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___x_401_; lean_object* v_toSub_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_toInv_406_; lean_object* v___x_407_; lean_object* v_toRing_408_; lean_object* v___x_409_; lean_object* v_toAddMonoidWithOne_410_; lean_object* v_toNatCast_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; 
v___x_401_ = lp_mathlib_Field_toSemifield___redArg(v_inst_395_);
v_toSub_402_ = lean_ctor_get(v_inst_396_, 2);
lean_inc(v_toSub_402_);
lean_dec_ref(v_inst_396_);
v___x_403_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_401_);
lean_dec_ref(v___x_401_);
v___x_404_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_403_);
v___x_405_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_404_);
lean_dec_ref(v___x_404_);
v_toInv_406_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_toInv_406_);
lean_dec_ref(v___x_405_);
v___x_407_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_395_);
v_toRing_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_toRing_408_);
lean_dec_ref(v___x_407_);
v___x_409_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_408_);
v_toAddMonoidWithOne_410_ = lean_ctor_get(v___x_409_, 1);
lean_inc_ref(v_toAddMonoidWithOne_410_);
lean_dec_ref(v___x_409_);
v_toNatCast_411_ = lean_ctor_get(v_toAddMonoidWithOne_410_, 0);
lean_inc_n(v_toNatCast_411_, 2);
lean_dec_ref(v_toAddMonoidWithOne_410_);
lean_inc(v_inst_397_);
v___f_412_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__0), 7, 5);
lean_closure_set(v___f_412_, 0, v_toNatCast_411_);
lean_closure_set(v___f_412_, 1, v_E_398_);
lean_closure_set(v___f_412_, 2, v_a_399_);
lean_closure_set(v___f_412_, 3, v_inst_397_);
lean_closure_set(v___f_412_, 4, v_toSub_402_);
v___x_413_ = lp_mathlib_Nat_factorialBinarySplitting(v_k_400_);
v___x_414_ = lean_apply_1(v_toNatCast_411_, v___x_413_);
v___x_415_ = lean_apply_1(v_toInv_406_, v___x_414_);
v___f_416_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__0));
v___f_417_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__1));
v___x_418_ = l_List_range(v_k_400_);
v___x_419_ = lean_box(0);
v___x_420_ = l_List_mapTR_loop___redArg(v___f_412_, v___x_418_, v___x_419_);
v___f_421_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_binomE___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_421_, 0, v___f_416_);
lean_closure_set(v___f_421_, 1, v___f_417_);
lean_closure_set(v___f_421_, 2, v___x_420_);
lean_closure_set(v___f_421_, 3, v_inst_397_);
lean_closure_set(v___f_421_, 4, v___x_415_);
return v___f_421_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE(lean_object* v_n_422_, lean_object* v_K_423_, lean_object* v_V_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_E_428_, lean_object* v_a_429_, lean_object* v_k_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lp_tree_Formalism_MainNotions_G_binomE___redArg(v_inst_425_, v_inst_426_, v_inst_427_, v_E_428_, v_a_429_, v_k_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_binomE___boxed(lean_object* v_n_432_, lean_object* v_K_433_, lean_object* v_V_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_E_438_, lean_object* v_a_439_, lean_object* v_k_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = lp_tree_Formalism_MainNotions_G_binomE(v_n_432_, v_K_433_, v_V_434_, v_inst_435_, v_inst_436_, v_inst_437_, v_E_438_, v_a_439_, v_k_440_);
lean_dec(v_n_432_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_UZmon(lean_object* v_n_442_, lean_object* v_K_443_, lean_object* v_V_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_E_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_box(0);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_UZmon___boxed(lean_object* v_n_450_, lean_object* v_K_451_, lean_object* v_V_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_E_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = lp_tree_Formalism_MainNotions_G_UZmon(v_n_450_, v_K_451_, v_V_452_, v_inst_453_, v_inst_454_, v_inst_455_, v_E_456_);
lean_dec(v_E_456_);
lean_dec(v_inst_455_);
lean_dec_ref(v_inst_454_);
lean_dec_ref(v_inst_453_);
lean_dec(v_n_450_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Umon(lean_object* v_n_458_, lean_object* v_K_459_, lean_object* v_V_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_E_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Umon___boxed(lean_object* v_n_466_, lean_object* v_K_467_, lean_object* v_V_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_E_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = lp_tree_Formalism_MainNotions_G_Umon(v_n_466_, v_K_467_, v_V_468_, v_inst_469_, v_inst_470_, v_inst_471_, v_E_472_);
lean_dec(v_E_472_);
lean_dec(v_inst_471_);
lean_dec_ref(v_inst_470_);
lean_dec_ref(v_inst_469_);
lean_dec(v_n_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_MQ(lean_object* v_K_474_, lean_object* v_V_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_O_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_M_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_box(0);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_MQ___boxed(lean_object* v_K_486_, lean_object* v_V_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_O_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_M_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = lp_tree_Formalism_MainNotions_G_MQ(v_K_486_, v_V_487_, v_inst_488_, v_inst_489_, v_inst_490_, v_O_491_, v_inst_492_, v_inst_493_, v_inst_494_, v_inst_495_, v_M_496_);
lean_dec_ref(v_inst_494_);
lean_dec(v_inst_493_);
lean_dec_ref(v_inst_492_);
lean_dec(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec_ref(v_inst_488_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Delta(lean_object* v_n_498_, lean_object* v_K_499_, lean_object* v_V_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_O_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_E_509_, lean_object* v_v_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_box(0);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Delta___boxed(lean_object* v_n_512_, lean_object* v_K_513_, lean_object* v_V_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_O_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_E_523_, lean_object* v_v_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = lp_tree_Formalism_MainNotions_G_Delta(v_n_512_, v_K_513_, v_V_514_, v_inst_515_, v_inst_516_, v_inst_517_, v_O_518_, v_inst_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_E_523_, v_v_524_);
lean_dec(v_v_524_);
lean_dec(v_E_523_);
lean_dec_ref(v_inst_521_);
lean_dec(v_inst_520_);
lean_dec_ref(v_inst_519_);
lean_dec(v_inst_517_);
lean_dec_ref(v_inst_516_);
lean_dec_ref(v_inst_515_);
lean_dec(v_n_512_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts___redArg(lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_toSemiring_531_; lean_object* v_toAddMonoid_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_toSupSet_535_; lean_object* v___x_536_; 
v___x_529_ = lp_mathlib_Field_toSemifield___redArg(v_inst_526_);
v___x_530_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_529_);
v_toSemiring_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_toSemiring_531_);
lean_dec_ref(v___x_530_);
v_toAddMonoid_532_ = lean_ctor_get(v_inst_527_, 0);
v___x_533_ = lp_mathlib_Submodule_completeLattice___redArg(v_toSemiring_531_, v_toAddMonoid_532_, v_inst_528_);
lean_dec_ref(v_toSemiring_531_);
v___x_534_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_533_);
v_toSupSet_535_ = lean_ctor_get(v___x_534_, 1);
lean_inc(v_toSupSet_535_);
lean_dec_ref(v___x_534_);
v___x_536_ = lean_apply_1(v_toSupSet_535_, lean_box(0));
return v___x_536_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts___redArg___boxed(lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_inst_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = lp_tree_Formalism_MainNotions_G_otherWts___redArg(v_inst_537_, v_inst_538_, v_inst_539_);
lean_dec(v_inst_539_);
lean_dec_ref(v_inst_538_);
lean_dec_ref(v_inst_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts(lean_object* v_n_541_, lean_object* v_K_542_, lean_object* v_V_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_E_547_, lean_object* v_lam_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lp_tree_Formalism_MainNotions_G_otherWts___redArg(v_inst_544_, v_inst_545_, v_inst_546_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_otherWts___boxed(lean_object* v_n_550_, lean_object* v_K_551_, lean_object* v_V_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_E_556_, lean_object* v_lam_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = lp_tree_Formalism_MainNotions_G_otherWts(v_n_550_, v_K_551_, v_V_552_, v_inst_553_, v_inst_554_, v_inst_555_, v_E_556_, v_lam_557_);
lean_dec_ref(v_lam_557_);
lean_dec(v_E_556_);
lean_dec(v_inst_555_);
lean_dec_ref(v_inst_554_);
lean_dec_ref(v_inst_553_);
lean_dec(v_n_550_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_NablaSub(lean_object* v_n_559_, lean_object* v_K_560_, lean_object* v_V_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_O_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_E_570_, lean_object* v_lam_571_, lean_object* v_v_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_box(0);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_NablaSub___boxed(lean_object* v_n_574_, lean_object* v_K_575_, lean_object* v_V_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_O_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_E_585_, lean_object* v_lam_586_, lean_object* v_v_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = lp_tree_Formalism_MainNotions_G_NablaSub(v_n_574_, v_K_575_, v_V_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_O_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_inst_584_, v_E_585_, v_lam_586_, v_v_587_);
lean_dec(v_v_587_);
lean_dec_ref(v_lam_586_);
lean_dec(v_E_585_);
lean_dec_ref(v_inst_583_);
lean_dec(v_inst_582_);
lean_dec_ref(v_inst_581_);
lean_dec(v_inst_579_);
lean_dec_ref(v_inst_578_);
lean_dec_ref(v_inst_577_);
lean_dec(v_n_574_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_isoSub(lean_object* v_n_589_, lean_object* v_K_590_, lean_object* v_V_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_E_595_, lean_object* v_lam_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_isoSub___boxed(lean_object* v_n_598_, lean_object* v_K_599_, lean_object* v_V_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_E_604_, lean_object* v_lam_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = lp_tree_Formalism_MainNotions_G_isoSub(v_n_598_, v_K_599_, v_V_600_, v_inst_601_, v_inst_602_, v_inst_603_, v_E_604_, v_lam_605_);
lean_dec_ref(v_lam_605_);
lean_dec(v_E_604_);
lean_dec(v_inst_603_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_inst_601_);
lean_dec(v_n_598_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_PPath_h___redArg___lam__0(lean_object* v_P_607_, lean_object* v_i_608_, lean_object* v_c_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_apply_2(v_P_607_, v_i_608_, v_a_610_);
v___x_612_ = lean_int_dec_le(v_c_609_, v___x_611_);
lean_dec(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h___redArg___lam__0___boxed(lean_object* v_P_613_, lean_object* v_i_614_, lean_object* v_c_615_, lean_object* v_a_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = lp_tree_Formalism_MainNotions_G_PPath_h___redArg___lam__0(v_P_613_, v_i_614_, v_c_615_, v_a_616_);
lean_dec(v_c_615_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h___redArg(lean_object* v_n_619_, lean_object* v_P_620_, lean_object* v_i_621_, lean_object* v_c_622_){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___f_623_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_PPath_h___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_623_, 0, v_P_620_);
lean_closure_set(v___f_623_, 1, v_i_621_);
lean_closure_set(v___f_623_, 2, v_c_622_);
v___x_624_ = l_List_finRange(v_n_619_);
v___x_625_ = lp_mathlib_Multiset_filter___redArg(v___f_623_, v___x_624_);
v___x_626_ = l_List_lengthTR___redArg(v___x_625_);
lean_dec(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h(lean_object* v_n_627_, lean_object* v_N_628_, lean_object* v_LL_629_, lean_object* v_B_630_, lean_object* v_P_631_, lean_object* v_i_632_, lean_object* v_c_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lp_tree_Formalism_MainNotions_G_PPath_h___redArg(v_n_627_, v_P_631_, v_i_632_, v_c_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_PPath_h___boxed(lean_object* v_n_635_, lean_object* v_N_636_, lean_object* v_LL_637_, lean_object* v_B_638_, lean_object* v_P_639_, lean_object* v_i_640_, lean_object* v_c_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = lp_tree_Formalism_MainNotions_G_PPath_h(v_n_635_, v_N_636_, v_LL_637_, v_B_638_, v_P_639_, v_i_640_, v_c_641_);
lean_dec_ref(v_B_638_);
lean_dec_ref(v_LL_637_);
lean_dec(v_N_636_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus___redArg(lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_toSemiring_648_; lean_object* v_toAddMonoid_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_toSupSet_652_; lean_object* v___x_653_; 
v___x_646_ = lp_mathlib_Field_toSemifield___redArg(v_inst_643_);
v___x_647_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_646_);
v_toSemiring_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_toSemiring_648_);
lean_dec_ref(v___x_647_);
v_toAddMonoid_649_ = lean_ctor_get(v_inst_644_, 0);
v___x_650_ = lp_mathlib_Submodule_completeLattice___redArg(v_toSemiring_648_, v_toAddMonoid_649_, v_inst_645_);
lean_dec_ref(v_toSemiring_648_);
v___x_651_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_650_);
v_toSupSet_652_ = lean_ctor_get(v___x_651_, 1);
lean_inc(v_toSupSet_652_);
lean_dec_ref(v___x_651_);
v___x_653_ = lean_apply_1(v_toSupSet_652_, lean_box(0));
return v___x_653_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus___redArg___boxed(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = lp_tree_Formalism_MainNotions_G_nMinus___redArg(v_inst_654_, v_inst_655_, v_inst_656_);
lean_dec(v_inst_656_);
lean_dec_ref(v_inst_655_);
lean_dec_ref(v_inst_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus(lean_object* v_n_658_, lean_object* v_K_659_, lean_object* v_V_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_E_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lp_tree_Formalism_MainNotions_G_nMinus___redArg(v_inst_661_, v_inst_662_, v_inst_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nMinus___boxed(lean_object* v_n_666_, lean_object* v_K_667_, lean_object* v_V_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_E_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = lp_tree_Formalism_MainNotions_G_nMinus(v_n_666_, v_K_667_, v_V_668_, v_inst_669_, v_inst_670_, v_inst_671_, v_E_672_);
lean_dec(v_E_672_);
lean_dec(v_inst_671_);
lean_dec_ref(v_inst_670_);
lean_dec_ref(v_inst_669_);
lean_dec(v_n_666_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___redArg___lam__0(lean_object* v_toNeg_674_, lean_object* v_toOne_675_, lean_object* v_toNPow_676_, lean_object* v_mu_677_, lean_object* v_a_678_, lean_object* v_b_679_, lean_object* v_toNatCast_680_, lean_object* v_toDiv_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_E_684_, lean_object* v_k_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_687_ = lean_apply_1(v_toNeg_674_, v_toOne_675_);
lean_inc_n(v_k_685_, 2);
v___x_688_ = lean_apply_2(v_toNPow_676_, v_k_685_, v___x_687_);
lean_inc_ref(v_mu_677_);
lean_inc_n(v_a_678_, 3);
v___x_689_ = lean_apply_1(v_mu_677_, v_a_678_);
lean_inc_n(v_b_679_, 3);
v___x_690_ = lean_apply_1(v_mu_677_, v_b_679_);
v___x_691_ = lean_int_sub(v___x_689_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_nat_to_int(v_b_679_);
v___x_693_ = lean_nat_to_int(v_a_678_);
v___x_694_ = lean_int_sub(v___x_692_, v___x_693_);
lean_dec(v___x_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_int_add(v___x_691_, v___x_694_);
lean_dec(v___x_694_);
lean_dec(v___x_691_);
v___x_696_ = l_Int_toNat(v___x_695_);
lean_dec(v___x_695_);
v___x_697_ = lean_nat_add(v___x_696_, v_k_685_);
lean_dec(v___x_696_);
v___x_698_ = lp_mathlib_Nat_fast__choose(v___x_697_, v_k_685_);
lean_dec(v___x_697_);
v___x_699_ = lean_apply_1(v_toNatCast_680_, v___x_698_);
v___x_700_ = lean_apply_2(v_toDiv_681_, v___x_688_, v___x_699_);
lean_inc(v_E_684_);
lean_inc_n(v_inst_683_, 2);
lean_inc_ref(v_inst_682_);
v___x_701_ = lp_tree_Formalism_MainNotions_G_divPowE___redArg(v_inst_682_, v_inst_683_, v_E_684_, v_b_679_, v_a_678_, v_k_685_);
v___x_702_ = lp_tree_Formalism_MainNotions_G_divPowE___redArg(v_inst_682_, v_inst_683_, v_E_684_, v_a_678_, v_b_679_, v_k_685_);
v___x_703_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___x_702_, v___x_701_, v___y_686_);
v___x_704_ = lean_apply_2(v_inst_683_, v___x_700_, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___redArg(lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_E_708_, lean_object* v_mu_709_, lean_object* v_a_710_, lean_object* v_b_711_, lean_object* v_T_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_toSemiring_715_; lean_object* v_toAddMonoid_716_; lean_object* v___x_717_; lean_object* v_toMonoid_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_toDiv_721_; lean_object* v_toNPow_722_; lean_object* v_toRing_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_toNeg_726_; lean_object* v___x_727_; lean_object* v_toAddMonoidWithOne_728_; lean_object* v_toNatCast_729_; lean_object* v_toOne_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; 
v___x_713_ = lp_mathlib_Field_toSemifield___redArg(v_inst_705_);
v___x_714_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_713_);
v_toSemiring_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc_ref(v_toSemiring_715_);
lean_dec_ref(v___x_714_);
v_toAddMonoid_716_ = lean_ctor_get(v_inst_706_, 0);
lean_inc_ref(v_toAddMonoid_716_);
lean_dec_ref(v_inst_706_);
v___x_717_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_716_);
v_toMonoid_718_ = lean_ctor_get(v_toSemiring_715_, 1);
lean_inc_ref(v_toMonoid_718_);
lean_dec_ref(v_toSemiring_715_);
lean_inc_ref(v_inst_705_);
v___x_719_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_705_);
v___x_720_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_719_);
v_toDiv_721_ = lean_ctor_get(v___x_720_, 2);
lean_inc(v_toDiv_721_);
lean_dec_ref(v___x_720_);
v_toNPow_722_ = lean_ctor_get(v_toMonoid_718_, 2);
lean_inc(v_toNPow_722_);
lean_dec_ref(v_toMonoid_718_);
v_toRing_723_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_toRing_723_);
lean_dec_ref(v___x_719_);
v___x_724_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_723_);
v___x_725_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_724_);
lean_dec_ref(v___x_724_);
v_toNeg_726_ = lean_ctor_get(v___x_725_, 1);
lean_inc(v_toNeg_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_723_);
v_toAddMonoidWithOne_728_ = lean_ctor_get(v___x_727_, 1);
lean_inc_ref(v_toAddMonoidWithOne_728_);
lean_dec_ref(v___x_727_);
v_toNatCast_729_ = lean_ctor_get(v_toAddMonoidWithOne_728_, 0);
lean_inc(v_toNatCast_729_);
v_toOne_730_ = lean_ctor_get(v_toAddMonoidWithOne_728_, 2);
lean_inc(v_toOne_730_);
lean_dec_ref(v_toAddMonoidWithOne_728_);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_T_712_, v___x_731_);
v___x_733_ = l_List_range(v___x_732_);
v___f_734_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_ppFac___redArg___lam__0), 13, 11);
lean_closure_set(v___f_734_, 0, v_toNeg_726_);
lean_closure_set(v___f_734_, 1, v_toOne_730_);
lean_closure_set(v___f_734_, 2, v_toNPow_722_);
lean_closure_set(v___f_734_, 3, v_mu_709_);
lean_closure_set(v___f_734_, 4, v_a_710_);
lean_closure_set(v___f_734_, 5, v_b_711_);
lean_closure_set(v___f_734_, 6, v_toNatCast_729_);
lean_closure_set(v___f_734_, 7, v_toDiv_721_);
lean_closure_set(v___f_734_, 8, v_inst_705_);
lean_closure_set(v___f_734_, 9, v_inst_707_);
lean_closure_set(v___f_734_, 10, v_E_708_);
v___x_735_ = lp_mathlib_Finset_sum___redArg(v___x_717_, v___x_733_, v___f_734_);
lean_dec_ref(v___x_717_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___redArg___boxed(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_E_739_, lean_object* v_mu_740_, lean_object* v_a_741_, lean_object* v_b_742_, lean_object* v_T_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = lp_tree_Formalism_MainNotions_G_ppFac___redArg(v_inst_736_, v_inst_737_, v_inst_738_, v_E_739_, v_mu_740_, v_a_741_, v_b_742_, v_T_743_);
lean_dec(v_T_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac(lean_object* v_n_745_, lean_object* v_K_746_, lean_object* v_V_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_E_751_, lean_object* v_mu_752_, lean_object* v_a_753_, lean_object* v_b_754_, lean_object* v_T_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lp_tree_Formalism_MainNotions_G_ppFac___redArg(v_inst_748_, v_inst_749_, v_inst_750_, v_E_751_, v_mu_752_, v_a_753_, v_b_754_, v_T_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_ppFac___boxed(lean_object* v_n_757_, lean_object* v_K_758_, lean_object* v_V_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_E_763_, lean_object* v_mu_764_, lean_object* v_a_765_, lean_object* v_b_766_, lean_object* v_T_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = lp_tree_Formalism_MainNotions_G_ppFac(v_n_757_, v_K_758_, v_V_759_, v_inst_760_, v_inst_761_, v_inst_762_, v_E_763_, v_mu_764_, v_a_765_, v_b_766_, v_T_767_);
lean_dec(v_T_767_);
lean_dec(v_n_757_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___redArg___lam__0(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_E_772_, lean_object* v_mu_773_, lean_object* v_T_774_, lean_object* v_ab_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_31__overap_779_; lean_object* v___x_780_; 
v_fst_777_ = lean_ctor_get(v_ab_775_, 0);
lean_inc(v_fst_777_);
v_snd_778_ = lean_ctor_get(v_ab_775_, 1);
lean_inc(v_snd_778_);
lean_dec_ref(v_ab_775_);
v___x_31__overap_779_ = lp_tree_Formalism_MainNotions_G_ppFac___redArg(v_inst_769_, v_inst_770_, v_inst_771_, v_E_772_, v_mu_773_, v_fst_777_, v_snd_778_, v_T_774_);
v___x_780_ = lean_apply_1(v___x_31__overap_779_, v___y_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___redArg___lam__0___boxed(lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_E_784_, lean_object* v_mu_785_, lean_object* v_T_786_, lean_object* v_ab_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = lp_tree_Formalism_MainNotions_G_pp___redArg___lam__0(v_inst_781_, v_inst_782_, v_inst_783_, v_E_784_, v_mu_785_, v_T_786_, v_ab_787_, v___y_788_);
lean_dec(v_T_786_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_E_793_, lean_object* v_mu_794_, lean_object* v_ord_795_, lean_object* v_T_796_){
_start:
{
lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___f_797_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_pp___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_797_, 0, v_inst_790_);
lean_closure_set(v___f_797_, 1, v_inst_791_);
lean_closure_set(v___f_797_, 2, v_inst_792_);
lean_closure_set(v___f_797_, 3, v_E_793_);
lean_closure_set(v___f_797_, 4, v_mu_794_);
lean_closure_set(v___f_797_, 5, v_T_796_);
v___f_798_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__0));
v___f_799_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_divPowE___redArg___closed__1));
v___x_800_ = lean_box(0);
v___x_801_ = l_List_mapTR_loop___redArg(v___f_797_, v_ord_795_, v___x_800_);
v___x_802_ = l_List_prod___redArg(v___f_798_, v___f_799_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp(lean_object* v_n_803_, lean_object* v_K_804_, lean_object* v_V_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_E_809_, lean_object* v_mu_810_, lean_object* v_ord_811_, lean_object* v_T_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lp_tree_Formalism_MainNotions_G_pp___redArg(v_inst_806_, v_inst_807_, v_inst_808_, v_E_809_, v_mu_810_, v_ord_811_, v_T_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pp___boxed(lean_object* v_n_814_, lean_object* v_K_815_, lean_object* v_V_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_E_820_, lean_object* v_mu_821_, lean_object* v_ord_822_, lean_object* v_T_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = lp_tree_Formalism_MainNotions_G_pp(v_n_814_, v_K_815_, v_V_816_, v_inst_817_, v_inst_818_, v_inst_819_, v_E_820_, v_mu_821_, v_ord_822_, v_T_823_);
lean_dec(v_n_814_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_jointIsoSub(lean_object* v_n_825_, lean_object* v_K_826_, lean_object* v_V_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_N_831_, lean_object* v_E_832_, lean_object* v_lam_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_box(0);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_jointIsoSub___boxed(lean_object* v_n_835_, lean_object* v_K_836_, lean_object* v_V_837_, lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_N_841_, lean_object* v_E_842_, lean_object* v_lam_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = lp_tree_Formalism_MainNotions_G_jointIsoSub(v_n_835_, v_K_836_, v_V_837_, v_inst_838_, v_inst_839_, v_inst_840_, v_N_841_, v_E_842_, v_lam_843_);
lean_dec_ref(v_lam_843_);
lean_dec(v_E_842_);
lean_dec(v_N_841_);
lean_dec(v_inst_840_);
lean_dec_ref(v_inst_839_);
lean_dec_ref(v_inst_838_);
lean_dec(v_n_835_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_sumLetters___redArg(lean_object* v_LL_845_){
_start:
{
lean_object* v___x_846_; 
lean_inc_ref(v_LL_845_);
v___x_846_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_846_, 0, lean_box(0));
lean_closure_set(v___x_846_, 1, lean_box(0));
lean_closure_set(v___x_846_, 2, lean_box(0));
lean_closure_set(v___x_846_, 3, v_LL_845_);
lean_closure_set(v___x_846_, 4, v_LL_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_sumLetters(lean_object* v_00_u03b9_847_, lean_object* v_LL_848_){
_start:
{
lean_object* v___x_849_; 
lean_inc_ref(v_LL_848_);
v___x_849_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_849_, 0, lean_box(0));
lean_closure_set(v___x_849_, 1, lean_box(0));
lean_closure_set(v___x_849_, 2, lean_box(0));
lean_closure_set(v___x_849_, 3, v_LL_848_);
lean_closure_set(v___x_849_, 4, v_LL_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pEnd___redArg(lean_object* v_N_850_, lean_object* v_mu_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_apply_2(v_mu_851_, v_N_850_, v_a_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pEnd(lean_object* v_N_854_, lean_object* v_n_855_, lean_object* v_mu_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = lean_apply_2(v_mu_856_, v_N_854_, v_a_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_pEnd___boxed(lean_object* v_N_859_, lean_object* v_n_860_, lean_object* v_mu_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = lp_tree_Formalism_MainNotions_G_pEnd(v_N_859_, v_n_860_, v_mu_861_, v_a_862_);
lean_dec(v_n_860_);
return v_res_863_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_colH___lam__0(lean_object* v_mu_864_, lean_object* v_c_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_apply_1(v_mu_864_, v_a_866_);
v___x_868_ = lean_int_dec_le(v_c_865_, v___x_867_);
lean_dec(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colH___lam__0___boxed(lean_object* v_mu_869_, lean_object* v_c_870_, lean_object* v_a_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = lp_tree_Formalism_MainNotions_G_colH___lam__0(v_mu_869_, v_c_870_, v_a_871_);
lean_dec(v_c_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colH(lean_object* v_n_874_, lean_object* v_mu_875_, lean_object* v_c_876_){
_start:
{
lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___f_877_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_colH___lam__0___boxed), 3, 2);
lean_closure_set(v___f_877_, 0, v_mu_875_);
lean_closure_set(v___f_877_, 1, v_c_876_);
v___x_878_ = l_List_finRange(v_n_874_);
v___x_879_ = lp_mathlib_Multiset_filter___redArg(v___f_877_, v___x_878_);
v___x_880_ = l_List_lengthTR___redArg(v___x_879_);
lean_dec(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extOne___redArg(lean_object* v_n_881_, lean_object* v_inst_882_, lean_object* v_J_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_884_, 0, v_n_881_);
v___x_885_ = lean_box(0);
v___x_886_ = l_List_decidablePerm___redArg(v___x_884_, v_J_883_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v_toSemiring_887_; lean_object* v___x_888_; lean_object* v_toZero_889_; 
v_toSemiring_887_ = lean_ctor_get(v_inst_882_, 0);
lean_inc_ref(v_toSemiring_887_);
lean_dec_ref(v_inst_882_);
v___x_888_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_887_);
v_toZero_889_ = lean_ctor_get(v___x_888_, 1);
lean_inc(v_toZero_889_);
lean_dec_ref(v___x_888_);
return v_toZero_889_;
}
else
{
lean_object* v___x_890_; lean_object* v_toAddMonoidWithOne_891_; lean_object* v_toOne_892_; 
v___x_890_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_882_);
v_toAddMonoidWithOne_891_ = lean_ctor_get(v___x_890_, 1);
lean_inc_ref(v_toAddMonoidWithOne_891_);
lean_dec_ref(v___x_890_);
v_toOne_892_ = lean_ctor_get(v_toAddMonoidWithOne_891_, 2);
lean_inc(v_toOne_892_);
lean_dec_ref(v_toAddMonoidWithOne_891_);
return v_toOne_892_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extOne(lean_object* v_n_893_, lean_object* v_P_894_, lean_object* v_inst_895_, lean_object* v_J_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lp_tree_Formalism_MainNotions_G_extOne___redArg(v_n_893_, v_inst_895_, v_J_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_wedgeR___redArg___lam__0(lean_object* v_toNeg_898_, lean_object* v_toOne_899_, lean_object* v_n_900_, lean_object* v_J_901_, lean_object* v_toNPow_902_, lean_object* v_x_903_, lean_object* v_toMul_904_, lean_object* v_K_905_, lean_object* v_m_906_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_907_ = lean_apply_1(v_toNeg_898_, v_toOne_899_);
lean_inc_n(v_m_906_, 2);
lean_inc(v_n_900_);
v___x_908_ = lean_alloc_closure((void*)(l_Fin_decLt___boxed), 3, 2);
lean_closure_set(v___x_908_, 0, v_n_900_);
lean_closure_set(v___x_908_, 1, v_m_906_);
lean_inc(v_J_901_);
v___x_909_ = lp_mathlib_Multiset_filter___redArg(v___x_908_, v_J_901_);
v___x_910_ = l_List_lengthTR___redArg(v___x_909_);
lean_dec(v___x_909_);
v___x_911_ = lean_apply_2(v_toNPow_902_, v___x_910_, v___x_907_);
v___x_912_ = lean_apply_1(v_x_903_, v_m_906_);
lean_inc(v_toMul_904_);
v___x_913_ = lean_apply_2(v_toMul_904_, v___x_911_, v___x_912_);
v___x_914_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_914_, 0, v_n_900_);
v___x_915_ = lp_mathlib_Multiset_erase___redArg(v___x_914_, v_J_901_, v_m_906_);
v___x_916_ = lean_apply_1(v_K_905_, v___x_915_);
v___x_917_ = lean_apply_2(v_toMul_904_, v___x_913_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_wedgeR___redArg(lean_object* v_n_918_, lean_object* v_inst_919_, lean_object* v_x_920_, lean_object* v_K_921_, lean_object* v_J_922_){
_start:
{
lean_object* v_toSemiring_923_; lean_object* v_toAddCommMonoid_924_; lean_object* v_toMonoid_925_; lean_object* v___x_926_; lean_object* v_toMul_927_; lean_object* v_toNPow_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_toNeg_931_; lean_object* v___x_932_; lean_object* v_toAddMonoidWithOne_933_; lean_object* v_toOne_934_; lean_object* v___f_935_; lean_object* v___x_936_; 
v_toSemiring_923_ = lean_ctor_get(v_inst_919_, 0);
v_toAddCommMonoid_924_ = lean_ctor_get(v_toSemiring_923_, 0);
lean_inc_ref(v_toAddCommMonoid_924_);
v_toMonoid_925_ = lean_ctor_get(v_toSemiring_923_, 1);
lean_inc_ref(v_toSemiring_923_);
v___x_926_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_923_);
v_toMul_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_toMul_927_);
lean_dec_ref(v___x_926_);
v_toNPow_928_ = lean_ctor_get(v_toMonoid_925_, 2);
lean_inc(v_toNPow_928_);
v___x_929_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_919_);
v___x_930_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_929_);
lean_dec_ref(v___x_929_);
v_toNeg_931_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_toNeg_931_);
lean_dec_ref(v___x_930_);
v___x_932_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_919_);
v_toAddMonoidWithOne_933_ = lean_ctor_get(v___x_932_, 1);
lean_inc_ref(v_toAddMonoidWithOne_933_);
lean_dec_ref(v___x_932_);
v_toOne_934_ = lean_ctor_get(v_toAddMonoidWithOne_933_, 2);
lean_inc(v_toOne_934_);
lean_dec_ref(v_toAddMonoidWithOne_933_);
lean_inc(v_J_922_);
v___f_935_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_wedgeR___redArg___lam__0), 9, 8);
lean_closure_set(v___f_935_, 0, v_toNeg_931_);
lean_closure_set(v___f_935_, 1, v_toOne_934_);
lean_closure_set(v___f_935_, 2, v_n_918_);
lean_closure_set(v___f_935_, 3, v_J_922_);
lean_closure_set(v___f_935_, 4, v_toNPow_928_);
lean_closure_set(v___f_935_, 5, v_x_920_);
lean_closure_set(v___f_935_, 6, v_toMul_927_);
lean_closure_set(v___f_935_, 7, v_K_921_);
v___x_936_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_924_, v_J_922_, v___f_935_);
lean_dec_ref(v_toAddCommMonoid_924_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_wedgeR(lean_object* v_n_937_, lean_object* v_P_938_, lean_object* v_inst_939_, lean_object* v_x_940_, lean_object* v_K_941_, lean_object* v_J_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = lp_tree_Formalism_MainNotions_G_wedgeR___redArg(v_n_937_, v_inst_939_, v_x_940_, v_K_941_, v_J_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_contrR___redArg___lam__0(lean_object* v_toNeg_944_, lean_object* v_toOne_945_, lean_object* v_n_946_, lean_object* v_J_947_, lean_object* v_toNPow_948_, lean_object* v_x_949_, lean_object* v_toMul_950_, lean_object* v___x_951_, lean_object* v_K_952_, lean_object* v_m_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_954_ = lean_apply_1(v_toNeg_944_, v_toOne_945_);
lean_inc_n(v_m_953_, 2);
v___x_955_ = lean_alloc_closure((void*)(l_Fin_decLt___boxed), 3, 2);
lean_closure_set(v___x_955_, 0, v_n_946_);
lean_closure_set(v___x_955_, 1, v_m_953_);
lean_inc(v_J_947_);
v___x_956_ = lp_mathlib_Multiset_filter___redArg(v___x_955_, v_J_947_);
v___x_957_ = l_List_lengthTR___redArg(v___x_956_);
lean_dec(v___x_956_);
v___x_958_ = lean_apply_2(v_toNPow_948_, v___x_957_, v___x_954_);
v___x_959_ = lean_apply_1(v_x_949_, v_m_953_);
lean_inc(v_toMul_950_);
v___x_960_ = lean_apply_2(v_toMul_950_, v___x_958_, v___x_959_);
v___x_961_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_951_, v_m_953_, v_J_947_);
v___x_962_ = lean_apply_1(v_K_952_, v___x_961_);
v___x_963_ = lean_apply_2(v_toMul_950_, v___x_960_, v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_contrR___redArg(lean_object* v_n_964_, lean_object* v_inst_965_, lean_object* v_x_966_, lean_object* v_K_967_, lean_object* v_J_968_){
_start:
{
lean_object* v_toSemiring_969_; lean_object* v_toAddCommMonoid_970_; lean_object* v_toMonoid_971_; lean_object* v___x_972_; lean_object* v_toMul_973_; lean_object* v_toNPow_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_toNeg_977_; lean_object* v___x_978_; lean_object* v_toAddMonoidWithOne_979_; lean_object* v_toOne_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
v_toSemiring_969_ = lean_ctor_get(v_inst_965_, 0);
v_toAddCommMonoid_970_ = lean_ctor_get(v_toSemiring_969_, 0);
lean_inc_ref(v_toAddCommMonoid_970_);
v_toMonoid_971_ = lean_ctor_get(v_toSemiring_969_, 1);
lean_inc_ref(v_toSemiring_969_);
v___x_972_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_969_);
v_toMul_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_toMul_973_);
lean_dec_ref(v___x_972_);
v_toNPow_974_ = lean_ctor_get(v_toMonoid_971_, 2);
lean_inc(v_toNPow_974_);
v___x_975_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_965_);
v___x_976_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_975_);
lean_dec_ref(v___x_975_);
v_toNeg_977_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_toNeg_977_);
lean_dec_ref(v___x_976_);
v___x_978_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_965_);
v_toAddMonoidWithOne_979_ = lean_ctor_get(v___x_978_, 1);
lean_inc_ref(v_toAddMonoidWithOne_979_);
lean_dec_ref(v___x_978_);
v_toOne_980_ = lean_ctor_get(v_toAddMonoidWithOne_979_, 2);
lean_inc(v_toOne_980_);
lean_dec_ref(v_toAddMonoidWithOne_979_);
lean_inc_n(v_n_964_, 2);
v___x_981_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_981_, 0, v_n_964_);
v___x_982_ = l_List_finRange(v_n_964_);
lean_inc(v_J_968_);
lean_inc_ref(v___x_981_);
v___x_983_ = lp_mathlib_Multiset_sub___redArg(v___x_981_, v___x_982_, v_J_968_);
v___f_984_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_contrR___redArg___lam__0), 10, 9);
lean_closure_set(v___f_984_, 0, v_toNeg_977_);
lean_closure_set(v___f_984_, 1, v_toOne_980_);
lean_closure_set(v___f_984_, 2, v_n_964_);
lean_closure_set(v___f_984_, 3, v_J_968_);
lean_closure_set(v___f_984_, 4, v_toNPow_974_);
lean_closure_set(v___f_984_, 5, v_x_966_);
lean_closure_set(v___f_984_, 6, v_toMul_973_);
lean_closure_set(v___f_984_, 7, v___x_981_);
lean_closure_set(v___f_984_, 8, v_K_967_);
v___x_985_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_970_, v___x_983_, v___f_984_);
lean_dec_ref(v_toAddCommMonoid_970_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_contrR(lean_object* v_n_986_, lean_object* v_P_987_, lean_object* v_inst_988_, lean_object* v_x_989_, lean_object* v_K_990_, lean_object* v_J_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = lp_tree_Formalism_MainNotions_G_contrR___redArg(v_n_986_, v_inst_988_, v_x_989_, v_K_990_, v_J_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep___redArg(lean_object* v_n_993_, lean_object* v_inst_994_, lean_object* v_c_995_, lean_object* v_hP_996_, lean_object* v_hN_997_, lean_object* v_x_998_, lean_object* v_K_999_, lean_object* v_a_1000_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_nat_dec_lt(v_hP_996_, v_hN_997_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_nat_dec_lt(v_hN_997_, v_hP_996_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
lean_dec(v_x_998_);
lean_dec_ref(v_inst_994_);
lean_dec(v_n_993_);
v___x_1003_ = lean_apply_1(v_K_999_, v_a_1000_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_rootW___closed__0, &lp_tree_Formalism_MainNotions_G_rootW___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_rootW___closed__0);
v___x_1005_ = lean_int_dec_le(v___x_1004_, v_c_995_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lp_tree_Formalism_MainNotions_G_wedgeR___redArg(v_n_993_, v_inst_994_, v_x_998_, v_K_999_, v_a_1000_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lp_tree_Formalism_MainNotions_G_contrR___redArg(v_n_993_, v_inst_994_, v_x_998_, v_K_999_, v_a_1000_);
return v___x_1007_;
}
}
}
else
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_rootW___closed__0, &lp_tree_Formalism_MainNotions_G_rootW___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_rootW___closed__0);
v___x_1009_ = lean_int_dec_le(v___x_1008_, v_c_995_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = lp_tree_Formalism_MainNotions_G_contrR___redArg(v_n_993_, v_inst_994_, v_x_998_, v_K_999_, v_a_1000_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = lp_tree_Formalism_MainNotions_G_wedgeR___redArg(v_n_993_, v_inst_994_, v_x_998_, v_K_999_, v_a_1000_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep___redArg___boxed(lean_object* v_n_1012_, lean_object* v_inst_1013_, lean_object* v_c_1014_, lean_object* v_hP_1015_, lean_object* v_hN_1016_, lean_object* v_x_1017_, lean_object* v_K_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = lp_tree_Formalism_MainNotions_G_colStep___redArg(v_n_1012_, v_inst_1013_, v_c_1014_, v_hP_1015_, v_hN_1016_, v_x_1017_, v_K_1018_, v_a_1019_);
lean_dec(v_hN_1016_);
lean_dec(v_hP_1015_);
lean_dec(v_c_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep(lean_object* v_n_1021_, lean_object* v_P_1022_, lean_object* v_inst_1023_, lean_object* v_c_1024_, lean_object* v_hP_1025_, lean_object* v_hN_1026_, lean_object* v_x_1027_, lean_object* v_K_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lp_tree_Formalism_MainNotions_G_colStep___redArg(v_n_1021_, v_inst_1023_, v_c_1024_, v_hP_1025_, v_hN_1026_, v_x_1027_, v_K_1028_, v_a_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colStep___boxed(lean_object* v_n_1031_, lean_object* v_P_1032_, lean_object* v_inst_1033_, lean_object* v_c_1034_, lean_object* v_hP_1035_, lean_object* v_hN_1036_, lean_object* v_x_1037_, lean_object* v_K_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = lp_tree_Formalism_MainNotions_G_colStep(v_n_1031_, v_P_1032_, v_inst_1033_, v_c_1034_, v_hP_1035_, v_hN_1036_, v_x_1037_, v_K_1038_, v_a_1039_);
lean_dec(v_hN_1036_);
lean_dec(v_hP_1035_);
lean_dec(v_c_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_Ican___lam__0(lean_object* v_N_1041_, lean_object* v_n_1042_, lean_object* v_mu_1043_, lean_object* v_c_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
lean_inc(v_n_1042_);
v___x_1046_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_pEnd___boxed), 4, 3);
lean_closure_set(v___x_1046_, 0, v_N_1041_);
lean_closure_set(v___x_1046_, 1, v_n_1042_);
lean_closure_set(v___x_1046_, 2, v_mu_1043_);
v___x_1047_ = lp_tree_Formalism_MainNotions_G_colH(v_n_1042_, v___x_1046_, v_c_1044_);
v___x_1048_ = lean_nat_dec_le(v___x_1047_, v_a_1045_);
lean_dec(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ican___lam__0___boxed(lean_object* v_N_1049_, lean_object* v_n_1050_, lean_object* v_mu_1051_, lean_object* v_c_1052_, lean_object* v_a_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = lp_tree_Formalism_MainNotions_G_Ican___lam__0(v_N_1049_, v_n_1050_, v_mu_1051_, v_c_1052_, v_a_1053_);
lean_dec(v_a_1053_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_Ican___lam__1(lean_object* v_N_1056_, lean_object* v_n_1057_, lean_object* v_mu_1058_, lean_object* v_c_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
lean_inc(v_n_1057_);
v___x_1061_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_pEnd___boxed), 4, 3);
lean_closure_set(v___x_1061_, 0, v_N_1056_);
lean_closure_set(v___x_1061_, 1, v_n_1057_);
lean_closure_set(v___x_1061_, 2, v_mu_1058_);
v___x_1062_ = lp_tree_Formalism_MainNotions_G_colH(v_n_1057_, v___x_1061_, v_c_1059_);
v___x_1063_ = lean_nat_dec_lt(v_a_1060_, v___x_1062_);
lean_dec(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ican___lam__1___boxed(lean_object* v_N_1064_, lean_object* v_n_1065_, lean_object* v_mu_1066_, lean_object* v_c_1067_, lean_object* v_a_1068_){
_start:
{
uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = lp_tree_Formalism_MainNotions_G_Ican___lam__1(v_N_1064_, v_n_1065_, v_mu_1066_, v_c_1067_, v_a_1068_);
lean_dec(v_a_1068_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ican(lean_object* v_N_1071_, lean_object* v_n_1072_, lean_object* v_mu_1073_, lean_object* v_c_1074_){
_start:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_rootW___closed__0, &lp_tree_Formalism_MainNotions_G_rootW___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_rootW___closed__0);
v___x_1076_ = lean_int_dec_le(v___x_1075_, v_c_1074_);
if (v___x_1076_ == 0)
{
lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_inc(v_n_1072_);
v___f_1077_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_Ican___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1077_, 0, v_N_1071_);
lean_closure_set(v___f_1077_, 1, v_n_1072_);
lean_closure_set(v___f_1077_, 2, v_mu_1073_);
lean_closure_set(v___f_1077_, 3, v_c_1074_);
v___x_1078_ = l_List_finRange(v_n_1072_);
v___x_1079_ = lp_mathlib_Multiset_filter___redArg(v___f_1077_, v___x_1078_);
return v___x_1079_;
}
else
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_inc(v_n_1072_);
v___f_1080_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_Ican___lam__1___boxed), 5, 4);
lean_closure_set(v___f_1080_, 0, v_N_1071_);
lean_closure_set(v___f_1080_, 1, v_n_1072_);
lean_closure_set(v___f_1080_, 2, v_mu_1073_);
lean_closure_set(v___f_1080_, 3, v_c_1074_);
v___x_1081_ = l_List_finRange(v_n_1072_);
v___x_1082_ = lp_mathlib_Multiset_filter___redArg(v___f_1080_, v___x_1081_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tabCol(lean_object* v_n_1083_, lean_object* v_I_1084_, lean_object* v_c_1085_){
_start:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_rootW___closed__0, &lp_tree_Formalism_MainNotions_G_rootW___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_rootW___closed__0);
v___x_1087_ = lean_int_dec_le(v___x_1086_, v_c_1085_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_inc(v_n_1083_);
v___x_1088_ = l_List_finRange(v_n_1083_);
v___x_1089_ = lean_apply_1(v_I_1084_, v_c_1085_);
v___x_1090_ = lp_mathlib_List_diff___at___00Multiset_sub___at___00SSet_boundary_face_u03b9_spec__0_spec__0(v_n_1083_, v___x_1088_, v___x_1089_);
lean_dec(v___x_1089_);
lean_dec(v_n_1083_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
lean_dec(v_n_1083_);
v___x_1091_ = lean_apply_1(v_I_1084_, v_c_1085_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plPart___redArg(lean_object* v_mu_1092_, lean_object* v_i_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_apply_2(v_mu_1092_, v_i_1093_, v_a_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plPart(lean_object* v_N_1096_, lean_object* v_r_1097_, lean_object* v_K_1098_, lean_object* v_mu_1099_, lean_object* v_i_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_apply_2(v_mu_1099_, v_i_1100_, v_a_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plPart___boxed(lean_object* v_N_1103_, lean_object* v_r_1104_, lean_object* v_K_1105_, lean_object* v_mu_1106_, lean_object* v_i_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = lp_tree_Formalism_MainNotions_G_plPart(v_N_1103_, v_r_1104_, v_K_1105_, v_mu_1106_, v_i_1107_, v_a_1108_);
lean_dec(v_K_1105_);
lean_dec(v_r_1104_);
lean_dec(v_N_1103_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart___redArg(lean_object* v_r_1110_, lean_object* v_mu_1111_, lean_object* v_i_1112_, lean_object* v_b_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_nat_add(v_r_1110_, v_b_1113_);
v___x_1115_ = lean_apply_2(v_mu_1111_, v_i_1112_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart___redArg___boxed(lean_object* v_r_1116_, lean_object* v_mu_1117_, lean_object* v_i_1118_, lean_object* v_b_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = lp_tree_Formalism_MainNotions_G_tanPart___redArg(v_r_1116_, v_mu_1117_, v_i_1118_, v_b_1119_);
lean_dec(v_b_1119_);
lean_dec(v_r_1116_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart(lean_object* v_N_1121_, lean_object* v_r_1122_, lean_object* v_K_1123_, lean_object* v_mu_1124_, lean_object* v_i_1125_, lean_object* v_b_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lp_tree_Formalism_MainNotions_G_tanPart___redArg(v_r_1122_, v_mu_1124_, v_i_1125_, v_b_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanPart___boxed(lean_object* v_N_1128_, lean_object* v_r_1129_, lean_object* v_K_1130_, lean_object* v_mu_1131_, lean_object* v_i_1132_, lean_object* v_b_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = lp_tree_Formalism_MainNotions_G_tanPart(v_N_1128_, v_r_1129_, v_K_1130_, v_mu_1131_, v_i_1132_, v_b_1133_);
lean_dec(v_b_1133_);
lean_dec(v_K_1130_);
lean_dec(v_r_1129_);
lean_dec(v_N_1128_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT___redArg(lean_object* v_r_1135_, lean_object* v_nu_1136_, lean_object* v_ka_1137_, lean_object* v_i_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc(v_i_1138_);
v___x_1140_ = lean_apply_1(v_nu_1136_, v_i_1138_);
v___x_1141_ = lean_apply_1(v_ka_1137_, v_i_1138_);
v___x_1142_ = l_Fin_addCases___redArg(v_r_1135_, v___x_1140_, v___x_1141_, v_a_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT___redArg___boxed(lean_object* v_r_1143_, lean_object* v_nu_1144_, lean_object* v_ka_1145_, lean_object* v_i_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = lp_tree_Formalism_MainNotions_G_joinPT___redArg(v_r_1143_, v_nu_1144_, v_ka_1145_, v_i_1146_, v_a_1147_);
lean_dec(v_r_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT(lean_object* v_N_1149_, lean_object* v_r_1150_, lean_object* v_K_1151_, lean_object* v_nu_1152_, lean_object* v_ka_1153_, lean_object* v_i_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = lp_tree_Formalism_MainNotions_G_joinPT___redArg(v_r_1150_, v_nu_1152_, v_ka_1153_, v_i_1154_, v_a_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinPT___boxed(lean_object* v_N_1157_, lean_object* v_r_1158_, lean_object* v_K_1159_, lean_object* v_nu_1160_, lean_object* v_ka_1161_, lean_object* v_i_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = lp_tree_Formalism_MainNotions_G_joinPT(v_N_1157_, v_r_1158_, v_K_1159_, v_nu_1160_, v_ka_1161_, v_i_1162_, v_a_1163_);
lean_dec(v_K_1159_);
lean_dec(v_r_1158_);
lean_dec(v_N_1157_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plVar___redArg(lean_object* v_v_1165_){
_start:
{
lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_fst_1166_ = lean_ctor_get(v_v_1165_, 0);
v_snd_1167_ = lean_ctor_get(v_v_1165_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_v_1165_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v_v_1165_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_inc(v_fst_1166_);
lean_dec(v_v_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_snd_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plVar(lean_object* v_N_1175_, lean_object* v_r_1176_, lean_object* v_K_1177_, lean_object* v_v_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = lp_tree_Formalism_MainNotions_G_plVar___redArg(v_v_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plVar___boxed(lean_object* v_N_1180_, lean_object* v_r_1181_, lean_object* v_K_1182_, lean_object* v_v_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = lp_tree_Formalism_MainNotions_G_plVar(v_N_1180_, v_r_1181_, v_K_1182_, v_v_1183_);
lean_dec(v_K_1182_);
lean_dec(v_r_1181_);
lean_dec(v_N_1180_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar___redArg(lean_object* v_r_1185_, lean_object* v_v_1186_){
_start:
{
lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_fst_1187_ = lean_ctor_get(v_v_1186_, 0);
v_snd_1188_ = lean_ctor_get(v_v_1186_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_v_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v_v_1186_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v_v_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_nat_add(v_r_1185_, v_snd_1188_);
lean_dec(v_snd_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_fst_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar___redArg___boxed(lean_object* v_r_1197_, lean_object* v_v_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = lp_tree_Formalism_MainNotions_G_tanVar___redArg(v_r_1197_, v_v_1198_);
lean_dec(v_r_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar(lean_object* v_N_1200_, lean_object* v_r_1201_, lean_object* v_K_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lp_tree_Formalism_MainNotions_G_tanVar___redArg(v_r_1201_, v_v_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_tanVar___boxed(lean_object* v_N_1205_, lean_object* v_r_1206_, lean_object* v_K_1207_, lean_object* v_v_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = lp_tree_Formalism_MainNotions_G_tanVar(v_N_1205_, v_r_1206_, v_K_1207_, v_v_1208_);
lean_dec(v_K_1207_);
lean_dec(v_r_1206_);
lean_dec(v_N_1205_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinI___lam__0(lean_object* v___y_1210_){
_start:
{
lean_inc(v___y_1210_);
return v___y_1210_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinI___lam__0___boxed(lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = lp_tree_Formalism_MainNotions_G_joinI___lam__0(v___y_1211_);
lean_dec(v___y_1211_);
return v_res_1212_;
}
}
LEAN_EXPORT uint8_t lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___lam__0(lean_object* v_a_1213_, lean_object* v_b_1214_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_eq(v_a_1213_, v_b_1214_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = 1;
return v___x_1216_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = 0;
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v_a_1218_, lean_object* v_b_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___lam__0(v_a_1218_, v_b_1219_);
lean_dec(v_b_1219_);
lean_dec(v_a_1218_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_l_1223_){
_start:
{
lean_object* v___f_1224_; lean_object* v___x_1225_; 
v___f_1224_ = ((lean_object*)(lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_1225_ = lp_batteries_List_pwFilter___redArg(v___f_1224_, v_l_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1(lean_object* v___x_1226_, lean_object* v_s_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg(v_s_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1229_, lean_object* v_s_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1(v___x_1229_, v_s_1230_);
lean_dec(v___x_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0(lean_object* v___x_1232_, lean_object* v_s_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg(v_s_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0___boxed(lean_object* v___x_1235_, lean_object* v_s_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0(v___x_1235_, v_s_1236_);
lean_dec(v___x_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg(lean_object* v___x_1238_, lean_object* v_f_1239_, lean_object* v_s_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lp_mathlib_Multiset_map___redArg(v_f_1239_, v_s_1240_);
v___x_1242_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg___boxed(lean_object* v___x_1243_, lean_object* v_f_1244_, lean_object* v_s_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg(v___x_1243_, v_f_1244_, v_s_1245_);
lean_dec(v___x_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg(lean_object* v_as_1247_, size_t v_i_1248_, size_t v_stop_1249_, lean_object* v_b_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_eq(v_i_1248_, v_stop_1249_);
if (v___x_1251_ == 0)
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = lean_usize_sub(v_i_1248_, v___x_1252_);
v___x_1254_ = lean_array_uget_borrowed(v_as_1247_, v___x_1253_);
v___x_1255_ = lp_mathlib_List_elem___at___00List_diff___at___00Multiset_sub___at___00SSet_boundary_face_u03b9_spec__0_spec__0_spec__1___redArg(v___x_1254_, v_b_1250_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_inc(v___x_1254_);
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v_b_1250_);
v_i_1248_ = v___x_1253_;
v_b_1250_ = v___x_1256_;
goto _start;
}
else
{
v_i_1248_ = v___x_1253_;
goto _start;
}
}
else
{
return v_b_1250_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_as_1259_, lean_object* v_i_1260_, lean_object* v_stop_1261_, lean_object* v_b_1262_){
_start:
{
size_t v_i_boxed_1263_; size_t v_stop_boxed_1264_; lean_object* v_res_1265_; 
v_i_boxed_1263_ = lean_unbox_usize(v_i_1260_);
lean_dec(v_i_1260_);
v_stop_boxed_1264_ = lean_unbox_usize(v_stop_1261_);
lean_dec(v_stop_1261_);
v_res_1265_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg(v_as_1259_, v_i_boxed_1263_, v_stop_boxed_1264_, v_b_1262_);
lean_dec_ref(v_as_1259_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2(lean_object* v___x_1266_, lean_object* v_init_1267_, lean_object* v_l_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1269_ = lean_array_mk(v_l_1268_);
v___x_1270_ = lean_array_get_size(v___x_1269_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_nat_dec_lt(v___x_1271_, v___x_1270_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v___x_1269_);
return v_init_1267_;
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_usize_of_nat(v___x_1270_);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg(v___x_1269_, v___x_1273_, v___x_1274_, v_init_1267_);
lean_dec_ref(v___x_1269_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2___boxed(lean_object* v___x_1276_, lean_object* v_init_1277_, lean_object* v_l_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2(v___x_1276_, v_init_1277_, v_l_1278_);
lean_dec(v___x_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1(lean_object* v___x_1280_, lean_object* v_s_1281_, lean_object* v_t_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2(v___x_1280_, v_t_1282_, v_s_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1___boxed(lean_object* v___x_1284_, lean_object* v_s_1285_, lean_object* v_t_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1(v___x_1284_, v_s_1285_, v_t_1286_);
lean_dec(v___x_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_joinI(lean_object* v_r_1289_, lean_object* v_K_1290_, lean_object* v_I_x27_1291_, lean_object* v_I_x27_x27_1292_, lean_object* v_c_1293_){
_start:
{
lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___f_1294_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_joinI___closed__0));
v___x_1295_ = lean_nat_add(v_r_1289_, v_K_1290_);
lean_inc(v_c_1293_);
v___x_1296_ = lean_apply_1(v_I_x27_1291_, v_c_1293_);
v___x_1297_ = lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg(v___x_1295_, v___f_1294_, v___x_1296_);
v___x_1298_ = lean_alloc_closure((void*)(l_Fin_natAdd___boxed), 3, 2);
lean_closure_set(v___x_1298_, 0, v_K_1290_);
lean_closure_set(v___x_1298_, 1, v_r_1289_);
v___x_1299_ = lean_apply_1(v_I_x27_x27_1292_, v_c_1293_);
v___x_1300_ = lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg(v___x_1295_, v___x_1298_, v___x_1299_);
v___x_1301_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2(v___x_1295_, v___x_1300_, v___x_1297_);
lean_dec(v___x_1295_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0(lean_object* v___x_1302_, lean_object* v_00_u03b1_1303_, lean_object* v_f_1304_, lean_object* v_s_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___redArg(v___x_1302_, v_f_1304_, v_s_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0___boxed(lean_object* v___x_1307_, lean_object* v_00_u03b1_1308_, lean_object* v_f_1309_, lean_object* v_s_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = lp_tree_Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0(v___x_1307_, v_00_u03b1_1308_, v_f_1309_, v_s_1310_);
lean_dec(v___x_1307_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3(lean_object* v___x_1312_, lean_object* v_l_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___redArg(v_l_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v___x_1315_, lean_object* v_l_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_G_joinI_spec__0_spec__0_spec__1_spec__3(v___x_1315_, v_l_1316_);
lean_dec(v___x_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4(lean_object* v___x_1318_, lean_object* v_as_1319_, size_t v_i_1320_, size_t v_stop_1321_, lean_object* v_b_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___redArg(v_as_1319_, v_i_1320_, v_stop_1321_, v_b_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4___boxed(lean_object* v___x_1324_, lean_object* v_as_1325_, lean_object* v_i_1326_, lean_object* v_stop_1327_, lean_object* v_b_1328_){
_start:
{
size_t v_i_boxed_1329_; size_t v_stop_boxed_1330_; lean_object* v_res_1331_; 
v_i_boxed_1329_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_stop_boxed_1330_ = lean_unbox_usize(v_stop_1327_);
lean_dec(v_stop_1327_);
v_res_1331_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_G_joinI_spec__1_spec__2_spec__4(v___x_1324_, v_as_1325_, v_i_boxed_1329_, v_stop_boxed_1330_, v_b_1328_);
lean_dec_ref(v_as_1325_);
lean_dec(v___x_1324_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt___redArg(lean_object* v_r_1332_, lean_object* v_LL_1333_, lean_object* v_om_1334_, lean_object* v_v_1335_){
_start:
{
lean_object* v_fst_1336_; lean_object* v_snd_1337_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_fst_1336_ = lean_ctor_get(v_v_1335_, 0);
lean_inc_n(v_fst_1336_, 2);
v_snd_1337_ = lean_ctor_get(v_v_1335_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v_v_1335_);
lean_inc_ref(v_LL_1333_);
v___x_1345_ = lean_apply_1(v_LL_1333_, v_fst_1336_);
v___x_1346_ = lean_unbox(v___x_1345_);
if (v___x_1346_ == 0)
{
goto v___jp_1338_;
}
else
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_le(v_r_1332_, v_snd_1337_);
if (v___x_1347_ == 0)
{
goto v___jp_1338_;
}
else
{
lean_object* v___x_1348_; 
lean_dec(v_snd_1337_);
lean_dec_ref(v_LL_1333_);
v___x_1348_ = lean_apply_1(v_om_1334_, v_fst_1336_);
return v___x_1348_;
}
}
v___jp_1338_:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
lean_inc(v_fst_1336_);
v___x_1339_ = lean_apply_1(v_LL_1333_, v_fst_1336_);
v___x_1340_ = lean_unbox(v___x_1339_);
if (v___x_1340_ == 0)
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_nat_dec_lt(v_snd_1337_, v_r_1332_);
lean_dec(v_snd_1337_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec(v_fst_1336_);
lean_dec_ref(v_om_1334_);
v___x_1342_ = lean_unsigned_to_nat(0u);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_apply_1(v_om_1334_, v_fst_1336_);
return v___x_1343_;
}
}
else
{
lean_object* v___x_1344_; 
lean_dec(v_snd_1337_);
lean_dec(v_fst_1336_);
lean_dec_ref(v_om_1334_);
v___x_1344_ = lean_unsigned_to_nat(0u);
return v___x_1344_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt___redArg___boxed(lean_object* v_r_1349_, lean_object* v_LL_1350_, lean_object* v_om_1351_, lean_object* v_v_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = lp_tree_Formalism_MainNotions_G_symWt___redArg(v_r_1349_, v_LL_1350_, v_om_1351_, v_v_1352_);
lean_dec(v_r_1349_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt(lean_object* v_N_1354_, lean_object* v_r_1355_, lean_object* v_K_1356_, lean_object* v_LL_1357_, lean_object* v_om_1358_, lean_object* v_v_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lp_tree_Formalism_MainNotions_G_symWt___redArg(v_r_1355_, v_LL_1357_, v_om_1358_, v_v_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_symWt___boxed(lean_object* v_N_1361_, lean_object* v_r_1362_, lean_object* v_K_1363_, lean_object* v_LL_1364_, lean_object* v_om_1365_, lean_object* v_v_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = lp_tree_Formalism_MainNotions_G_symWt(v_N_1361_, v_r_1362_, v_K_1363_, v_LL_1364_, v_om_1365_, v_v_1366_);
lean_dec(v_K_1363_);
lean_dec(v_r_1362_);
lean_dec(v_N_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___redArg___lam__0(lean_object* v_LL_1368_, lean_object* v_r_1369_, lean_object* v_toFun_1370_, lean_object* v_v_1371_){
_start:
{
lean_object* v_toLetters_1372_; lean_object* v_fst_1373_; lean_object* v_snd_1374_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_toLetters_1372_ = lean_ctor_get(v_LL_1368_, 0);
lean_inc_ref_n(v_toLetters_1372_, 2);
lean_dec_ref(v_LL_1368_);
v_fst_1373_ = lean_ctor_get(v_v_1371_, 0);
v_snd_1374_ = lean_ctor_get(v_v_1371_, 1);
lean_inc(v_fst_1373_);
v___x_1382_ = lean_apply_1(v_toLetters_1372_, v_fst_1373_);
v___x_1383_ = lean_unbox(v___x_1382_);
if (v___x_1383_ == 0)
{
goto v___jp_1375_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_nat_dec_le(v_r_1369_, v_snd_1374_);
if (v___x_1384_ == 0)
{
goto v___jp_1375_;
}
else
{
lean_object* v___x_1385_; 
lean_dec_ref(v_toLetters_1372_);
v___x_1385_ = lean_apply_1(v_toFun_1370_, v_v_1371_);
return v___x_1385_;
}
}
v___jp_1375_:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
lean_inc(v_fst_1373_);
v___x_1376_ = lean_apply_1(v_toLetters_1372_, v_fst_1373_);
v___x_1377_ = lean_unbox(v___x_1376_);
if (v___x_1377_ == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_nat_dec_lt(v_snd_1374_, v_r_1369_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_v_1371_);
lean_dec(v_toFun_1370_);
v___x_1379_ = lean_unsigned_to_nat(0u);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_apply_1(v_toFun_1370_, v_v_1371_);
return v___x_1380_;
}
}
else
{
lean_object* v___x_1381_; 
lean_dec_ref(v_v_1371_);
lean_dec(v_toFun_1370_);
v___x_1381_ = lean_unsigned_to_nat(0u);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___redArg___lam__0___boxed(lean_object* v_LL_1386_, lean_object* v_r_1387_, lean_object* v_toFun_1388_, lean_object* v_v_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = lp_tree_Formalism_MainNotions_G_degUS___redArg___lam__0(v_LL_1386_, v_r_1387_, v_toFun_1388_, v_v_1389_);
lean_dec(v_r_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___redArg(lean_object* v_LL_1391_, lean_object* v_r_1392_, lean_object* v_m_1393_){
_start:
{
lean_object* v_support_1394_; lean_object* v_toFun_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v_support_1394_ = lean_ctor_get(v_m_1393_, 0);
lean_inc(v_support_1394_);
v_toFun_1395_ = lean_ctor_get(v_m_1393_, 1);
lean_inc(v_toFun_1395_);
lean_dec_ref(v_m_1393_);
v___f_1396_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_degUS___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1396_, 0, v_LL_1391_);
lean_closure_set(v___f_1396_, 1, v_r_1392_);
lean_closure_set(v___f_1396_, 2, v_toFun_1395_);
v___x_1397_ = lp_mathlib_Finset_sum___at___00Nat_multinomial_spec__0___redArg(v_support_1394_, v___f_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS(lean_object* v_k_1398_, lean_object* v_00_u03b9_1399_, lean_object* v_LL_1400_, lean_object* v_r_1401_, lean_object* v_m_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = lp_tree_Formalism_MainNotions_G_degUS___redArg(v_LL_1400_, v_r_1401_, v_m_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_degUS___boxed(lean_object* v_k_1404_, lean_object* v_00_u03b9_1405_, lean_object* v_LL_1406_, lean_object* v_r_1407_, lean_object* v_m_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = lp_tree_Formalism_MainNotions_G_degUS(v_k_1404_, v_00_u03b9_1405_, v_LL_1406_, v_r_1407_, v_m_1408_);
lean_dec(v_k_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_powC___redArg(lean_object* v_inst_1410_, lean_object* v_P_1411_, lean_object* v_Kv_1412_, lean_object* v_J_1413_){
_start:
{
lean_object* v_toSemiring_1414_; lean_object* v_toMonoid_1415_; lean_object* v_toNPow_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_toSemiring_1414_ = lean_ctor_get(v_inst_1410_, 0);
lean_inc_ref(v_toSemiring_1414_);
lean_dec_ref(v_inst_1410_);
v_toMonoid_1415_ = lean_ctor_get(v_toSemiring_1414_, 1);
lean_inc_ref(v_toMonoid_1415_);
lean_dec_ref(v_toSemiring_1414_);
v_toNPow_1416_ = lean_ctor_get(v_toMonoid_1415_, 2);
lean_inc(v_toNPow_1416_);
lean_dec_ref(v_toMonoid_1415_);
v___x_1417_ = lean_apply_1(v_Kv_1412_, v_J_1413_);
v___x_1418_ = lean_apply_2(v_toNPow_1416_, v_P_1411_, v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_powC(lean_object* v_P_x27_1419_, lean_object* v_inst_1420_, lean_object* v_k_1421_, lean_object* v_P_1422_, lean_object* v_Kv_1423_, lean_object* v_J_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lp_tree_Formalism_MainNotions_G_powC___redArg(v_inst_1420_, v_P_1422_, v_Kv_1423_, v_J_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_powC___boxed(lean_object* v_P_x27_1426_, lean_object* v_inst_1427_, lean_object* v_k_1428_, lean_object* v_P_1429_, lean_object* v_Kv_1430_, lean_object* v_J_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = lp_tree_Formalism_MainNotions_G_powC(v_P_x27_1426_, v_inst_1427_, v_k_1428_, v_P_1429_, v_Kv_1430_, v_J_1431_);
lean_dec(v_k_1428_);
return v_res_1432_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_ObjPol(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
