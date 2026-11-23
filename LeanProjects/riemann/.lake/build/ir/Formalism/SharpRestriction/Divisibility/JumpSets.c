// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.JumpSets
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataDIV public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SatakeDualWeyl.Statement public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
lean_object* l_Sum_swap___redArg(lean_object*);
lean_object* lp_mathlib_MonoidHom_prod___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorization(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_HostRaw_small___redArg(lean_object*);
lean_object* lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(lean_object*, lean_object*);
uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(lean_object*, lean_object*);
lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_decLe___boxed(lean_object*, lean_object*);
lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_DV_toGG(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primeTo(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primeTo___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_botRows(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_tightSh(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_tightSh___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_embG(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kCl(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kCl___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_DecW(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_DecW___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_piK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_piK(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_piK___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_formsSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_formsSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_excSet(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_ramSet(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__0_value;
static lean_once_cell_t lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2(lean_object*);
static const lean_closure_object lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_decLe___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_sum___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_sum___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__1___boxed(lean_object*);
static const lean_array_object lp_tree_Formalism_MainNotions_JumpSetsAlt_smallSum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_smallSum___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_JumpSetsAlt_smallSum___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_smallSum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primesUpTo(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primesUpTo___boxed(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_le(v_x1_1_, v_x2_2_);
if (v___x_3_ == 0)
{
lean_inc(v_x1_1_);
return v_x1_1_;
}
else
{
lean_inc(v_x2_2_);
return v_x2_2_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___lam__0___boxed(lean_object* v_x1_4_, lean_object* v_x2_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___lam__0(v_x1_4_, v_x2_5_);
lean_dec(v_x2_5_);
lean_dec(v_x1_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg(lean_object* v_s_8_, lean_object* v_f_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___f_10_ = ((lean_object*)(lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg___closed__0));
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lp_mathlib_Finset_fold___redArg(v___f_10_, v___x_11_, v_f_9_, v_s_8_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0(lean_object* v_00_u03b2_13_, lean_object* v_s_14_, lean_object* v_f_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg(v_s_14_, v_f_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal___lam__0(lean_object* v_n_17_, lean_object* v_l_18_, lean_object* v_i_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_toFun_22_; lean_object* v___x_23_; 
v___x_20_ = lp_mathlib_Nat_fast__choose(v_n_17_, v_i_19_);
v___x_21_ = lp_mathlib_Nat_factorization(v___x_20_);
v_toFun_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_toFun_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lean_apply_1(v_toFun_22_, v_l_18_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal___lam__0___boxed(lean_object* v_n_24_, lean_object* v_l_25_, lean_object* v_i_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal___lam__0(v_n_24_, v_l_25_, v_i_26_);
lean_dec(v_i_26_);
lean_dec(v_n_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal(lean_object* v_l_28_, lean_object* v_n_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc(v_n_29_);
v___f_30_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal___lam__0___boxed), 3, 2);
lean_closure_set(v___f_30_, 0, v_n_29_);
lean_closure_set(v___f_30_, 1, v_l_28_);
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_add(v_n_29_, v___x_31_);
lean_dec(v_n_29_);
v___x_33_ = l_List_range(v___x_32_);
v___x_34_ = lp_tree_Finset_sup___at___00Formalism_MainNotions_JumpSetsAlt_maxVal_spec__0___redArg(v___x_33_, v___f_30_);
return v___x_34_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___lam__0(lean_object* v_a_35_){
_start:
{
lean_object* v_fst_36_; lean_object* v_snd_37_; uint8_t v___x_38_; 
v_fst_36_ = lean_ctor_get(v_a_35_, 0);
v_snd_37_ = lean_ctor_get(v_a_35_, 1);
v___x_38_ = lean_nat_dec_lt(v_fst_36_, v_snd_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___lam__0___boxed(lean_object* v_a_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___lam__0(v_a_39_);
lean_dec_ref(v_a_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs(lean_object* v_N_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_44_ = ((lean_object*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs___closed__0));
v___x_45_ = l_List_finRange(v_N_43_);
lean_inc(v___x_45_);
v___x_46_ = lp_mathlib_Multiset_product___redArg(v___x_45_, v___x_45_);
v___x_47_ = lp_mathlib_Multiset_filter___redArg(v___f_44_, v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_unsigned_to_nat(1u);
v___x_49_ = lean_nat_to_int(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv(lean_object* v_N_50_, lean_object* v_lam_51_, lean_object* v_i_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc(v_i_52_);
v___x_53_ = lean_apply_1(v_lam_51_, v_i_52_);
v___x_54_ = lean_nat_to_int(v_N_50_);
v___x_55_ = lean_obj_once(&lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0, &lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0_once, _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0);
v___x_56_ = lean_int_sub(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_nat_to_int(v_i_52_);
v___x_58_ = lean_int_sub(v___x_56_, v___x_57_);
lean_dec(v___x_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_int_add(v___x_53_, v___x_58_);
lean_dec(v___x_58_);
lean_dec(v___x_53_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eF___lam__0(lean_object* v_N_60_, lean_object* v_lam_61_, lean_object* v_l_62_, lean_object* v_p_63_){
_start:
{
lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_fst_64_ = lean_ctor_get(v_p_63_, 0);
lean_inc(v_fst_64_);
v_snd_65_ = lean_ctor_get(v_p_63_, 1);
lean_inc(v_snd_65_);
lean_dec_ref(v_p_63_);
lean_inc_ref(v_lam_61_);
lean_inc(v_N_60_);
v___x_66_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv(v_N_60_, v_lam_61_, v_fst_64_);
v___x_67_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv(v_N_60_, v_lam_61_, v_snd_65_);
v___x_68_ = lean_int_sub(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_obj_once(&lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0, &lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0_once, _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_Uv___closed__0);
v___x_70_ = lean_int_sub(v___x_68_, v___x_69_);
lean_dec(v___x_68_);
v___x_71_ = l_Int_toNat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_maxVal(v_l_62_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eF(lean_object* v_N_73_, lean_object* v_l_74_, lean_object* v_lam_75_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_inc(v_N_73_);
v___f_76_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_eF___lam__0), 4, 3);
lean_closure_set(v___f_76_, 0, v_N_73_);
lean_closure_set(v___f_76_, 1, v_lam_75_);
lean_closure_set(v___f_76_, 2, v_l_74_);
v___x_77_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs(v_N_73_);
v___x_78_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_77_, v___f_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart___redArg(lean_object* v_N_79_, lean_object* v_l_80_, lean_object* v_lam_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
lean_inc(v_N_79_);
v___f_83_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_eF___lam__0), 4, 3);
lean_closure_set(v___f_83_, 0, v_N_79_);
lean_closure_set(v___f_83_, 1, v_lam_81_);
lean_closure_set(v___f_83_, 2, v_l_80_);
v___x_84_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_85_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_posPairs(v_N_79_);
v___x_86_ = lp_mathlib_Multiset_filter___redArg(v_inst_82_, v___x_85_);
v___x_87_ = lp_mathlib_Finset_sum___redArg(v___x_84_, v___x_86_, v___f_83_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart(lean_object* v_N_88_, lean_object* v_l_89_, lean_object* v_lam_90_, lean_object* v_P_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart___redArg(v_N_88_, v_l_89_, v_lam_90_, v_inst_92_);
return v___x_93_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl___lam__0(lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_snd_96_; uint8_t v___x_97_; 
v_snd_96_ = lean_ctor_get(v_a_95_, 1);
v___x_97_ = lean_nat_dec_lt(v_snd_96_, v_a_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl___lam__0___boxed(lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl___lam__0(v_a_98_, v_a_99_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl(lean_object* v_N_102_, lean_object* v_l_103_, lean_object* v_lam_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; 
v___f_106_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_eCl___lam__0___boxed), 2, 1);
lean_closure_set(v___f_106_, 0, v_a_105_);
v___x_107_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart___redArg(v_N_102_, v_l_103_, v_lam_104_, v___f_106_);
return v___x_107_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest___lam__0(lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_fst_110_; uint8_t v___x_111_; 
v_fst_110_ = lean_ctor_get(v_a_109_, 0);
v___x_111_ = lean_nat_dec_le(v_a_108_, v_fst_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest___lam__0___boxed(lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest___lam__0(v_a_112_, v_a_113_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest(lean_object* v_N_116_, lean_object* v_l_117_, lean_object* v_lam_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; 
v___f_120_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_eRest___lam__0___boxed), 2, 1);
lean_closure_set(v___f_120_, 0, v_a_119_);
v___x_121_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart___redArg(v_N_116_, v_l_117_, v_lam_118_, v___f_120_);
return v___x_121_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross___lam__0(lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_fst_124_; lean_object* v_snd_125_; uint8_t v___x_126_; 
v_fst_124_ = lean_ctor_get(v_a_123_, 0);
v_snd_125_ = lean_ctor_get(v_a_123_, 1);
v___x_126_ = lean_nat_dec_lt(v_fst_124_, v_a_122_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_le(v_a_122_, v_snd_125_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross___lam__0___boxed(lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross___lam__0(v_a_128_, v_a_129_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross(lean_object* v_N_132_, lean_object* v_l_133_, lean_object* v_lam_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___f_136_; lean_object* v___x_137_; 
v___f_136_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_eCross___lam__0___boxed), 2, 1);
lean_closure_set(v___f_136_, 0, v_a_135_);
v___x_137_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_ePart___redArg(v_N_132_, v_l_133_, v_lam_134_, v___f_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primeTo(lean_object* v_l_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primeTo___boxed(lean_object* v_l_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_primeTo(v_l_140_);
lean_dec(v_l_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0(lean_object* v_a_142_, lean_object* v_lam_143_, lean_object* v_i_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_nat_add(v_a_142_, v_i_144_);
v___x_146_ = lean_apply_1(v_lam_143_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed(lean_object* v_a_147_, lean_object* v_lam_148_, lean_object* v_i_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0(v_a_147_, v_lam_148_, v_i_149_);
lean_dec(v_i_149_);
lean_dec(v_a_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg(lean_object* v_lam_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___f_153_; 
v___f_153_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_153_, 0, v_a_152_);
lean_closure_set(v___f_153_, 1, v_lam_151_);
return v___f_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr(lean_object* v_N_154_, lean_object* v_lam_155_, lean_object* v_a_156_, lean_object* v_n_157_, lean_object* v_h_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_159_, 0, v_a_156_);
lean_closure_set(v___f_159_, 1, v_lam_155_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___boxed(lean_object* v_N_160_, lean_object* v_lam_161_, lean_object* v_a_162_, lean_object* v_n_163_, lean_object* v_h_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_restr(v_N_160_, v_lam_161_, v_a_162_, v_n_163_, v_h_164_);
lean_dec(v_n_163_);
lean_dec(v_N_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows___redArg(lean_object* v_lam_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___f_168_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___f_168_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_168_, 0, v___x_167_);
lean_closure_set(v___f_168_, 1, v_lam_166_);
return v___f_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows(lean_object* v_N_169_, lean_object* v_lam_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows___redArg(v_lam_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows___boxed(lean_object* v_N_173_, lean_object* v_lam_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_topRows(v_N_173_, v_lam_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec(v_N_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_botRows(lean_object* v_N_177_, lean_object* v_lam_178_, lean_object* v_a_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_le(v_a_179_, v_N_177_);
if (v___x_180_ == 0)
{
lean_object* v___f_181_; 
lean_dec(v_a_179_);
v___f_181_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_181_, 0, v_N_177_);
lean_closure_set(v___f_181_, 1, v_lam_178_);
return v___f_181_;
}
else
{
lean_object* v___f_182_; 
lean_dec(v_N_177_);
v___f_182_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_restr___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_182_, 0, v_a_179_);
lean_closure_set(v___f_182_, 1, v_lam_178_);
return v___f_182_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kap(lean_object* v_h_183_, lean_object* v_l_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_sub(v_l_184_, v___x_185_);
v___x_187_ = lean_nat_div(v_h_183_, v___x_186_);
lean_dec(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kap___boxed(lean_object* v_h_188_, lean_object* v_l_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_kap(v_h_188_, v_l_189_);
lean_dec(v_l_189_);
lean_dec(v_h_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_tightSh(lean_object* v_N_191_, lean_object* v_kc_192_, lean_object* v_U_193_, lean_object* v_sh_194_){
_start:
{
lean_object* v_j_195_; lean_object* v_q_196_; lean_object* v_xm_197_; lean_object* v_xp_198_; lean_object* v_maxB_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_218_; 
v_j_195_ = lean_ctor_get(v_sh_194_, 0);
v_q_196_ = lean_ctor_get(v_sh_194_, 1);
v_xm_197_ = lean_ctor_get(v_sh_194_, 2);
v_xp_198_ = lean_ctor_get(v_sh_194_, 3);
v_maxB_199_ = lean_ctor_get(v_sh_194_, 4);
v_isSharedCheck_218_ = !lean_is_exclusive(v_sh_194_);
if (v_isSharedCheck_218_ == 0)
{
v___x_201_ = v_sh_194_;
v_isShared_202_ = v_isSharedCheck_218_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_maxB_199_);
lean_inc(v_xp_198_);
lean_inc(v_xm_197_);
lean_inc(v_q_196_);
lean_inc(v_j_195_);
lean_dec(v_sh_194_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_218_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___y_204_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_sub(v_kc_192_, v___x_214_);
v___x_216_ = lean_nat_dec_lt(v___x_215_, v_N_191_);
if (v___x_216_ == 0)
{
lean_dec(v___x_215_);
v___y_204_ = v_xm_197_;
goto v___jp_203_;
}
else
{
lean_object* v___x_217_; 
lean_dec(v_xm_197_);
lean_inc_ref(v_U_193_);
v___x_217_ = lean_apply_1(v_U_193_, v___x_215_);
v___y_204_ = v___x_217_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_lt(v___x_205_, v_N_191_);
if (v___x_206_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v_U_193_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 2, v___y_204_);
v___x_208_ = v___x_201_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_j_195_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_q_196_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___y_204_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_xp_198_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_maxB_199_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_dec(v_xp_198_);
v___x_210_ = lean_apply_1(v_U_193_, v___x_205_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 3, v___x_210_);
lean_ctor_set(v___x_201_, 2, v___y_204_);
v___x_212_ = v___x_201_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_j_195_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_q_196_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v___y_204_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_maxB_199_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_tightSh___boxed(lean_object* v_N_219_, lean_object* v_kc_220_, lean_object* v_U_221_, lean_object* v_sh_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_tightSh(v_N_219_, v_kc_220_, v_U_221_, v_sh_222_);
lean_dec(v_kc_220_);
lean_dec(v_N_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet___lam__0(lean_object* v_maxB_224_, lean_object* v_s_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_nat_to_int(v_s_225_);
v___x_227_ = lean_int_sub(v_maxB_224_, v___x_226_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet___lam__0___boxed(lean_object* v_maxB_228_, lean_object* v_s_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet___lam__0(v_maxB_228_, v_s_229_);
lean_dec(v_maxB_228_);
return v_res_230_;
}
}
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object* v___x_231_, uint8_t v___x_232_, lean_object* v___y_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_int_dec_eq(v___x_231_, v___y_233_);
if (v___x_234_ == 0)
{
uint8_t v___x_235_; 
v___x_235_ = 1;
return v___x_235_;
}
else
{
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___x_236_, lean_object* v___x_237_, lean_object* v___y_238_){
_start:
{
uint8_t v___x_296__boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v___x_296__boxed_239_ = lean_unbox(v___x_237_);
v_res_240_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(v___x_236_, v___x_296__boxed_239_, v___y_238_);
lean_dec(v___y_238_);
lean_dec(v___x_236_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_as_242_, size_t v_i_243_, size_t v_stop_244_, lean_object* v_b_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_usize_dec_eq(v_i_243_, v_stop_244_);
if (v___x_246_ == 0)
{
size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___f_251_; uint8_t v___x_252_; 
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_sub(v_i_243_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_as_242_, v___x_248_);
v___x_250_ = lean_box(v___x_246_);
lean_inc(v___x_249_);
v___f_251_ = lean_alloc_closure((void*)(lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_251_, 0, v___x_249_);
lean_closure_set(v___f_251_, 1, v___x_250_);
lean_inc(v_b_245_);
v___x_252_ = l_List_decidableBAll___redArg(v___f_251_, v_b_245_);
if (v___x_252_ == 0)
{
v_i_243_ = v___x_248_;
goto _start;
}
else
{
lean_object* v___x_254_; 
lean_inc(v___x_249_);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_249_);
lean_ctor_set(v___x_254_, 1, v_b_245_);
v_i_243_ = v___x_248_;
v_b_245_ = v___x_254_;
goto _start;
}
}
else
{
return v_b_245_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_as_256_, lean_object* v_i_257_, lean_object* v_stop_258_, lean_object* v_b_259_){
_start:
{
size_t v_i_boxed_260_; size_t v_stop_boxed_261_; lean_object* v_res_262_; 
v_i_boxed_260_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_stop_boxed_261_ = lean_unbox_usize(v_stop_258_);
lean_dec(v_stop_258_);
v_res_262_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_as_256_, v_i_boxed_260_, v_stop_boxed_261_, v_b_259_);
lean_dec_ref(v_as_256_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_init_263_, lean_object* v_l_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_array_mk(v_l_264_);
v___x_266_ = lean_array_get_size(v___x_265_);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_nat_dec_lt(v___x_267_, v___x_266_);
if (v___x_268_ == 0)
{
lean_dec_ref(v___x_265_);
return v_init_263_;
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_usize_of_nat(v___x_266_);
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v___x_265_, v___x_269_, v___x_270_, v_init_263_);
lean_dec_ref(v___x_265_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_l_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(0);
v___x_274_ = lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v___x_273_, v_l_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1(lean_object* v_s_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0(lean_object* v_s_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0___redArg(lean_object* v_f_279_, lean_object* v_s_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lp_mathlib_Multiset_map___redArg(v_f_279_, v_s_280_);
v___x_282_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet(lean_object* v_t_283_, lean_object* v_maxB_284_){
_start:
{
lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___f_285_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet___lam__0___boxed), 2, 1);
lean_closure_set(v___f_285_, 0, v_maxB_284_);
v___x_286_ = l_List_range(v_t_283_);
v___x_287_ = lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0___redArg(v___f_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0(lean_object* v_00_u03b1_288_, lean_object* v_f_289_, lean_object* v_s_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0___redArg(v_f_289_, v_s_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2(lean_object* v_l_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_R_294_, lean_object* v_l_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_embG(lean_object* v_D_297_, lean_object* v_00_u03c4_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v_00_u03c4_298_);
v___x_300_ = lp_tree_Formalism_BasicNotions_DV_toGG(v_D_297_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt___redArg(lean_object* v_h_301_, lean_object* v_u_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_val_304_; lean_object* v___x_305_; 
lean_dec(v_h_301_);
v_val_304_ = lean_ctor_get(v_x_303_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v_x_303_, 1);
v___x_305_ = lean_apply_1(v_u_302_, v_val_304_);
return v___x_305_;
}
else
{
lean_object* v_val_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_val_306_ = lean_ctor_get(v_x_303_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v_x_303_, 1);
v___x_307_ = lean_nat_to_int(v_h_301_);
v___x_308_ = lean_apply_1(v_u_302_, v_val_306_);
v___x_309_ = lean_int_sub(v___x_307_, v___x_308_);
lean_dec(v___x_308_);
lean_dec(v___x_307_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt(lean_object* v_D_310_, lean_object* v_h_311_, lean_object* v_u_312_, lean_object* v_x_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt___redArg(v_h_311_, v_u_312_, v_x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt___boxed(lean_object* v_D_315_, lean_object* v_h_316_, lean_object* v_u_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_wAt(v_D_315_, v_h_316_, v_u_317_, v_x_318_);
lean_dec_ref(v_D_315_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___redArg(uint8_t v_e_320_, lean_object* v_00_u03c3_321_){
_start:
{
if (v_e_320_ == 0)
{
return v_00_u03c3_321_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = l_Sum_swap___redArg(v_00_u03c3_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___redArg___boxed(lean_object* v_e_323_, lean_object* v_00_u03c3_324_){
_start:
{
uint8_t v_e_boxed_325_; lean_object* v_res_326_; 
v_e_boxed_325_ = lean_unbox(v_e_323_);
v_res_326_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___redArg(v_e_boxed_325_, v_00_u03c3_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE(lean_object* v_D_327_, uint8_t v_e_328_, lean_object* v_00_u03c3_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___redArg(v_e_328_, v_00_u03c3_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_epE___boxed(lean_object* v_D_331_, lean_object* v_e_332_, lean_object* v_00_u03c3_333_){
_start:
{
uint8_t v_e_boxed_334_; lean_object* v_res_335_; 
v_e_boxed_334_ = lean_unbox(v_e_332_);
v_res_335_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_epE(v_D_331_, v_e_boxed_334_, v_00_u03c3_333_);
lean_dec_ref(v_D_331_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kCl(lean_object* v_D_336_){
_start:
{
lean_object* v_R_337_; lean_object* v_k_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_R_337_ = lean_ctor_get(v_D_336_, 0);
v_k_338_ = lean_ctor_get(v_R_337_, 1);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_sub(v_k_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_kCl___boxed(lean_object* v_D_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_kCl(v_D_341_);
lean_dec_ref(v_D_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_DecW(lean_object* v_D_343_, lean_object* v_w_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_DecW___boxed(lean_object* v_D_346_, lean_object* v_w_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_DecW(v_D_346_, v_w_347_);
lean_dec_ref(v_D_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_piK___redArg(lean_object* v_X_349_, lean_object* v_l_350_, lean_object* v_c_351_){
_start:
{
lean_object* v_kapK_352_; lean_object* v_typ_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_kapK_352_ = lean_ctor_get(v_X_349_, 7);
lean_inc_ref(v_kapK_352_);
v_typ_353_ = lean_ctor_get(v_X_349_, 8);
lean_inc_ref(v_typ_353_);
lean_dec_ref(v_X_349_);
lean_inc(v_c_351_);
lean_inc(v_l_350_);
v___x_354_ = lean_apply_2(v_kapK_352_, v_l_350_, v_c_351_);
v___x_355_ = lean_apply_2(v_typ_353_, v_l_350_, v_c_351_);
v___x_356_ = lp_mathlib_MonoidHom_prod___redArg(v___x_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_piK(lean_object* v_D_357_, lean_object* v_X_358_, lean_object* v_l_359_, lean_object* v_c_360_){
_start:
{
lean_object* v_kapK_361_; lean_object* v_typ_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_kapK_361_ = lean_ctor_get(v_X_358_, 7);
lean_inc_ref(v_kapK_361_);
v_typ_362_ = lean_ctor_get(v_X_358_, 8);
lean_inc_ref(v_typ_362_);
lean_dec_ref(v_X_358_);
lean_inc(v_c_360_);
lean_inc(v_l_359_);
v___x_363_ = lean_apply_2(v_kapK_361_, v_l_359_, v_c_360_);
v___x_364_ = lean_apply_2(v_typ_362_, v_l_359_, v_c_360_);
v___x_365_ = lp_mathlib_MonoidHom_prod___redArg(v___x_363_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_piK___boxed(lean_object* v_D_366_, lean_object* v_X_367_, lean_object* v_l_368_, lean_object* v_c_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_piK(v_D_366_, v_X_367_, v_l_368_, v_c_369_);
lean_dec_ref(v_D_366_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_formsSub(lean_object* v_D_371_, lean_object* v_X_372_, lean_object* v_l_373_, lean_object* v_c_374_, lean_object* v_lam_375_, lean_object* v_U_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_formsSub___boxed(lean_object* v_D_378_, lean_object* v_X_379_, lean_object* v_l_380_, lean_object* v_c_381_, lean_object* v_lam_382_, lean_object* v_U_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_formsSub(v_D_378_, v_X_379_, v_l_380_, v_c_381_, v_lam_382_, v_U_383_);
lean_dec_ref(v_lam_382_);
lean_dec(v_c_381_);
lean_dec(v_l_380_);
lean_dec_ref(v_X_379_);
lean_dec_ref(v_D_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE___lam__0(lean_object* v_h_385_, lean_object* v_x_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_nat_to_int(v_h_385_);
v___x_388_ = lean_int_sub(v___x_387_, v_x_386_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE___lam__0___boxed(lean_object* v_h_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE___lam__0(v_h_389_, v_x_390_);
lean_dec(v_x_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE(lean_object* v_D_392_, lean_object* v_h_393_, lean_object* v_sh_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v_R_396_; lean_object* v_val_397_; lean_object* v_t_398_; lean_object* v___x_399_; lean_object* v_maxB_400_; lean_object* v___x_401_; 
lean_dec(v_h_393_);
v_R_396_ = lean_ctor_get(v_D_392_, 0);
lean_inc_ref(v_R_396_);
lean_dec_ref(v_D_392_);
v_val_397_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v_x_395_, 1);
v_t_398_ = lean_ctor_get(v_R_396_, 3);
lean_inc(v_t_398_);
lean_dec_ref(v_R_396_);
v___x_399_ = lean_apply_1(v_sh_394_, v_val_397_);
v_maxB_400_ = lean_ctor_get(v___x_399_, 4);
lean_inc(v_maxB_400_);
lean_dec_ref(v___x_399_);
v___x_401_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet(v_t_398_, v_maxB_400_);
return v___x_401_;
}
else
{
lean_object* v_R_402_; lean_object* v_val_403_; lean_object* v_t_404_; lean_object* v___x_405_; lean_object* v_maxB_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_R_402_ = lean_ctor_get(v_D_392_, 0);
lean_inc_ref(v_R_402_);
lean_dec_ref(v_D_392_);
v_val_403_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v_x_395_, 1);
v_t_404_ = lean_ctor_get(v_R_402_, 3);
lean_inc(v_t_404_);
lean_dec_ref(v_R_402_);
v___x_405_ = lean_apply_1(v_sh_394_, v_val_403_);
v_maxB_406_ = lean_ctor_get(v___x_405_, 4);
lean_inc(v_maxB_406_);
lean_dec_ref(v___x_405_);
v___f_407_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_blockE___lam__0___boxed), 2, 1);
lean_closure_set(v___f_407_, 0, v_h_393_);
v___x_408_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_blockSet(v_t_404_, v_maxB_406_);
v___x_409_ = lp_tree_Finset_image___at___00Formalism_MainNotions_JumpSetsAlt_blockSet_spec__0___redArg(v___f_407_, v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0_spec__1(lean_object* v_as_410_, size_t v_i_411_, size_t v_stop_412_, lean_object* v_b_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_eq(v_i_411_, v_stop_412_);
if (v___x_414_ == 0)
{
size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_sub(v_i_411_, v___x_415_);
v___x_417_ = lean_array_uget_borrowed(v_as_410_, v___x_416_);
v___x_418_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(v___x_417_, v_b_413_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_inc(v___x_417_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v_b_413_);
v_i_411_ = v___x_416_;
v_b_413_ = v___x_419_;
goto _start;
}
else
{
v_i_411_ = v___x_416_;
goto _start;
}
}
else
{
return v_b_413_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0_spec__1___boxed(lean_object* v_as_422_, lean_object* v_i_423_, lean_object* v_stop_424_, lean_object* v_b_425_){
_start:
{
size_t v_i_boxed_426_; size_t v_stop_boxed_427_; lean_object* v_res_428_; 
v_i_boxed_426_ = lean_unbox_usize(v_i_423_);
lean_dec(v_i_423_);
v_stop_boxed_427_ = lean_unbox_usize(v_stop_424_);
lean_dec(v_stop_424_);
v_res_428_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0_spec__1(v_as_422_, v_i_boxed_426_, v_stop_boxed_427_, v_b_425_);
lean_dec_ref(v_as_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0(lean_object* v_init_429_, lean_object* v_l_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_431_ = lean_array_mk(v_l_430_);
v___x_432_ = lean_array_get_size(v___x_431_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_nat_dec_lt(v___x_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_dec_ref(v___x_431_);
return v_init_429_;
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_usize_of_nat(v___x_432_);
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0_spec__1(v___x_431_, v___x_435_, v___x_436_, v_init_429_);
lean_dec_ref(v___x_431_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0(lean_object* v_s_438_, lean_object* v_t_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0(v_t_439_, v_s_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_excSet(lean_object* v_D_441_){
_start:
{
lean_object* v_host_442_; lean_object* v_toHostAx_443_; lean_object* v_pde_444_; lean_object* v_pde_x27_445_; lean_object* v_q_446_; lean_object* v_d_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_host_442_ = lean_ctor_get(v_D_441_, 1);
lean_inc_ref(v_host_442_);
lean_dec_ref(v_D_441_);
v_toHostAx_443_ = lean_ctor_get(v_host_442_, 0);
lean_inc_ref(v_toHostAx_443_);
v_pde_444_ = lean_ctor_get(v_host_442_, 7);
lean_inc(v_pde_444_);
v_pde_x27_445_ = lean_ctor_get(v_host_442_, 8);
lean_inc(v_pde_x27_445_);
lean_dec_ref(v_host_442_);
v_q_446_ = lean_ctor_get(v_toHostAx_443_, 0);
lean_inc(v_q_446_);
v_d_447_ = lean_ctor_get(v_toHostAx_443_, 1);
lean_inc(v_d_447_);
v___x_448_ = lp_tree_Formalism_HC_HostRaw_small___redArg(v_toHostAx_443_);
lean_dec_ref(v_toHostAx_443_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v_pde_x27_445_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(v_pde_444_, v___x_450_);
v___x_452_ = lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(v_d_447_, v___x_451_);
v___x_453_ = lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(v_q_446_, v___x_452_);
v___x_454_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0(v___x_453_, v___x_448_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_ramSet(lean_object* v_D_455_){
_start:
{
lean_object* v_host_456_; lean_object* v_toHostAx_457_; lean_object* v_q_458_; lean_object* v_d_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_host_456_ = lean_ctor_get(v_D_455_, 1);
lean_inc_ref(v_host_456_);
lean_dec_ref(v_D_455_);
v_toHostAx_457_ = lean_ctor_get(v_host_456_, 0);
lean_inc_ref(v_toHostAx_457_);
lean_dec_ref(v_host_456_);
v_q_458_ = lean_ctor_get(v_toHostAx_457_, 0);
lean_inc(v_q_458_);
v_d_459_ = lean_ctor_get(v_toHostAx_457_, 1);
lean_inc(v_d_459_);
v___x_460_ = lp_tree_Formalism_HC_HostRaw_small___redArg(v_toHostAx_457_);
lean_dec_ref(v_toHostAx_457_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v_d_459_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(v_q_458_, v___x_462_);
v___x_464_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_MainNotions_JumpSetsAlt_excSet_spec__0_spec__0(v___x_463_, v___x_460_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__0(lean_object* v___y_465_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__0___boxed(lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__0(v___y_466_);
lean_dec(v___y_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1(lean_object* v___x_468_, lean_object* v___f_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Fin_cases___redArg(v___x_468_, v___f_469_, v___y_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1___boxed(lean_object* v___x_472_, lean_object* v___f_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1(v___x_472_, v___f_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec(v___x_472_);
return v_res_475_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_nat_to_int(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__2(void){
_start:
{
lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___f_481_; 
v___f_479_ = ((lean_object*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__0));
v___x_480_ = lean_obj_once(&lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1, &lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1_once, _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1);
v___f_481_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_481_, 0, v___x_480_);
lean_closure_set(v___f_481_, 1, v___f_479_);
return v___f_481_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2(lean_object* v_n_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___f_485_; 
v___x_483_ = lean_nat_to_int(v_n_482_);
v___f_484_ = lean_obj_once(&lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__2, &lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__2_once, _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__2);
v___f_485_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_485_, 0, v___x_483_);
lean_closure_set(v___f_485_, 1, v___f_484_);
return v___f_485_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg(lean_object* v_s_487_){
_start:
{
lean_object* v___f_488_; lean_object* v___x_489_; 
v___f_488_ = ((lean_object*)(lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg___closed__0));
v___x_489_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v_s_487_, v___f_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0(lean_object* v_s_490_, lean_object* v_r_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg(v_s_490_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_sum___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__1(lean_object* v_l_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1, &lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1_once, _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_wt2___closed__1);
v___x_498_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v___x_497_, v_l_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_sum___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__1___boxed(lean_object* v_l_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = lp_tree_List_sum___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__1(v_l_499_);
lean_dec(v_l_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_smallSum(lean_object* v_N_503_, lean_object* v_U_504_, lean_object* v_n_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_506_ = l_List_finRange(v_N_503_);
v___x_507_ = lp_mathlib_Multiset_map___redArg(v_U_504_, v___x_506_);
v___x_508_ = lp_tree_Multiset_sort___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__0___redArg(v___x_507_);
v___x_509_ = ((lean_object*)(lp_tree_Formalism_MainNotions_JumpSetsAlt_smallSum___closed__0));
lean_inc(v___x_508_);
v___x_510_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v___x_508_, v___x_508_, v_n_505_, v___x_509_);
lean_dec(v___x_508_);
v___x_511_ = lp_tree_List_sum___at___00Formalism_MainNotions_JumpSetsAlt_smallSum_spec__1(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primesUpTo(lean_object* v_n_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_n_512_, v___x_513_);
v___x_515_ = l_List_range(v___x_514_);
v___x_516_ = lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_primesUpTo___boxed(lean_object* v_n_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_primesUpTo(v_n_517_);
lean_dec(v_n_517_);
return v_res_518_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___closed__0(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(6u);
v___x_520_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of(lean_object* v_l_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___f_528_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_524_ = l_List_getD___redArg(v_l_521_, v___x_522_, v___x_523_);
v___x_525_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_526_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_526_, 0, v___x_524_);
lean_closure_set(v___f_526_, 1, v___x_525_);
v___x_527_ = lean_obj_once(&lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___closed__0, &lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___closed__0_once, _init_lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___closed__0);
v___f_528_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_528_, 0, v___f_526_);
lean_closure_set(v___f_528_, 1, v___x_527_);
return v___f_528_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of___boxed(lean_object* v_l_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = lp_tree_Formalism_MainNotions_JumpSetsAlt_a0Of(v_l_529_);
lean_dec(v_l_529_);
return v_res_530_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DeltaInvariantLattices(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_JumpSets(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DeltaInvariantLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
