// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.RowForms
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter public import Formalism.LocalToGlobal.Columns.LevGCount public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions public import Formalism.LocalToGlobal.Columns.StdLatUnimodular public import Formalism.LocalToGlobal.Columns.DecoFin public import Formalism.LocalToGlobal.Columns.CoefCol public import Formalism.LocalToGlobal.Columns.ColForms public import Formalism.LocalToGlobal.Divisibility.Tuples public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
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
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_restr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_L2_Col_supSum___at___00Formalism_L2_Col_supHom___at___00Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8_spec__11_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_coarse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_tree_Finset_prod___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Subgroup_inclusion___at___00Formalism_L2_Col_lamXm___at___00Formalism_L2_Col_colLev_spec__2_spec__3___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_LinearEquiv_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_toBlock___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_extChi___at___00Formalism_L2_Col_colLev_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_SPsym(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_MonoidHom_toHomUnits___at___00Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_rS(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU___at___00Formalism_L2_Col_rP0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subgroup_inclusion___at___00Formalism_L2_Col_lamXm___at___00Formalism_L2_Col_colLev_spec__2_spec__3___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym___at___00Formalism_L2_Col_rPsym_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym___at___00Formalism_L2_Col_rPsym_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsym___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_comap___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_comap___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_map___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_map___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rowTyG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rowTyK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__0(lean_object* v_toAddCommMonoid_1_, lean_object* v_i_2_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_1_);
return v_toAddCommMonoid_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_L2_Col_trF___redArg___lam__0(v_toAddCommMonoid_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec_ref(v_toAddCommMonoid_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__1(lean_object* v_a_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; lean_object* v_val_9_; lean_object* v_inv_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_17_; 
v___x_8_ = lean_apply_1(v_a_6_, v___y_7_);
v_val_9_ = lean_ctor_get(v___x_8_, 0);
v_inv_10_ = lean_ctor_get(v___x_8_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_17_ == 0)
{
v___x_12_ = v___x_8_;
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_inv_10_);
lean_inc(v_val_9_);
lean_dec(v___x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v_val_9_);
lean_ctor_set(v___x_12_, 0, v_inv_10_);
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_inv_10_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_val_9_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__2(lean_object* v___f_18_, lean_object* v_toSemiring_19_, lean_object* v___x_20_, lean_object* v_fieldE_21_, lean_object* v_n_22_, lean_object* v_a_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_trF___redArg___lam__1), 2, 1);
lean_closure_set(v___f_26_, 0, v_a_23_);
v___x_27_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_18_);
v___x_28_ = lp_mathlib_LinearEquiv_refl(lean_box(0), lean_box(0), v_toSemiring_19_, v___x_27_, v___x_20_);
lean_dec_ref(v___x_27_);
v___x_29_ = lp_tree_Formalism_L2_Col_Deco_act___redArg(v_fieldE_21_, v_n_22_, v___x_28_, v___f_26_, v___y_25_);
v___x_30_ = lean_apply_1(v___y_24_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg___lam__2___boxed(lean_object* v___f_31_, lean_object* v_toSemiring_32_, lean_object* v___x_33_, lean_object* v_fieldE_34_, lean_object* v_n_35_, lean_object* v_a_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_L2_Col_trF___redArg___lam__2(v___f_31_, v_toSemiring_32_, v___x_33_, v_fieldE_34_, v_n_35_, v_a_36_, v___y_37_, v___y_38_);
lean_dec(v___x_33_);
lean_dec_ref(v_toSemiring_32_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___redArg(lean_object* v_X_40_, lean_object* v_n_41_){
_start:
{
lean_object* v_fieldE_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v_toSemiring_45_; lean_object* v_toAddCommMonoid_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___f_50_; 
v_fieldE_42_ = lean_ctor_get(v_X_40_, 1);
lean_inc_ref(v_fieldE_42_);
lean_dec_ref(v_X_40_);
v___x_43_ = lp_mathlib_Field_toSemifield___redArg(v_fieldE_42_);
v___x_44_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_43_);
v_toSemiring_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_toSemiring_45_);
lean_dec_ref(v___x_44_);
v_toAddCommMonoid_46_ = lean_ctor_get(v_toSemiring_45_, 0);
lean_inc_ref(v_toAddCommMonoid_46_);
v___f_47_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_trF___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_47_, 0, v_toAddCommMonoid_46_);
v___x_48_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_45_);
v___x_49_ = lp_mathlib_Pi_Function_module___redArg(v___x_48_);
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_trF___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_50_, 0, v___f_47_);
lean_closure_set(v___f_50_, 1, v_toSemiring_45_);
lean_closure_set(v___f_50_, 2, v___x_49_);
lean_closure_set(v___f_50_, 3, v_fieldE_42_);
lean_closure_set(v___f_50_, 4, v_n_41_);
return v___f_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF(lean_object* v_X_51_, lean_object* v_n_52_, lean_object* v_ST_53_, lean_object* v_SG_54_, lean_object* v_V_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_tree_Formalism_L2_Col_trF___redArg(v_X_51_, v_n_52_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_trF___boxed(lean_object* v_X_59_, lean_object* v_n_60_, lean_object* v_ST_61_, lean_object* v_SG_62_, lean_object* v_V_63_, lean_object* v_inst_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_L2_Col_trF(v_X_59_, v_n_60_, v_ST_61_, v_SG_62_, v_V_63_, v_inst_64_, v_inst_65_);
lean_dec(v_inst_65_);
lean_dec_ref(v_inst_64_);
lean_dec(v_SG_62_);
lean_dec(v_ST_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___redArg___lam__0(lean_object* v_Ch_67_, lean_object* v_w_68_, lean_object* v_s_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_chi_71_; lean_object* v___x_72_; 
v_chi_71_ = lean_ctor_get(v_Ch_67_, 1);
lean_inc_ref(v_chi_71_);
lean_dec_ref(v_Ch_67_);
v___x_72_ = lean_apply_3(v_chi_71_, v_s_69_, v_w_68_, v___y_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___redArg(lean_object* v_X_73_, lean_object* v_R_74_, lean_object* v_Ch_75_, lean_object* v_w_76_, lean_object* v_s_77_){
_start:
{
lean_object* v_m_78_; lean_object* v___f_79_; lean_object* v___x_80_; 
v_m_78_ = lean_ctor_get(v_R_74_, 2);
v___f_79_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_chiAt___redArg___lam__0), 4, 2);
lean_closure_set(v___f_79_, 0, v_Ch_75_);
lean_closure_set(v___f_79_, 1, v_w_76_);
v___x_80_ = lp_tree_Formalism_L2_Col_extChi___at___00Formalism_L2_Col_colLev_spec__1___redArg(v_X_73_, v_m_78_, v___f_79_, v_s_77_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___redArg___boxed(lean_object* v_X_81_, lean_object* v_R_82_, lean_object* v_Ch_83_, lean_object* v_w_84_, lean_object* v_s_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_L2_Col_chiAt___redArg(v_X_81_, v_R_82_, v_Ch_83_, v_w_84_, v_s_85_);
lean_dec_ref(v_R_82_);
lean_dec_ref(v_X_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt(lean_object* v_X_87_, lean_object* v_Pr_88_, lean_object* v_R_89_, lean_object* v_Ch_90_, lean_object* v_w_91_, lean_object* v_s_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_tree_Formalism_L2_Col_chiAt___redArg(v_X_87_, v_R_89_, v_Ch_90_, v_w_91_, v_s_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiAt___boxed(lean_object* v_X_94_, lean_object* v_Pr_95_, lean_object* v_R_96_, lean_object* v_Ch_97_, lean_object* v_w_98_, lean_object* v_s_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_tree_Formalism_L2_Col_chiAt(v_X_94_, v_Pr_95_, v_R_96_, v_Ch_97_, v_w_98_, v_s_99_);
lean_dec_ref(v_R_96_);
lean_dec_ref(v_Pr_95_);
lean_dec_ref(v_X_94_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_psiU___at___00Formalism_L2_Col_rP0_spec__0(lean_object* v_X_101_, lean_object* v___x_102_, lean_object* v_00_u03c8_103_, lean_object* v_k_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = lean_box(0);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_sub(v_k_104_, v___x_106_);
v___x_108_ = l_List_range(v___x_107_);
lean_inc(v_k_104_);
v___x_109_ = lp_tree_Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8(v_X_101_, v___x_102_, v_00_u03c8_103_, v_k_104_, v_k_104_, v___x_105_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0___redArg(lean_object* v_X_110_, lean_object* v_R_111_, lean_object* v_Ch_112_, lean_object* v_w_113_){
_start:
{
lean_object* v_psi0_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_psi0_114_ = lean_ctor_get(v_Ch_112_, 0);
lean_inc(v_psi0_114_);
lean_dec_ref(v_Ch_112_);
v___x_115_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_111_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_apply_1(v_psi0_114_, v_w_113_);
v___x_118_ = lp_tree_Formalism_L2_Col_psiU___at___00Formalism_L2_Col_rP0_spec__0(v_X_110_, v_w_113_, v___x_117_, v___x_115_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0___redArg___boxed(lean_object* v_X_120_, lean_object* v_R_121_, lean_object* v_Ch_122_, lean_object* v_w_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_Formalism_L2_Col_rP0___redArg(v_X_120_, v_R_121_, v_Ch_122_, v_w_123_);
lean_dec_ref(v_R_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0(lean_object* v_X_125_, lean_object* v_Pr_126_, lean_object* v_R_127_, lean_object* v_Ch_128_, lean_object* v_w_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_tree_Formalism_L2_Col_rP0___redArg(v_X_125_, v_R_127_, v_Ch_128_, v_w_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rP0___boxed(lean_object* v_X_131_, lean_object* v_Pr_132_, lean_object* v_R_133_, lean_object* v_Ch_134_, lean_object* v_w_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = lp_tree_Formalism_L2_Col_rP0(v_X_131_, v_Pr_132_, v_R_133_, v_Ch_134_, v_w_135_);
lean_dec_ref(v_R_133_);
lean_dec_ref(v_Pr_132_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp___redArg(lean_object* v_X_138_, lean_object* v_R_139_, lean_object* v_Ch_140_, lean_object* v_w_141_){
_start:
{
lean_object* v_psi0_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___x_149_; 
v_psi0_142_ = lean_ctor_get(v_Ch_140_, 0);
lean_inc(v_psi0_142_);
lean_dec_ref(v_Ch_140_);
v___x_143_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_139_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_1(v_psi0_142_, v_w_141_);
v___x_146_ = lp_tree_Formalism_L2_Col_psiU___at___00Formalism_L2_Col_rP0_spec__0(v_X_138_, v_w_141_, v___x_145_, v___x_143_);
v___f_147_ = ((lean_object*)(lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0));
v___f_148_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_148_, 0, v___f_147_);
lean_closure_set(v___f_148_, 1, v___x_146_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_144_);
lean_ctor_set(v___x_149_, 1, v___f_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp___redArg___boxed(lean_object* v_X_150_, lean_object* v_R_151_, lean_object* v_Ch_152_, lean_object* v_w_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_tree_Formalism_L2_Col_rPsharp___redArg(v_X_150_, v_R_151_, v_Ch_152_, v_w_153_);
lean_dec_ref(v_R_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp(lean_object* v_X_155_, lean_object* v_Pr_156_, lean_object* v_R_157_, lean_object* v_Ch_158_, lean_object* v_w_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lp_tree_Formalism_L2_Col_rPsharp___redArg(v_X_155_, v_R_157_, v_Ch_158_, v_w_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsharp___boxed(lean_object* v_X_161_, lean_object* v_Pr_162_, lean_object* v_R_163_, lean_object* v_Ch_164_, lean_object* v_w_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_tree_Formalism_L2_Col_rPsharp(v_X_161_, v_Pr_162_, v_R_163_, v_Ch_164_, v_w_165_);
lean_dec_ref(v_R_163_);
lean_dec_ref(v_Pr_162_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym___at___00Formalism_L2_Col_rPsym_spec__0(lean_object* v_X_167_, lean_object* v___x_168_, lean_object* v_n_169_, lean_object* v_k_170_, lean_object* v_rS_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsym___at___00Formalism_L2_Col_rPsym_spec__0___boxed(lean_object* v_X_173_, lean_object* v___x_174_, lean_object* v_n_175_, lean_object* v_k_176_, lean_object* v_rS_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_tree_Formalism_L2_Col_HPsym___at___00Formalism_L2_Col_rPsym_spec__0(v_X_173_, v___x_174_, v_n_175_, v_k_176_, v_rS_177_);
lean_dec(v_rS_177_);
lean_dec(v_k_176_);
lean_dec(v_n_175_);
lean_dec_ref(v_X_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__0(lean_object* v_fieldE_179_, lean_object* v_i_180_, lean_object* v_rS_181_, lean_object* v_k_182_, lean_object* v_M_183_, lean_object* v_j_184_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_i_180_, v___x_193_);
v___x_195_ = lean_nat_dec_eq(v___x_194_, v_rS_181_);
lean_dec(v___x_194_);
if (v___x_195_ == 0)
{
lean_dec(v_j_184_);
lean_dec(v_M_183_);
lean_dec(v_i_180_);
goto v___jp_185_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_nat_add(v_rS_181_, v_k_182_);
v___x_197_ = lean_nat_dec_eq(v_j_184_, v___x_196_);
lean_dec(v___x_196_);
if (v___x_197_ == 0)
{
lean_dec(v_j_184_);
lean_dec(v_M_183_);
lean_dec(v_i_180_);
goto v___jp_185_;
}
else
{
lean_object* v___x_198_; 
lean_dec_ref(v_fieldE_179_);
v___x_198_ = lean_apply_2(v_M_183_, v_i_180_, v_j_184_);
return v___x_198_;
}
}
v___jp_185_:
{
lean_object* v_toCommRing_186_; lean_object* v_toSemiring_187_; lean_object* v___x_188_; lean_object* v_toNonUnitalNonAssocSemiring_189_; lean_object* v_toAddCommMonoid_190_; lean_object* v___x_191_; lean_object* v_toZero_192_; 
v_toCommRing_186_ = lean_ctor_get(v_fieldE_179_, 0);
lean_inc_ref(v_toCommRing_186_);
lean_dec_ref(v_fieldE_179_);
v_toSemiring_187_ = lean_ctor_get(v_toCommRing_186_, 0);
lean_inc_ref(v_toSemiring_187_);
lean_dec_ref(v_toCommRing_186_);
v___x_188_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_187_);
v_toNonUnitalNonAssocSemiring_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc_ref(v_toNonUnitalNonAssocSemiring_189_);
lean_dec_ref(v___x_188_);
v_toAddCommMonoid_190_ = lean_ctor_get(v_toNonUnitalNonAssocSemiring_189_, 0);
lean_inc_ref(v_toAddCommMonoid_190_);
lean_dec_ref(v_toNonUnitalNonAssocSemiring_189_);
v___x_191_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_190_);
lean_dec_ref(v_toAddCommMonoid_190_);
v_toZero_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_toZero_192_);
lean_dec_ref(v___x_191_);
return v_toZero_192_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_fieldE_199_, lean_object* v_i_200_, lean_object* v_rS_201_, lean_object* v_k_202_, lean_object* v_M_203_, lean_object* v_j_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__0(v_fieldE_199_, v_i_200_, v_rS_201_, v_k_202_, v_M_203_, v_j_204_);
lean_dec(v_k_202_);
lean_dec(v_rS_201_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__1(lean_object* v_fieldE_206_, lean_object* v_rS_207_, lean_object* v_k_208_, lean_object* v_M_209_, lean_object* v_X_210_, lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v_i_213_){
_start:
{
lean_object* v___f_214_; lean_object* v___x_215_; 
v___f_214_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__0___boxed), 6, 5);
lean_closure_set(v___f_214_, 0, v_fieldE_206_);
lean_closure_set(v___f_214_, 1, v_i_213_);
lean_closure_set(v___f_214_, 2, v_rS_207_);
lean_closure_set(v___f_214_, 3, v_k_208_);
lean_closure_set(v___f_214_, 4, v_M_209_);
v___x_215_ = lp_tree_Finset_sum___at___00Formalism_L2_Col_supSum___at___00Formalism_L2_Col_supHom___at___00Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8_spec__11_spec__14_spec__16___redArg(v_X_210_, v___x_211_, v___x_212_, v___f_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2(lean_object* v_X_216_, lean_object* v___x_217_, lean_object* v_n_218_, lean_object* v_k_219_, lean_object* v_rS_220_, lean_object* v_M_221_){
_start:
{
lean_object* v_fieldE_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___x_225_; 
v_fieldE_222_ = lean_ctor_get(v_X_216_, 1);
v___x_223_ = l_List_finRange(v_n_218_);
lean_inc(v___x_223_);
lean_inc_ref(v_X_216_);
lean_inc_ref(v_fieldE_222_);
v___f_224_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2___lam__1), 8, 7);
lean_closure_set(v___f_224_, 0, v_fieldE_222_);
lean_closure_set(v___f_224_, 1, v_rS_220_);
lean_closure_set(v___f_224_, 2, v_k_219_);
lean_closure_set(v___f_224_, 3, v_M_221_);
lean_closure_set(v___f_224_, 4, v_X_216_);
lean_closure_set(v___f_224_, 5, v___x_217_);
lean_closure_set(v___f_224_, 6, v___x_223_);
v___x_225_ = lp_tree_Finset_sum___at___00Formalism_L2_Col_supSum___at___00Formalism_L2_Col_supHom___at___00Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8_spec__11_spec__14_spec__16___redArg(v_X_216_, v___x_217_, v___x_223_, v___f_224_);
return v___x_225_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_226_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0(lean_object* v_X_227_, lean_object* v___x_228_, lean_object* v_n_229_, lean_object* v_k_230_, lean_object* v_rS_231_, lean_object* v_M_232_){
_start:
{
lean_object* v_val_233_; lean_object* v___x_234_; lean_object* v_toFun_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_val_233_ = lean_ctor_get(v_M_232_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v_M_232_);
v___x_234_ = lean_obj_once(&lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0___closed__0, &lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0___closed__0);
v_toFun_235_ = lean_ctor_get(v___x_234_, 0);
v___x_236_ = lp_tree_Formalism_L2_Col_offSum___at___00Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1_spec__2(v_X_227_, v___x_228_, v_n_229_, v_k_230_, v_rS_231_, v_val_233_);
lean_inc(v_toFun_235_);
v___x_237_ = lean_apply_1(v_toFun_235_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1(lean_object* v_X_238_, lean_object* v___x_239_, lean_object* v_n_240_, lean_object* v_k_241_, lean_object* v_rS_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0), 6, 5);
lean_closure_set(v___f_243_, 0, v_X_238_);
lean_closure_set(v___f_243_, 1, v___x_239_);
lean_closure_set(v___f_243_, 2, v_n_240_);
lean_closure_set(v___f_243_, 3, v_k_241_);
lean_closure_set(v___f_243_, 4, v_rS_242_);
return v___f_243_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1___lam__0(lean_object* v___x_244_, lean_object* v___f_245_, lean_object* v___x_246_, lean_object* v___x_247_, lean_object* v___x_248_, lean_object* v_m_249_){
_start:
{
lean_object* v___x_250_; lean_object* v_toMul_251_; lean_object* v___x_252_; lean_object* v_val_253_; lean_object* v_inv_254_; lean_object* v___x_255_; lean_object* v_val_256_; lean_object* v_inv_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_266_; 
v___x_250_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_244_);
v_toMul_251_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_toMul_251_);
lean_dec_ref(v___x_250_);
lean_inc_ref(v_m_249_);
v___x_252_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_245_, v___x_246_, v_m_249_);
v_val_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_val_253_);
v_inv_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_inv_254_);
lean_dec(v___x_252_);
v___x_255_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___x_247_, v___x_248_, v_m_249_);
v_val_256_ = lean_ctor_get(v___x_255_, 0);
v_inv_257_ = lean_ctor_get(v___x_255_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_266_ == 0)
{
v___x_259_ = v___x_255_;
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_inv_257_);
lean_inc(v_val_256_);
lean_dec(v___x_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_toMul_251_);
v___x_261_ = lean_apply_2(v_toMul_251_, v_val_253_, v_val_256_);
v___x_262_ = lean_apply_2(v_toMul_251_, v_inv_257_, v_inv_254_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_262_);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1___lam__0___boxed(lean_object* v___x_267_, lean_object* v___f_268_, lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v___x_271_, lean_object* v_m_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1___lam__0(v___x_267_, v___f_268_, v___x_269_, v___x_270_, v___x_271_, v_m_272_);
lean_dec_ref(v___x_267_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1(lean_object* v_X_274_, lean_object* v___x_275_, lean_object* v_00_u03c8_276_, lean_object* v_n_277_, lean_object* v_k_278_, lean_object* v_rS_279_){
_start:
{
lean_object* v_fieldK_280_; lean_object* v_toCommRing_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___f_289_; 
v_fieldK_280_ = lean_ctor_get(v_X_274_, 2);
v_toCommRing_281_ = lean_ctor_get(v_fieldK_280_, 0);
v___x_282_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_281_);
v___x_283_ = lean_box(0);
lean_inc(v_rS_279_);
lean_inc(v_k_278_);
v___x_284_ = lp_tree_Formalism_L2_Col_SPsym(v_n_277_, v_k_278_, v_rS_279_);
lean_inc_n(v_n_277_, 2);
lean_inc(v_00_u03c8_276_);
lean_inc_ref_n(v_X_274_, 2);
v___x_285_ = lp_tree_Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8(v_X_274_, v___x_275_, v_00_u03c8_276_, v_n_277_, v_n_277_, v___x_283_, v___x_284_);
v___f_286_ = ((lean_object*)(lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0));
v___x_287_ = lp_tree_MonoidHom_toHomUnits___at___00Formalism_L2_Col_supChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__8_spec__10(v_X_274_, v___x_275_, v_00_u03c8_276_);
v___f_288_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_offHom___at___00Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1_spec__1___lam__0), 6, 5);
lean_closure_set(v___f_288_, 0, v_X_274_);
lean_closure_set(v___f_288_, 1, v___x_275_);
lean_closure_set(v___f_288_, 2, v_n_277_);
lean_closure_set(v___f_288_, 3, v_k_278_);
lean_closure_set(v___f_288_, 4, v_rS_279_);
v___f_289_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1___lam__0___boxed), 6, 5);
lean_closure_set(v___f_289_, 0, v___x_282_);
lean_closure_set(v___f_289_, 1, v___f_286_);
lean_closure_set(v___f_289_, 2, v___x_285_);
lean_closure_set(v___f_289_, 3, v___f_288_);
lean_closure_set(v___f_289_, 4, v___x_287_);
return v___f_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsym___redArg(lean_object* v_X_290_, lean_object* v_R_291_, lean_object* v_Ch_292_, lean_object* v_w_293_){
_start:
{
lean_object* v_k_294_; lean_object* v_psi0_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_k_294_ = lean_ctor_get(v_R_291_, 1);
lean_inc(v_k_294_);
v_psi0_295_ = lean_ctor_get(v_Ch_292_, 0);
lean_inc(v_psi0_295_);
lean_dec_ref(v_Ch_292_);
v___x_296_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_291_);
v___x_297_ = lp_tree_Formalism_BasicNotions_Ranks_rS(v_R_291_);
lean_dec_ref(v_R_291_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v_psi0_295_, v_w_293_);
v___x_300_ = lp_tree_Formalism_L2_Col_chiSym___at___00Formalism_L2_Col_rPsym_spec__1(v_X_290_, v_w_293_, v___x_299_, v___x_296_, v_k_294_, v___x_297_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsym(lean_object* v_X_302_, lean_object* v_Pr_303_, lean_object* v_R_304_, lean_object* v_Ch_305_, lean_object* v_w_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lp_tree_Formalism_L2_Col_rPsym___redArg(v_X_302_, v_R_304_, v_Ch_305_, v_w_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rPsym___boxed(lean_object* v_X_308_, lean_object* v_Pr_309_, lean_object* v_R_310_, lean_object* v_Ch_311_, lean_object* v_w_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = lp_tree_Formalism_L2_Col_rPsym(v_X_308_, v_Pr_309_, v_R_310_, v_Ch_311_, v_w_312_);
lean_dec_ref(v_Pr_309_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg___lam__0(lean_object* v_toMonoid_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; lean_object* v_toOne_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v___x_316_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_314_);
v_toOne_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v___x_316_, 1);
lean_dec(v_unused_325_);
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_toOne_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
lean_inc(v_toOne_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_toOne_317_);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_toOne_317_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_toOne_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg___lam__0___boxed(lean_object* v_toMonoid_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = lp_tree_Formalism_L2_Col_rKg___redArg___lam__0(v_toMonoid_326_, v_x_327_);
lean_dec_ref(v_x_327_);
lean_dec_ref(v_toMonoid_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg(lean_object* v_X_329_){
_start:
{
lean_object* v_fieldK_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_toSemiring_333_; lean_object* v_toMonoid_334_; lean_object* v___x_335_; lean_object* v___f_336_; lean_object* v___x_337_; 
v_fieldK_330_ = lean_ctor_get(v_X_329_, 2);
v___x_331_ = lp_mathlib_Field_toSemifield___redArg(v_fieldK_330_);
v___x_332_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_331_);
v_toSemiring_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_toSemiring_333_);
lean_dec_ref(v___x_332_);
v_toMonoid_334_ = lean_ctor_get(v_toSemiring_333_, 1);
lean_inc_ref(v_toMonoid_334_);
lean_dec_ref(v_toSemiring_333_);
v___x_335_ = lean_box(0);
v___f_336_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_rKg___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_336_, 0, v_toMonoid_334_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___f_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___redArg___boxed(lean_object* v_X_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = lp_tree_Formalism_L2_Col_rKg___redArg(v_X_338_);
lean_dec_ref(v_X_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg(lean_object* v_X_340_, lean_object* v_Pr_341_, lean_object* v_R_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lp_tree_Formalism_L2_Col_rKg___redArg(v_X_340_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rKg___boxed(lean_object* v_X_345_, lean_object* v_Pr_346_, lean_object* v_R_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = lp_tree_Formalism_L2_Col_rKg(v_X_345_, v_Pr_346_, v_R_347_, v_x_348_);
lean_dec_ref(v_R_347_);
lean_dec_ref(v_Pr_346_);
lean_dec_ref(v_X_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_f_350_, lean_object* v_n_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_1(v_f_350_, v_n_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg(lean_object* v_f_353_){
_start:
{
lean_object* v___f_354_; 
v___f_354_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg___lam__0), 2, 1);
lean_closure_set(v___f_354_, 0, v_f_353_);
return v___f_354_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg___lam__0(lean_object* v_n_355_, lean_object* v_r_356_, lean_object* v_M_357_){
_start:
{
lean_object* v_val_358_; lean_object* v_inv_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v_val_358_ = lean_ctor_get(v_M_357_, 0);
v_inv_359_ = lean_ctor_get(v_M_357_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_M_357_);
if (v_isSharedCheck_368_ == 0)
{
v___x_361_ = v_M_357_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_inv_359_);
lean_inc(v_val_358_);
lean_dec(v_M_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_inc(v_r_356_);
lean_inc(v_n_355_);
v___x_363_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_restr___boxed), 7, 5);
lean_closure_set(v___x_363_, 0, v_n_355_);
lean_closure_set(v___x_363_, 1, lean_box(0));
lean_closure_set(v___x_363_, 2, v_r_356_);
lean_closure_set(v___x_363_, 3, lean_box(0));
lean_closure_set(v___x_363_, 4, v_val_358_);
v___x_364_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_restr___boxed), 7, 5);
lean_closure_set(v___x_364_, 0, v_n_355_);
lean_closure_set(v___x_364_, 1, lean_box(0));
lean_closure_set(v___x_364_, 2, v_r_356_);
lean_closure_set(v___x_364_, 3, lean_box(0));
lean_closure_set(v___x_364_, 4, v_inv_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_364_);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg(lean_object* v_n_369_, lean_object* v_r_370_){
_start:
{
lean_object* v___f_371_; 
v___f_371_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_371_, 0, v_n_369_);
lean_closure_set(v___f_371_, 1, v_r_370_);
return v___f_371_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg(lean_object* v_X_372_, lean_object* v___x_373_, lean_object* v_n_374_, lean_object* v_r_375_, lean_object* v_bl_376_, lean_object* v_H_u2080_377_){
_start:
{
lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; 
v___f_378_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_378_, 0, v_n_374_);
lean_closure_set(v___f_378_, 1, v_r_375_);
v___f_379_ = ((lean_object*)(lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0));
v___f_380_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_380_, 0, v___f_379_);
lean_closure_set(v___f_380_, 1, v___f_378_);
v___f_381_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg___lam__0), 2, 1);
lean_closure_set(v___f_381_, 0, v___f_380_);
return v___f_381_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg___boxed(lean_object* v_X_382_, lean_object* v___x_383_, lean_object* v_n_384_, lean_object* v_r_385_, lean_object* v_bl_386_, lean_object* v_H_u2080_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg(v_X_382_, v___x_383_, v_n_384_, v_r_385_, v_bl_386_, v_H_u2080_387_);
lean_dec(v_bl_386_);
lean_dec_ref(v_X_382_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg___lam__0(lean_object* v___x_389_, lean_object* v___x_390_, lean_object* v_lam_u2080_391_, lean_object* v___f_392_, lean_object* v___x_393_, lean_object* v_m_394_){
_start:
{
lean_object* v___x_395_; lean_object* v_toMul_396_; lean_object* v___x_397_; lean_object* v_val_398_; lean_object* v_inv_399_; lean_object* v___x_400_; lean_object* v_val_401_; lean_object* v_inv_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v___x_395_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_389_);
v_toMul_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc(v_toMul_396_);
lean_dec_ref(v___x_395_);
lean_inc_ref(v_m_394_);
v___x_397_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___x_390_, v_lam_u2080_391_, v_m_394_);
v_val_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_398_);
v_inv_399_ = lean_ctor_get(v___x_397_, 1);
lean_inc(v_inv_399_);
lean_dec(v___x_397_);
v___x_400_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___f_392_, v___x_393_, v_m_394_);
v_val_401_ = lean_ctor_get(v___x_400_, 0);
v_inv_402_ = lean_ctor_get(v___x_400_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_411_ == 0)
{
v___x_404_ = v___x_400_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_inv_402_);
lean_inc(v_val_401_);
lean_dec(v___x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
lean_inc(v_toMul_396_);
v___x_406_ = lean_apply_2(v_toMul_396_, v_val_398_, v_val_401_);
v___x_407_ = lean_apply_2(v_toMul_396_, v_inv_402_, v_inv_399_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_407_);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg___lam__0___boxed(lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v_lam_u2080_414_, lean_object* v___f_415_, lean_object* v___x_416_, lean_object* v_m_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg___lam__0(v___x_412_, v___x_413_, v_lam_u2080_414_, v___f_415_, v___x_416_, v_m_417_);
lean_dec_ref(v___x_412_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg(lean_object* v_X_419_, lean_object* v___x_420_, lean_object* v_n_421_, lean_object* v_r_422_, lean_object* v_bl_423_, lean_object* v_H_u2080_424_, lean_object* v_lam_u2080_425_, lean_object* v_00_u03c7_426_){
_start:
{
lean_object* v_fieldK_427_; lean_object* v_toCommRing_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___f_433_; 
v_fieldK_427_ = lean_ctor_get(v_X_419_, 2);
v_toCommRing_428_ = lean_ctor_get(v_fieldK_427_, 0);
v___x_429_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_428_);
lean_inc(v_r_422_);
lean_inc(v_n_421_);
v___x_430_ = lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg(v_X_419_, v___x_420_, v_n_421_, v_r_422_, v_bl_423_, v_H_u2080_424_);
v___x_431_ = lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10(v_X_419_, v___x_420_, v_00_u03c7_426_, v_n_421_, v_r_422_, v_bl_423_);
v___f_432_ = ((lean_object*)(lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0));
v___f_433_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_433_, 0, v___x_429_);
lean_closure_set(v___f_433_, 1, v___x_430_);
lean_closure_set(v___f_433_, 2, v_lam_u2080_425_);
lean_closure_set(v___f_433_, 3, v___f_432_);
lean_closure_set(v___f_433_, 4, v___x_431_);
return v___f_433_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_comap___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__2(lean_object* v_X_434_, lean_object* v___x_435_, lean_object* v_n_436_, lean_object* v___x_437_, lean_object* v_r_438_, lean_object* v_f_439_, lean_object* v_H_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_box(0);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_comap___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__2___boxed(lean_object* v_X_442_, lean_object* v___x_443_, lean_object* v_n_444_, lean_object* v___x_445_, lean_object* v_r_446_, lean_object* v_f_447_, lean_object* v_H_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = lp_tree_Subgroup_comap___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__2(v_X_442_, v___x_443_, v_n_444_, v___x_445_, v_r_446_, v_f_447_, v_H_448_);
lean_dec_ref(v_f_447_);
lean_dec(v_r_446_);
lean_dec(v_n_444_);
lean_dec_ref(v_X_442_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_map___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__3(lean_object* v_X_450_, lean_object* v___x_451_, lean_object* v_n_452_, lean_object* v___x_453_, lean_object* v_f_454_, lean_object* v_H_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_map___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__3___boxed(lean_object* v_X_457_, lean_object* v___x_458_, lean_object* v_n_459_, lean_object* v___x_460_, lean_object* v_f_461_, lean_object* v_H_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = lp_tree_Subgroup_map___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__3(v_X_457_, v___x_458_, v_n_459_, v___x_460_, v_f_461_, v_H_462_);
lean_dec_ref(v_f_461_);
lean_dec(v_n_459_);
lean_dec_ref(v_X_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___lam__0(lean_object* v_self_464_){
_start:
{
lean_inc_ref(v_self_464_);
return v_self_464_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___lam__0___boxed(lean_object* v_self_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___lam__0(v_self_465_);
lean_dec_ref(v_self_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0(lean_object* v_X_468_, lean_object* v___x_469_, lean_object* v_n_470_, lean_object* v_H_471_){
_start:
{
lean_object* v___f_472_; 
v___f_472_ = ((lean_object*)(lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___closed__0));
return v___f_472_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0___boxed(lean_object* v_X_473_, lean_object* v___x_474_, lean_object* v_n_475_, lean_object* v_H_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__0(v_X_473_, v___x_474_, v_n_475_, v_H_476_);
lean_dec(v_n_475_);
lean_dec_ref(v_X_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___redArg(lean_object* v_X_478_, lean_object* v___x_479_, lean_object* v_n_480_, lean_object* v_r_481_, lean_object* v_bl_482_, lean_object* v_H_u2080_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_box(0);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___redArg___boxed(lean_object* v_X_485_, lean_object* v___x_486_, lean_object* v_n_487_, lean_object* v_r_488_, lean_object* v_bl_489_, lean_object* v_H_u2080_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___redArg(v_X_485_, v___x_486_, v_n_487_, v_r_488_, v_bl_489_, v_H_u2080_490_);
lean_dec(v_bl_489_);
lean_dec(v_r_488_);
lean_dec(v_n_487_);
lean_dec_ref(v_X_485_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rowTyG(lean_object* v_X_492_, lean_object* v_Pr_493_, lean_object* v_R_494_, lean_object* v_Ch_495_, lean_object* v_P_496_, lean_object* v_w_497_){
_start:
{
lean_object* v_m_498_; lean_object* v_t_499_; lean_object* v___x_500_; lean_object* v_H_501_; lean_object* v_lam_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_517_; 
v_m_498_ = lean_ctor_get(v_R_494_, 2);
v_t_499_ = lean_ctor_get(v_R_494_, 3);
v___x_500_ = lean_apply_1(v_P_496_, v_w_497_);
v_H_501_ = lean_ctor_get(v___x_500_, 0);
v_lam_502_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_517_ == 0)
{
v___x_504_ = v___x_500_;
v_isShared_505_ = v_isSharedCheck_517_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_lam_502_);
lean_inc(v_H_501_);
lean_dec(v___x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_517_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_506_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_494_, v_m_498_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_sub(v___x_506_, v___x_507_);
lean_dec(v___x_506_);
v___x_509_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_494_);
lean_inc(v_t_499_);
lean_inc(v_m_498_);
v___x_510_ = l_List_replicateTR___redArg(v_m_498_, v_t_499_);
v___x_511_ = lean_box(0);
lean_inc_ref(v_X_492_);
v___x_512_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_chiAt___boxed), 6, 5);
lean_closure_set(v___x_512_, 0, v_X_492_);
lean_closure_set(v___x_512_, 1, v_Pr_493_);
lean_closure_set(v___x_512_, 2, v_R_494_);
lean_closure_set(v___x_512_, 3, v_Ch_495_);
lean_closure_set(v___x_512_, 4, v_w_497_);
v___x_513_ = lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg(v_X_492_, v_w_497_, v___x_508_, v___x_509_, v___x_510_, v_H_501_, v_lam_502_, v___x_512_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_513_);
lean_ctor_set(v___x_504_, 0, v___x_511_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0(lean_object* v_X_518_, lean_object* v___x_519_, lean_object* v_n_520_, lean_object* v_r_521_, lean_object* v_h_522_, lean_object* v_bl_523_, lean_object* v_H_u2080_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_box(0);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0___boxed(lean_object* v_X_526_, lean_object* v___x_527_, lean_object* v_n_528_, lean_object* v_r_529_, lean_object* v_h_530_, lean_object* v_bl_531_, lean_object* v_H_u2080_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = lp_tree_Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0(v_X_526_, v___x_527_, v_n_528_, v_r_529_, v_h_530_, v_bl_531_, v_H_u2080_532_);
lean_dec(v_bl_531_);
lean_dec(v_r_529_);
lean_dec(v_n_528_);
lean_dec_ref(v_X_526_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1(lean_object* v_X_534_, lean_object* v___x_535_, lean_object* v_n_536_, lean_object* v_r_537_, lean_object* v_h_538_, lean_object* v_bl_539_, lean_object* v_H_u2080_540_, lean_object* v_lam_u2080_541_, lean_object* v_00_u03c7_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg(v_X_534_, v___x_535_, v_n_536_, v_r_537_, v_bl_539_, v_H_u2080_540_, v_lam_u2080_541_, v_00_u03c7_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1(lean_object* v_X_544_, lean_object* v___x_545_, lean_object* v_n_546_, lean_object* v_r_547_, lean_object* v_h_548_, lean_object* v_bl_549_){
_start:
{
lean_object* v___f_550_; 
v___f_550_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_550_, 0, v_n_546_);
lean_closure_set(v___f_550_, 1, v_r_547_);
return v___f_550_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1___boxed(lean_object* v_X_551_, lean_object* v___x_552_, lean_object* v_n_553_, lean_object* v_r_554_, lean_object* v_h_555_, lean_object* v_bl_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = lp_tree_Formalism_L2_Col_blk0___at___00Formalism_L2_Col_HPar___at___00Formalism_L2_Col_rowTyG_spec__0_spec__1(v_X_551_, v___x_552_, v_n_553_, v_r_554_, v_h_555_, v_bl_556_);
lean_dec(v_bl_556_);
lean_dec_ref(v_X_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6(lean_object* v_X_558_, lean_object* v___x_559_, lean_object* v_n_560_, lean_object* v___x_561_, lean_object* v_r_562_, lean_object* v_inst_563_, lean_object* v_f_564_, lean_object* v_s_565_, lean_object* v_h_566_){
_start:
{
lean_object* v___f_567_; 
v___f_567_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___redArg___lam__0), 2, 1);
lean_closure_set(v___f_567_, 0, v_f_564_);
return v___f_567_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6___boxed(lean_object* v_X_568_, lean_object* v___x_569_, lean_object* v_n_570_, lean_object* v___x_571_, lean_object* v_r_572_, lean_object* v_inst_573_, lean_object* v_f_574_, lean_object* v_s_575_, lean_object* v_h_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = lp_tree_MonoidHom_codRestrict___at___00Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5_spec__6(v_X_568_, v___x_569_, v_n_570_, v___x_571_, v_r_572_, v_inst_573_, v_f_574_, v_s_575_, v_h_576_);
lean_dec(v_r_572_);
lean_dec(v_n_570_);
lean_dec_ref(v_X_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5(lean_object* v_X_578_, lean_object* v___x_579_, lean_object* v_n_580_, lean_object* v_r_581_, lean_object* v_h_582_, lean_object* v_bl_583_, lean_object* v_H_u2080_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___redArg(v_X_578_, v___x_579_, v_n_580_, v_r_581_, v_bl_583_, v_H_u2080_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5___boxed(lean_object* v_X_586_, lean_object* v___x_587_, lean_object* v_n_588_, lean_object* v_r_589_, lean_object* v_h_590_, lean_object* v_bl_591_, lean_object* v_H_u2080_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = lp_tree_Formalism_L2_Col_HPar0___at___00Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1_spec__5(v_X_586_, v___x_587_, v_n_588_, v_r_589_, v_h_590_, v_bl_591_, v_H_u2080_592_);
lean_dec(v_bl_591_);
lean_dec_ref(v_X_586_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0(lean_object* v_X_594_, lean_object* v___x_595_, lean_object* v_n_596_, lean_object* v_r_597_, lean_object* v_bl_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0___boxed(lean_object* v_X_600_, lean_object* v___x_601_, lean_object* v_n_602_, lean_object* v_r_603_, lean_object* v_bl_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = lp_tree_Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0(v_X_600_, v___x_601_, v_n_602_, v_r_603_, v_bl_604_);
lean_dec(v_bl_604_);
lean_dec(v_r_603_);
lean_dec(v_n_602_);
lean_dec_ref(v_X_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2(lean_object* v_X_606_, lean_object* v___x_607_, lean_object* v_00_u03c7_608_, lean_object* v_n_609_, lean_object* v_r_610_, lean_object* v_bl_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___f_614_; 
v___x_612_ = lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10(v_X_606_, v___x_607_, v_00_u03c7_608_, v_n_609_, v_r_610_, v_bl_611_);
v___f_613_ = ((lean_object*)(lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0));
v___f_614_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_614_, 0, v___f_613_);
lean_closure_set(v___f_614_, 1, v___x_612_);
return v___f_614_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1(lean_object* v_X_615_, lean_object* v___x_616_, lean_object* v_00_u03c7_617_, lean_object* v_n_618_, lean_object* v_r_619_, lean_object* v_t_620_, lean_object* v_j_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_List_replicateTR___redArg(v_j_621_, v_t_620_);
v___x_623_ = lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2(v_X_615_, v___x_616_, v_00_u03c7_617_, v_n_618_, v_r_619_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_rowTyK(lean_object* v_X_624_, lean_object* v_Pr_625_, lean_object* v_R_626_, lean_object* v_Ch_627_, lean_object* v_w_628_){
_start:
{
lean_object* v_m_629_; lean_object* v_t_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_m_629_ = lean_ctor_get(v_R_626_, 2);
lean_inc(v_m_629_);
v_t_630_ = lean_ctor_get(v_R_626_, 3);
lean_inc(v_t_630_);
v___x_631_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_626_, v_m_629_);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_sub(v___x_631_, v___x_632_);
lean_dec(v___x_631_);
v___x_634_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_626_);
v___x_635_ = lean_box(0);
lean_inc_ref(v_X_624_);
v___x_636_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_chiAt___boxed), 6, 5);
lean_closure_set(v___x_636_, 0, v_X_624_);
lean_closure_set(v___x_636_, 1, v_Pr_625_);
lean_closure_set(v___x_636_, 2, v_R_626_);
lean_closure_set(v___x_636_, 3, v_Ch_627_);
lean_closure_set(v___x_636_, 4, v_w_628_);
v___x_637_ = lp_tree_Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1(v_X_624_, v_w_628_, v___x_636_, v___x_633_, v___x_634_, v_t_630_, v_m_629_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1_spec__2(lean_object* v_X_639_, lean_object* v___x_640_, lean_object* v_n_641_, lean_object* v___x_642_, lean_object* v_r_643_, lean_object* v_bl_644_, lean_object* v_mc_645_, lean_object* v_f_646_, lean_object* v_S_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = lean_box(0);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_X_649_, lean_object* v___x_650_, lean_object* v_n_651_, lean_object* v___x_652_, lean_object* v_r_653_, lean_object* v_bl_654_, lean_object* v_mc_655_, lean_object* v_f_656_, lean_object* v_S_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1_spec__2(v_X_649_, v___x_650_, v_n_651_, v___x_652_, v_r_653_, v_bl_654_, v_mc_655_, v_f_656_, v_S_657_);
lean_dec(v_f_656_);
lean_dec(v_bl_654_);
lean_dec(v_r_653_);
lean_dec(v_n_651_);
lean_dec_ref(v_X_649_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___redArg(lean_object* v_X_659_, lean_object* v___x_660_, lean_object* v_n_661_, lean_object* v___x_662_, lean_object* v_r_663_, lean_object* v_bl_664_, lean_object* v_f_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_box(0);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_X_667_, lean_object* v___x_668_, lean_object* v_n_669_, lean_object* v___x_670_, lean_object* v_r_671_, lean_object* v_bl_672_, lean_object* v_f_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___redArg(v_X_667_, v___x_668_, v_n_669_, v___x_670_, v_r_671_, v_bl_672_, v_f_673_);
lean_dec(v_f_673_);
lean_dec(v_bl_672_);
lean_dec(v_r_671_);
lean_dec(v_n_669_);
lean_dec_ref(v_X_667_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0(lean_object* v_X_675_, lean_object* v___x_676_, lean_object* v_n_677_, lean_object* v___x_678_, lean_object* v_r_679_, lean_object* v_bl_680_, lean_object* v_f_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0___boxed(lean_object* v_X_683_, lean_object* v___x_684_, lean_object* v_n_685_, lean_object* v___x_686_, lean_object* v_r_687_, lean_object* v_bl_688_, lean_object* v_f_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = lp_tree_MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0(v_X_683_, v___x_684_, v_n_685_, v___x_686_, v_r_687_, v_bl_688_, v_f_689_);
lean_dec(v_f_689_);
lean_dec(v_bl_688_);
lean_dec(v_r_687_);
lean_dec(v_n_685_);
lean_dec_ref(v_X_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___lam__0(lean_object* v_M_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_val_694_; lean_object* v___x_695_; 
v_val_694_ = lean_ctor_get(v_M_691_, 0);
lean_inc(v_val_694_);
lean_dec_ref(v_M_691_);
v___x_695_ = lp_mathlib_Matrix_toBlock___redArg(v_val_694_, v___y_692_, v___y_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3(lean_object* v_r_697_, lean_object* v_bl_698_, lean_object* v_X_699_, lean_object* v___x_700_, lean_object* v_n_701_, lean_object* v_c_702_){
_start:
{
lean_object* v___f_703_; 
v___f_703_ = ((lean_object*)(lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___closed__0));
return v___f_703_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3___boxed(lean_object* v_r_704_, lean_object* v_bl_705_, lean_object* v_X_706_, lean_object* v___x_707_, lean_object* v_n_708_, lean_object* v_c_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = lp_tree_Formalism_L2_Col_blkHom___at___00Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14_spec__18___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__3(v_r_704_, v_bl_705_, v_X_706_, v___x_707_, v_n_708_, v_c_709_);
lean_dec(v_c_709_);
lean_dec(v_n_708_);
lean_dec_ref(v_X_706_);
lean_dec(v_bl_705_);
lean_dec(v_r_704_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1(lean_object* v_X_711_, lean_object* v___x_712_, lean_object* v_n_713_, lean_object* v___x_714_, lean_object* v_r_715_, lean_object* v_bl_716_, lean_object* v_mc_717_, lean_object* v_f_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_box(0);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1___boxed(lean_object* v_X_720_, lean_object* v___x_721_, lean_object* v_n_722_, lean_object* v___x_723_, lean_object* v_r_724_, lean_object* v_bl_725_, lean_object* v_mc_726_, lean_object* v_f_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_L2_Col_HK___at___00Formalism_L2_Col_rowTyK_spec__0_spec__0_spec__1(v_X_720_, v___x_721_, v_n_722_, v___x_723_, v_r_724_, v_bl_725_, v_mc_726_, v_f_727_);
lean_dec(v_f_727_);
lean_dec(v_bl_725_);
lean_dec(v_r_724_);
lean_dec(v_n_722_);
lean_dec_ref(v_X_720_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___redArg(lean_object* v_f_729_){
_start:
{
lean_inc_ref(v_f_729_);
return v_f_729_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___redArg___boxed(lean_object* v_f_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___redArg(v_f_730_);
lean_dec_ref(v_f_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0(lean_object* v_X_732_, lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v___x_735_, lean_object* v_f_736_, lean_object* v_map__mul_737_){
_start:
{
lean_inc_ref(v_f_736_);
return v_f_736_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0___boxed(lean_object* v_X_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v___x_741_, lean_object* v_f_742_, lean_object* v_map__mul_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_mtTyG_spec__0(v_X_738_, v___x_739_, v___x_740_, v___x_741_, v_f_742_, v_map__mul_743_);
lean_dec_ref(v_f_742_);
lean_dec(v___x_740_);
lean_dec_ref(v_X_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__0(lean_object* v_j_745_, lean_object* v_X_746_, lean_object* v_R_747_, lean_object* v_Ch_748_, lean_object* v_w_749_, lean_object* v_x_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_194__overap_754_; lean_object* v___x_755_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_sub(v_j_745_, v___x_752_);
v___x_194__overap_754_ = lp_tree_Formalism_L2_Col_chiAt___redArg(v_X_746_, v_R_747_, v_Ch_748_, v_w_749_, v___x_753_);
v___x_755_ = lean_apply_1(v___x_194__overap_754_, v___y_751_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__0___boxed(lean_object* v_j_756_, lean_object* v_X_757_, lean_object* v_R_758_, lean_object* v_Ch_759_, lean_object* v_w_760_, lean_object* v_x_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__0(v_j_756_, v_X_757_, v_R_758_, v_Ch_759_, v_w_760_, v_x_761_, v___y_762_);
lean_dec(v_x_761_);
lean_dec_ref(v_R_758_);
lean_dec_ref(v_X_757_);
lean_dec(v_j_756_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__1(lean_object* v_X_764_, lean_object* v_w_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_H_769_, lean_object* v_lam_770_, lean_object* v___f_771_, lean_object* v_g_772_){
_start:
{
lean_object* v___x_199__overap_773_; lean_object* v___x_774_; lean_object* v_val_775_; lean_object* v_inv_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v___x_199__overap_773_ = lp_tree_Formalism_L2_Col_lamPar___at___00Formalism_L2_Col_rowTyG_spec__1___redArg(v_X_764_, v_w_765_, v___x_766_, v___x_767_, v___x_768_, v_H_769_, v_lam_770_, v___f_771_);
v___x_774_ = lean_apply_1(v___x_199__overap_773_, v_g_772_);
v_val_775_ = lean_ctor_get(v___x_774_, 0);
v_inv_776_ = lean_ctor_get(v___x_774_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_774_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_inv_776_);
lean_inc(v_val_775_);
lean_dec(v___x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_val_775_);
lean_ctor_set(v___x_778_, 0, v_inv_776_);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_inv_776_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_val_775_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___redArg(lean_object* v_X_784_, lean_object* v_R_785_, lean_object* v_Ch_786_, lean_object* v_P_787_, lean_object* v_j_788_, lean_object* v_w_789_){
_start:
{
lean_object* v_t_790_; lean_object* v___x_791_; lean_object* v_H_792_; lean_object* v_lam_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
v_t_790_ = lean_ctor_get(v_R_785_, 3);
lean_inc(v_t_790_);
v___x_791_ = lean_apply_1(v_P_787_, v_w_789_);
v_H_792_ = lean_ctor_get(v___x_791_, 0);
v_lam_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_807_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_lam_793_);
lean_inc(v_H_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc_ref(v_R_785_);
lean_inc_ref(v_X_784_);
v___f_797_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_797_, 0, v_j_788_);
lean_closure_set(v___f_797_, 1, v_X_784_);
lean_closure_set(v___f_797_, 2, v_R_785_);
lean_closure_set(v___f_797_, 3, v_Ch_786_);
lean_closure_set(v___f_797_, 4, v_w_789_);
v___x_798_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_785_);
v___x_799_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_785_);
lean_dec_ref(v_R_785_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v_t_790_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___f_802_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_mtTyG___redArg___lam__1), 9, 8);
lean_closure_set(v___f_802_, 0, v_X_784_);
lean_closure_set(v___f_802_, 1, v_w_789_);
lean_closure_set(v___f_802_, 2, v___x_798_);
lean_closure_set(v___f_802_, 3, v___x_799_);
lean_closure_set(v___f_802_, 4, v___x_801_);
lean_closure_set(v___f_802_, 5, v_H_792_);
lean_closure_set(v___f_802_, 6, v_lam_793_);
lean_closure_set(v___f_802_, 7, v___f_797_);
v___x_803_ = lean_box(0);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___f_802_);
lean_ctor_set(v___x_795_, 0, v___x_803_);
v___x_805_ = v___x_795_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___f_802_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG(lean_object* v_X_808_, lean_object* v_Pr_809_, lean_object* v_R_810_, lean_object* v_Ch_811_, lean_object* v_P_812_, lean_object* v_j_813_, lean_object* v_w_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = lp_tree_Formalism_L2_Col_mtTyG___redArg(v_X_808_, v_R_810_, v_Ch_811_, v_P_812_, v_j_813_, v_w_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyG___boxed(lean_object* v_X_816_, lean_object* v_Pr_817_, lean_object* v_R_818_, lean_object* v_Ch_819_, lean_object* v_P_820_, lean_object* v_j_821_, lean_object* v_w_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = lp_tree_Formalism_L2_Col_mtTyG(v_X_816_, v_Pr_817_, v_R_818_, v_Ch_819_, v_P_820_, v_j_821_, v_w_822_);
lean_dec_ref(v_Pr_817_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__1(lean_object* v_X_824_, lean_object* v___x_825_, lean_object* v_n_826_, lean_object* v___x_827_, lean_object* v___f_828_, lean_object* v_s_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v_s_829_, v___x_831_);
v___x_833_ = lp_tree_Formalism_L2_Col_blkDet___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__14(v_X_824_, v___x_825_, v_n_826_, v___x_827_, v___x_832_);
v___x_834_ = lp_mathlib_OneHom_comp___redArg___lam__0(v___x_833_, v___f_828_, v___y_830_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__1___boxed(lean_object* v_X_835_, lean_object* v___x_836_, lean_object* v_n_837_, lean_object* v___x_838_, lean_object* v___f_839_, lean_object* v_s_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__1(v_X_835_, v___x_836_, v_n_837_, v___x_838_, v___f_839_, v_s_840_, v___y_841_);
lean_dec(v_s_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__0(lean_object* v_00_u03c7j_843_, lean_object* v_g_844_){
_start:
{
lean_object* v___x_845_; lean_object* v_val_846_; lean_object* v_inv_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v___x_845_ = lean_apply_1(v_00_u03c7j_843_, v_g_844_);
v_val_846_ = lean_ctor_get(v___x_845_, 0);
v_inv_847_ = lean_ctor_get(v___x_845_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_inv_847_);
lean_inc(v_val_846_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v_val_846_);
lean_ctor_set(v___x_849_, 0, v_inv_847_);
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_inv_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_val_846_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2(lean_object* v_X_855_, lean_object* v___x_856_, lean_object* v_00_u03c7j_857_, lean_object* v_X_858_, lean_object* v___x_859_, lean_object* v_n_860_, lean_object* v_a_861_, lean_object* v_bl_862_){
_start:
{
lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___f_863_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_863_, 0, v_00_u03c7j_857_);
lean_inc(v_bl_862_);
v___x_864_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_coarse___boxed), 3, 2);
lean_closure_set(v___x_864_, 0, v_a_861_);
lean_closure_set(v___x_864_, 1, v_bl_862_);
lean_inc(v_n_860_);
lean_inc_ref(v_X_858_);
v___f_865_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___lam__1___boxed), 7, 5);
lean_closure_set(v___f_865_, 0, v_X_858_);
lean_closure_set(v___f_865_, 1, v___x_859_);
lean_closure_set(v___f_865_, 2, v_n_860_);
lean_closure_set(v___f_865_, 3, v___x_864_);
lean_closure_set(v___f_865_, 4, v___f_863_);
v___x_866_ = lean_box(0);
v___x_867_ = l_List_lengthTR___redArg(v_bl_862_);
lean_dec(v_bl_862_);
v___x_868_ = l_List_range(v___x_867_);
v___x_869_ = lp_tree_Finset_prod___at___00Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10_spec__15___redArg(v_X_858_, v___x_859_, v_n_860_, v___x_866_, v___x_868_, v___f_865_);
lean_dec(v_n_860_);
lean_dec_ref(v_X_858_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2___boxed(lean_object* v_X_870_, lean_object* v___x_871_, lean_object* v_00_u03c7j_872_, lean_object* v_X_873_, lean_object* v___x_874_, lean_object* v_n_875_, lean_object* v_a_876_, lean_object* v_bl_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2(v_X_870_, v___x_871_, v_00_u03c7j_872_, v_X_873_, v___x_874_, v_n_875_, v_a_876_, v_bl_877_);
lean_dec_ref(v_X_870_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2(lean_object* v_X_879_, lean_object* v___x_880_, lean_object* v_00_u03c7j_881_, lean_object* v_X_882_, lean_object* v___x_883_, lean_object* v_n_884_, lean_object* v_r_885_, lean_object* v_bl_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___f_889_; 
v___x_887_ = lp_tree_Formalism_L2_Col_detChar___at___00Formalism_L2_Col_lamGen___at___00Formalism_L2_Col_lamX___at___00Formalism_L2_Col_colLev_spec__4_spec__6_spec__10___at___00Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2_spec__2(v_X_879_, v___x_880_, v_00_u03c7j_881_, v_X_882_, v___x_883_, v_n_884_, v_r_885_, v_bl_886_);
v___f_888_ = ((lean_object*)(lp_tree_Formalism_L2_Col_rPsharp___redArg___closed__0));
v___f_889_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_889_, 0, v___f_888_);
lean_closure_set(v___f_889_, 1, v___x_887_);
return v___f_889_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2___boxed(lean_object* v_X_890_, lean_object* v___x_891_, lean_object* v_00_u03c7j_892_, lean_object* v_X_893_, lean_object* v___x_894_, lean_object* v_n_895_, lean_object* v_r_896_, lean_object* v_bl_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2(v_X_890_, v___x_891_, v_00_u03c7j_892_, v_X_893_, v___x_894_, v_n_895_, v_r_896_, v_bl_897_);
lean_dec_ref(v_X_890_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0(lean_object* v_X_899_, lean_object* v___x_900_, lean_object* v_00_u03c7j_901_, lean_object* v_n_902_, lean_object* v_r_903_, lean_object* v_t_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v_t_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
lean_inc_ref(v_X_899_);
v___x_907_ = lp_tree_Formalism_L2_Col_lamK___at___00Formalism_L2_Col_lamKJ___at___00Formalism_L2_Col_rowTyK_spec__1_spec__2___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__2(v_X_899_, v___x_900_, v_00_u03c7j_901_, v_X_899_, v___x_900_, v_n_902_, v_r_903_, v___x_906_);
lean_dec_ref(v_X_899_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK___redArg(lean_object* v_X_908_, lean_object* v_R_909_, lean_object* v_Ch_910_, lean_object* v_j_911_, lean_object* v_w_912_){
_start:
{
lean_object* v_t_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_t_913_ = lean_ctor_get(v_R_909_, 3);
lean_inc(v_t_913_);
v___x_914_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_909_);
v___x_915_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_909_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_sub(v_j_911_, v___x_917_);
v___x_919_ = lp_tree_Formalism_L2_Col_chiAt___redArg(v_X_908_, v_R_909_, v_Ch_910_, v_w_912_, v___x_918_);
lean_dec_ref(v_R_909_);
v___x_920_ = lp_tree_Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0(v_X_908_, v_w_912_, v___x_919_, v___x_914_, v___x_915_, v_t_913_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_916_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK___redArg___boxed(lean_object* v_X_922_, lean_object* v_R_923_, lean_object* v_Ch_924_, lean_object* v_j_925_, lean_object* v_w_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = lp_tree_Formalism_L2_Col_mtTyK___redArg(v_X_922_, v_R_923_, v_Ch_924_, v_j_925_, v_w_926_);
lean_dec(v_j_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK(lean_object* v_X_928_, lean_object* v_Pr_929_, lean_object* v_R_930_, lean_object* v_Ch_931_, lean_object* v_j_932_, lean_object* v_w_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lp_tree_Formalism_L2_Col_mtTyK___redArg(v_X_928_, v_R_930_, v_Ch_931_, v_j_932_, v_w_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mtTyK___boxed(lean_object* v_X_935_, lean_object* v_Pr_936_, lean_object* v_R_937_, lean_object* v_Ch_938_, lean_object* v_j_939_, lean_object* v_w_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = lp_tree_Formalism_L2_Col_mtTyK(v_X_935_, v_Pr_936_, v_R_937_, v_Ch_938_, v_j_939_, v_w_940_);
lean_dec(v_j_939_);
lean_dec_ref(v_Pr_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___redArg(lean_object* v_f_942_){
_start:
{
lean_inc_ref(v_f_942_);
return v_f_942_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___redArg___boxed(lean_object* v_f_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___redArg(v_f_943_);
lean_dec_ref(v_f_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0(lean_object* v_X_945_, lean_object* v___x_946_, lean_object* v_f_947_, lean_object* v_map__mul_948_){
_start:
{
lean_inc_ref(v_f_947_);
return v_f_947_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0___boxed(lean_object* v_X_949_, lean_object* v___x_950_, lean_object* v_f_951_, lean_object* v_map__mul_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_L2_Col_lamKV___at___00Formalism_L2_Col_mtTyK_spec__0_spec__0(v_X_949_, v___x_950_, v_f_951_, v_map__mul_952_);
lean_dec_ref(v_f_951_);
lean_dec_ref(v_X_949_);
return v_res_953_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_LevGCount(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_DecoFin(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefCol(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Tuples(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_LevGCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_DecoFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefCol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Tuples(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
