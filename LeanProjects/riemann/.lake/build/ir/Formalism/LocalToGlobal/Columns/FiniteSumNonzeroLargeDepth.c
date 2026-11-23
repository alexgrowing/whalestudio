// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.ColForms public import Formalism.LocalToGlobal.Columns.ColFormsLemmas public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice public import Formalism.LocalToGlobal.Columns.RowForms public import Formalism.LocalToGlobal.Columns.RowFormsSym public import Formalism.LocalToGlobal.Columns.CoefModB public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_symIdxInv(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_tree_Formalism_L2_Col_extG___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_prod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
extern lean_object* lp_mathlib_Nat_instLocallyFiniteOrder;
lean_object* lp_mathlib_Finset_Icc___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Matrix_toLin_x27___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_toMatrix_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_OneHom_id___lam__0___boxed(lean_object*);
lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FormG_incl_spec__3___lam__0(lean_object*, lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
lean_object* lp_tree_Formalism_L2_Col_piChar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_extU___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_Deco_act___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_castAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_smulRight___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SMul_comp_smul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_aBr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_aBr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_aBr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bBr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bBr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bBr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_nBr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_nBr___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_nBr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_upVar___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_upVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_upVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bExp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extUH___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extUH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extUH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extGH___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extGH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extGH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_res___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_res(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_res___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_fr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_fr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_fr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___closed__0 = (const lean_object*)&lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___closed__0 = (const lean_object*)&lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___closed__0 = (const lean_object*)&lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp___at___00Formalism_L2_Col_FrmG_incl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp___at___00Formalism_L2_Col_FrmG_incl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___closed__0 = (const lean_object*)&lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___closed__0 = (const lean_object*)&lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_OneHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FormG_incl_spec__3___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Ideal_primeCompl___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Ideal_primeCompl___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_locS___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_locS___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13___closed__0 = (const lean_object*)&lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_supp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_supp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Ufl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Ufl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_R1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_R1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_fixX(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_fixX___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_N1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_N1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Cbe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Cbe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_prX(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_prX___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_Loc_xx1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_homAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_homAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_divLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_divLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mulLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mulLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inFr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inFr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inFr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_sclLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_sclLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_LocE_scE___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_LocE_scE___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_scE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_scE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_lamY(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_lamY___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_parL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_parL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsharp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsharp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bd5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bd5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cOf___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_epsSg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_epsSg___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Col_epsSg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_epsSg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_epsSg;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_prXp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_prXp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_prXp___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_prXp___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Col_prXp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_funLeft___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Col_prXp___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_Col_prXp___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Col_prXp___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ybCpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ybCpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toFinPl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toFinPl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toFinPl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofFinPl___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofFinPl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofFinPl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_sumLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_sumLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC___redArg(lean_object* v_i_1_){
_start:
{
lean_inc(v_i_1_);
return v_i_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC___redArg___boxed(lean_object* v_i_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_L2_Col_Br_iC___redArg(v_i_2_);
lean_dec(v_i_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC(lean_object* v_N_4_, lean_object* v_n_5_, lean_object* v_hN_6_, lean_object* v_i_7_){
_start:
{
lean_inc(v_i_7_);
return v_i_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iC___boxed(lean_object* v_N_8_, lean_object* v_n_9_, lean_object* v_hN_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_Col_Br_iC(v_N_8_, v_n_9_, v_hN_10_, v_i_11_);
lean_dec(v_i_11_);
lean_dec(v_n_9_);
lean_dec(v_N_8_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS___redArg(lean_object* v_i_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_i_13_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS___redArg___boxed(lean_object* v_i_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_L2_Col_Br_iS___redArg(v_i_16_);
lean_dec(v_i_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS(lean_object* v_N_18_, lean_object* v_n_19_, lean_object* v_hN_20_, lean_object* v_i_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_tree_Formalism_L2_Col_Br_iS___redArg(v_i_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iS___boxed(lean_object* v_N_23_, lean_object* v_n_24_, lean_object* v_hN_25_, lean_object* v_i_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_L2_Col_Br_iS(v_N_23_, v_n_24_, v_hN_25_, v_i_26_);
lean_dec(v_i_26_);
lean_dec(v_n_24_);
lean_dec(v_N_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL___redArg(lean_object* v_n_28_){
_start:
{
lean_inc(v_n_28_);
return v_n_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL___redArg___boxed(lean_object* v_n_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_L2_Col_Br_iL___redArg(v_n_29_);
lean_dec(v_n_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL(lean_object* v_N_31_, lean_object* v_n_32_, lean_object* v_hN_33_){
_start:
{
lean_inc(v_n_32_);
return v_n_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_iL___boxed(lean_object* v_N_34_, lean_object* v_n_35_, lean_object* v_hN_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_L2_Col_Br_iL(v_N_34_, v_n_35_, v_hN_36_);
lean_dec(v_n_35_);
lean_dec(v_N_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_aBr___redArg(lean_object* v_lam_38_, lean_object* v_sg_39_, lean_object* v_i_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_inc(v_i_40_);
v___x_41_ = lean_apply_1(v_sg_39_, v_i_40_);
v___x_42_ = lp_tree_Formalism_L2_Col_Br_iS___redArg(v_i_40_);
lean_dec(v_i_40_);
v___x_43_ = lean_apply_1(v_lam_38_, v___x_42_);
v___x_44_ = lean_int_sub(v___x_41_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v___x_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_aBr(lean_object* v_N_45_, lean_object* v_n_46_, lean_object* v_hN_47_, lean_object* v_lam_48_, lean_object* v_sg_49_, lean_object* v_i_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_L2_Col_Br_aBr___redArg(v_lam_48_, v_sg_49_, v_i_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_aBr___boxed(lean_object* v_N_52_, lean_object* v_n_53_, lean_object* v_hN_54_, lean_object* v_lam_55_, lean_object* v_sg_56_, lean_object* v_i_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_L2_Col_Br_aBr(v_N_52_, v_n_53_, v_hN_54_, v_lam_55_, v_sg_56_, v_i_57_);
lean_dec(v_n_53_);
lean_dec(v_N_52_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bBr___redArg(lean_object* v_lam_59_, lean_object* v_sg_60_, lean_object* v_i_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_inc(v_i_61_);
v___x_62_ = lean_apply_1(v_lam_59_, v_i_61_);
v___x_63_ = lean_apply_1(v_sg_60_, v_i_61_);
v___x_64_ = lean_int_sub(v___x_62_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bBr(lean_object* v_N_65_, lean_object* v_n_66_, lean_object* v_hN_67_, lean_object* v_lam_68_, lean_object* v_sg_69_, lean_object* v_i_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_tree_Formalism_L2_Col_Br_bBr___redArg(v_lam_68_, v_sg_69_, v_i_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bBr___boxed(lean_object* v_N_72_, lean_object* v_n_73_, lean_object* v_hN_74_, lean_object* v_lam_75_, lean_object* v_sg_76_, lean_object* v_i_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_tree_Formalism_L2_Col_Br_bBr(v_N_72_, v_n_73_, v_hN_74_, v_lam_75_, v_sg_76_, v_i_77_);
lean_dec(v_n_73_);
lean_dec(v_N_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0___redArg___lam__0(lean_object* v_lam_79_, lean_object* v_sg_80_, lean_object* v_i_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lp_tree_Formalism_L2_Col_Br_aBr___redArg(v_lam_79_, v_sg_80_, v_i_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0___redArg(lean_object* v_n_83_, lean_object* v_lam_84_, lean_object* v_sg_85_){
_start:
{
lean_object* v___f_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___f_86_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Br_d0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_86_, 0, v_lam_84_);
lean_closure_set(v___f_86_, 1, v_sg_85_);
v___x_87_ = l_List_finRange(v_n_83_);
v___x_88_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_87_, v___f_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0(lean_object* v_N_89_, lean_object* v_n_90_, lean_object* v_hN_91_, lean_object* v_lam_92_, lean_object* v_sg_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_tree_Formalism_L2_Col_Br_d0___redArg(v_n_90_, v_lam_92_, v_sg_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_d0___boxed(lean_object* v_N_95_, lean_object* v_n_96_, lean_object* v_hN_97_, lean_object* v_lam_98_, lean_object* v_sg_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_tree_Formalism_L2_Col_Br_d0(v_N_95_, v_n_96_, v_hN_97_, v_lam_98_, v_sg_99_);
lean_dec(v_N_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_nBr___lam__0(lean_object* v_lam_101_, lean_object* v_i_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_apply_1(v_lam_101_, v_i_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_nBr___lam__1(lean_object* v_sg_104_, lean_object* v_i_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_apply_1(v_sg_104_, v_i_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_nBr(lean_object* v_N_107_, lean_object* v_n_108_, lean_object* v_lam_109_, lean_object* v_sg_110_){
_start:
{
lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___f_111_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Br_nBr___lam__0), 2, 1);
lean_closure_set(v___f_111_, 0, v_lam_109_);
v___f_112_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Br_nBr___lam__1), 2, 1);
lean_closure_set(v___f_112_, 0, v_sg_110_);
v___x_113_ = l_List_finRange(v_N_107_);
v___x_114_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_113_, v___f_111_);
v___x_115_ = l_List_finRange(v_n_108_);
v___x_116_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_115_, v___f_112_);
v___x_117_ = lean_int_sub(v___x_114_, v___x_116_);
lean_dec(v___x_116_);
lean_dec(v___x_114_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_upVar___redArg(lean_object* v_v_118_){
_start:
{
lean_object* v_snd_119_; lean_object* v_fst_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_136_; 
v_snd_119_ = lean_ctor_get(v_v_118_, 1);
v_fst_120_ = lean_ctor_get(v_v_118_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_v_118_);
if (v_isSharedCheck_136_ == 0)
{
v___x_122_ = v_v_118_;
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_119_);
lean_inc(v_fst_120_);
lean_dec(v_v_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_fst_124_ = lean_ctor_get(v_snd_119_, 0);
v_snd_125_ = lean_ctor_get(v_snd_119_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_snd_119_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v_snd_119_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snd_125_);
lean_inc(v_fst_124_);
lean_dec(v_snd_119_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_fst_124_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_snd_125_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_130_);
v___x_132_ = v___x_122_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_fst_120_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_upVar(lean_object* v_00_u03b9_137_, lean_object* v_N_138_, lean_object* v_n_139_, lean_object* v_hN_140_, lean_object* v_v_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lp_tree_Formalism_L2_Col_Br_upVar___redArg(v_v_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_upVar___boxed(lean_object* v_00_u03b9_143_, lean_object* v_N_144_, lean_object* v_n_145_, lean_object* v_hN_146_, lean_object* v_v_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_tree_Formalism_L2_Col_Br_upVar(v_00_u03b9_143_, v_N_144_, v_n_145_, v_hN_146_, v_v_147_);
lean_dec(v_n_145_);
lean_dec(v_N_144_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bExp___redArg(lean_object* v_lam_149_, lean_object* v_sg_150_, lean_object* v_00_u03c4_151_, lean_object* v_s_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_inc(v_00_u03c4_151_);
v___x_153_ = lean_apply_1(v_lam_149_, v_00_u03c4_151_);
v___x_154_ = lean_apply_1(v_sg_150_, v_00_u03c4_151_);
v___x_155_ = lp_tree_Formalism_L2_Col_Br_bBr___redArg(v___x_153_, v___x_154_, v_s_152_);
v___x_156_ = l_Int_toNat(v___x_155_);
lean_dec(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bExp(lean_object* v_00_u03b9_157_, lean_object* v_N_158_, lean_object* v_n_159_, lean_object* v_hN_160_, lean_object* v_lam_161_, lean_object* v_sg_162_, lean_object* v_00_u03c4_163_, lean_object* v_s_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lp_tree_Formalism_L2_Col_Br_bExp___redArg(v_lam_161_, v_sg_162_, v_00_u03c4_163_, v_s_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_bExp___boxed(lean_object* v_00_u03b9_166_, lean_object* v_N_167_, lean_object* v_n_168_, lean_object* v_hN_169_, lean_object* v_lam_170_, lean_object* v_sg_171_, lean_object* v_00_u03c4_172_, lean_object* v_s_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_tree_Formalism_L2_Col_Br_bExp(v_00_u03b9_166_, v_N_167_, v_n_168_, v_hN_169_, v_lam_170_, v_sg_171_, v_00_u03c4_172_, v_s_173_);
lean_dec(v_n_168_);
lean_dec(v_N_167_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extUH___redArg(lean_object* v_inst_175_, lean_object* v_n_176_){
_start:
{
lean_object* v___f_177_; 
v___f_177_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extU___redArg___lam__0), 3, 2);
lean_closure_set(v___f_177_, 0, v_inst_175_);
lean_closure_set(v___f_177_, 1, v_n_176_);
return v___f_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extUH(lean_object* v_E_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_N_182_, lean_object* v_n_183_, lean_object* v_hN_184_){
_start:
{
lean_object* v___f_185_; 
v___f_185_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_extU___redArg___lam__0), 3, 2);
lean_closure_set(v___f_185_, 0, v_inst_179_);
lean_closure_set(v___f_185_, 1, v_n_183_);
return v___f_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extUH___boxed(lean_object* v_E_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_N_190_, lean_object* v_n_191_, lean_object* v_hN_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = lp_tree_Formalism_L2_Col_extUH(v_E_186_, v_inst_187_, v_inst_188_, v_inst_189_, v_N_190_, v_n_191_, v_hN_192_);
lean_dec(v_N_190_);
lean_dec(v_inst_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extGH___redArg(lean_object* v_inst_194_, lean_object* v_n_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lp_tree_Formalism_L2_Col_extG___redArg(v_inst_194_, v_n_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extGH(lean_object* v_E_197_, lean_object* v_inst_198_, lean_object* v_N_199_, lean_object* v_n_200_, lean_object* v_hN_201_, lean_object* v_SG_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lp_tree_Formalism_L2_Col_extG___redArg(v_inst_198_, v_n_200_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_extGH___boxed(lean_object* v_E_204_, lean_object* v_inst_205_, lean_object* v_N_206_, lean_object* v_n_207_, lean_object* v_hN_208_, lean_object* v_SG_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = lp_tree_Formalism_L2_Col_extGH(v_E_204_, v_inst_205_, v_N_206_, v_n_207_, v_hN_208_, v_SG_209_);
lean_dec(v_SG_209_);
lean_dec(v_N_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res___redArg___lam__0(lean_object* v_be_211_, lean_object* v_w_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_apply_3(v_be_211_, v_w_212_, v___y_213_, v___y_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res___redArg(lean_object* v_d_216_){
_start:
{
lean_object* v_N_217_; lean_object* v_f_218_; lean_object* v_be_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_N_217_ = lean_ctor_get(v_d_216_, 0);
v_f_218_ = lean_ctor_get(v_d_216_, 1);
v_be_219_ = lean_ctor_get(v_d_216_, 2);
v_isSharedCheck_227_ = !lean_is_exclusive(v_d_216_);
if (v_isSharedCheck_227_ == 0)
{
v___x_221_ = v_d_216_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_be_219_);
lean_inc(v_f_218_);
lean_inc(v_N_217_);
lean_dec(v_d_216_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___f_223_; lean_object* v___x_225_; 
v___f_223_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Deco_res___redArg___lam__0), 4, 1);
lean_closure_set(v___f_223_, 0, v_be_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 2, v___f_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_N_217_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_f_218_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v___f_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res(lean_object* v_E_228_, lean_object* v_inst_229_, lean_object* v_n_230_, lean_object* v_ST_231_, lean_object* v_SG_232_, lean_object* v_SG_x27_233_, lean_object* v_h_234_, lean_object* v_d_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lp_tree_Formalism_L2_Col_Deco_res___redArg(v_d_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_res___boxed(lean_object* v_E_237_, lean_object* v_inst_238_, lean_object* v_n_239_, lean_object* v_ST_240_, lean_object* v_SG_241_, lean_object* v_SG_x27_242_, lean_object* v_h_243_, lean_object* v_d_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_tree_Formalism_L2_Col_Deco_res(v_E_237_, v_inst_238_, v_n_239_, v_ST_240_, v_SG_241_, v_SG_x27_242_, v_h_243_, v_d_244_);
lean_dec(v_SG_x27_242_);
lean_dec(v_SG_241_);
lean_dec(v_ST_240_);
lean_dec(v_n_239_);
lean_dec_ref(v_inst_238_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_res___redArg(lean_object* v_d_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lp_tree_Formalism_L2_Col_Deco_res___redArg(v_d_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_res(lean_object* v_E_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_n_252_, lean_object* v_ST_253_, lean_object* v_SG_254_, lean_object* v_SG_x27_255_, lean_object* v_h_256_, lean_object* v_d_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lp_tree_Formalism_L2_Col_Deco_res___redArg(v_d_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoSet_res___boxed(lean_object* v_E_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_n_263_, lean_object* v_ST_264_, lean_object* v_SG_265_, lean_object* v_SG_x27_266_, lean_object* v_h_267_, lean_object* v_d_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_tree_Formalism_L2_Col_DecoSet_res(v_E_259_, v_inst_260_, v_inst_261_, v_inst_262_, v_n_263_, v_ST_264_, v_SG_265_, v_SG_x27_266_, v_h_267_, v_d_268_);
lean_dec(v_SG_x27_266_);
lean_dec(v_SG_265_);
lean_dec(v_ST_264_);
lean_dec(v_n_263_);
lean_dec(v_inst_262_);
lean_dec_ref(v_inst_260_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts___redArg___lam__0(lean_object* v_actD_270_, lean_object* v_Y_271_, lean_object* v_g_272_, lean_object* v_p_273_){
_start:
{
lean_object* v_fst_274_; lean_object* v_snd_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_284_; 
v_fst_274_ = lean_ctor_get(v_p_273_, 0);
v_snd_275_ = lean_ctor_get(v_p_273_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_p_273_);
if (v_isSharedCheck_284_ == 0)
{
v___x_277_ = v_p_273_;
v_isShared_278_ = v_isSharedCheck_284_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_275_);
lean_inc(v_fst_274_);
lean_dec(v_p_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_284_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_inc(v_g_272_);
v___x_279_ = lean_apply_2(v_actD_270_, v_g_272_, v_fst_274_);
v___x_280_ = lean_apply_2(v_Y_271_, v_g_272_, v_snd_275_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_280_);
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts___redArg(lean_object* v_S_285_, lean_object* v_Y_286_){
_start:
{
lean_object* v_actD_287_; lean_object* v___f_288_; 
v_actD_287_ = lean_ctor_get(v_S_285_, 1);
lean_inc(v_actD_287_);
lean_dec_ref(v_S_285_);
v___f_288_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionGPts___redArg___lam__0), 4, 2);
lean_closure_set(v___f_288_, 0, v_actD_287_);
lean_closure_set(v___f_288_, 1, v_Y_286_);
return v___f_288_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts(lean_object* v_K_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_S_293_, lean_object* v_Y_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lp_tree_Formalism_L2_Col_instMulActionGPts___redArg(v_S_293_, v_Y_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionGPts___boxed(lean_object* v_K_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_S_300_, lean_object* v_Y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = lp_tree_Formalism_L2_Col_instMulActionGPts(v_K_296_, v_inst_297_, v_inst_298_, v_inst_299_, v_S_300_, v_Y_301_);
lean_dec(v_inst_299_);
lean_dec_ref(v_inst_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL(lean_object* v_E_303_, lean_object* v_inst_304_, lean_object* v_n_305_, lean_object* v_M_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL___boxed(lean_object* v_E_308_, lean_object* v_inst_309_, lean_object* v_n_310_, lean_object* v_M_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = lp_tree_Formalism_L2_Col_stabL(v_E_308_, v_inst_309_, v_n_310_, v_M_311_);
lean_dec(v_n_310_);
lean_dec_ref(v_inst_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt(lean_object* v_E_313_, lean_object* v_inst_314_, lean_object* v_n_315_, lean_object* v_P_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt___boxed(lean_object* v_E_318_, lean_object* v_inst_319_, lean_object* v_n_320_, lean_object* v_P_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = lp_tree_Formalism_L2_Col_stdAt(v_E_318_, v_inst_319_, v_n_320_, v_P_321_);
lean_dec(v_n_320_);
lean_dec_ref(v_inst_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint(lean_object* v_E_323_, lean_object* v_inst_324_, lean_object* v_n_325_, lean_object* v_P_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_box(0);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint___boxed(lean_object* v_E_328_, lean_object* v_inst_329_, lean_object* v_n_330_, lean_object* v_P_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = lp_tree_Formalism_L2_Col_GLint(v_E_328_, v_inst_329_, v_n_330_, v_P_331_);
lean_dec(v_n_330_);
lean_dec_ref(v_inst_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco___redArg(lean_object* v_p_333_){
_start:
{
lean_object* v_fst_334_; 
v_fst_334_ = lean_ctor_get(v_p_333_, 0);
lean_inc(v_fst_334_);
return v_fst_334_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco___redArg___boxed(lean_object* v_p_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = lp_tree_Formalism_L2_Col_DecoF_deco___redArg(v_p_335_);
lean_dec_ref(v_p_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco(lean_object* v_E_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_n_340_, lean_object* v_ST_341_, lean_object* v_SG_342_, lean_object* v_Q_343_, lean_object* v_p_344_){
_start:
{
lean_object* v_fst_345_; 
v_fst_345_ = lean_ctor_get(v_p_344_, 0);
lean_inc(v_fst_345_);
return v_fst_345_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_deco___boxed(lean_object* v_E_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_n_349_, lean_object* v_ST_350_, lean_object* v_SG_351_, lean_object* v_Q_352_, lean_object* v_p_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = lp_tree_Formalism_L2_Col_DecoF_deco(v_E_346_, v_inst_347_, v_inst_348_, v_n_349_, v_ST_350_, v_SG_351_, v_Q_352_, v_p_353_);
lean_dec_ref(v_p_353_);
lean_dec(v_Q_352_);
lean_dec(v_SG_351_);
lean_dec(v_ST_350_);
lean_dec(v_n_349_);
lean_dec(v_inst_348_);
lean_dec_ref(v_inst_347_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_fr___redArg(lean_object* v_p_355_, lean_object* v_P_356_){
_start:
{
lean_object* v_snd_357_; lean_object* v___x_358_; 
v_snd_357_ = lean_ctor_get(v_p_355_, 1);
lean_inc(v_snd_357_);
lean_dec_ref(v_p_355_);
v___x_358_ = lean_apply_1(v_snd_357_, v_P_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_fr(lean_object* v_E_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_n_362_, lean_object* v_ST_363_, lean_object* v_SG_364_, lean_object* v_Q_365_, lean_object* v_p_366_, lean_object* v_P_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lp_tree_Formalism_L2_Col_DecoF_fr___redArg(v_p_366_, v_P_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_DecoF_fr___boxed(lean_object* v_E_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_n_372_, lean_object* v_ST_373_, lean_object* v_SG_374_, lean_object* v_Q_375_, lean_object* v_p_376_, lean_object* v_P_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = lp_tree_Formalism_L2_Col_DecoF_fr(v_E_369_, v_inst_370_, v_inst_371_, v_n_372_, v_ST_373_, v_SG_374_, v_Q_375_, v_p_376_, v_P_377_);
lean_dec(v_Q_375_);
lean_dec(v_SG_374_);
lean_dec(v_ST_373_);
lean_dec(v_n_372_);
lean_dec(v_inst_371_);
lean_dec_ref(v_inst_370_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__0(lean_object* v_snd_379_, lean_object* v_fst_380_, lean_object* v_snd_381_, lean_object* v_P_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_383_ = lean_apply_1(v_snd_379_, v_P_382_);
v___x_384_ = lp_mathlib_LinearEquiv_trans___redArg(v___x_383_, v_fst_380_);
v___x_385_ = lean_apply_1(v_snd_381_, v_P_382_);
v___x_386_ = lp_mathlib_LinearEquiv_symm___redArg(v___x_385_);
v___x_387_ = lp_mathlib_LinearEquiv_trans___redArg(v___x_386_, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__1(lean_object* v_inst_388_, lean_object* v_n_389_, lean_object* v_a_390_, lean_object* v_p_391_){
_start:
{
lean_object* v_snd_392_; lean_object* v_fst_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_406_; 
v_snd_392_ = lean_ctor_get(v_a_390_, 1);
lean_inc(v_snd_392_);
v_fst_393_ = lean_ctor_get(v_a_390_, 0);
lean_inc(v_fst_393_);
lean_dec_ref(v_a_390_);
v_fst_394_ = lean_ctor_get(v_snd_392_, 0);
lean_inc(v_fst_394_);
v_snd_395_ = lean_ctor_get(v_snd_392_, 1);
lean_inc(v_snd_395_);
lean_dec(v_snd_392_);
v_fst_396_ = lean_ctor_get(v_p_391_, 0);
v_snd_397_ = lean_ctor_get(v_p_391_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_p_391_);
if (v_isSharedCheck_406_ == 0)
{
v___x_399_ = v_p_391_;
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_p_391_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
lean_inc(v_fst_393_);
v___f_401_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__0), 4, 3);
lean_closure_set(v___f_401_, 0, v_snd_397_);
lean_closure_set(v___f_401_, 1, v_fst_393_);
lean_closure_set(v___f_401_, 2, v_snd_395_);
v___x_402_ = lp_tree_Formalism_L2_Col_Deco_act___redArg(v_inst_388_, v_n_389_, v_fst_393_, v_fst_394_, v_fst_396_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___f_401_);
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___f_401_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg(lean_object* v_inst_407_, lean_object* v_n_408_){
_start:
{
lean_object* v___f_409_; 
v___f_409_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__1), 4, 2);
lean_closure_set(v___f_409_, 0, v_inst_407_);
lean_closure_set(v___f_409_, 1, v_n_408_);
return v___f_409_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF(lean_object* v_E_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_n_414_, lean_object* v_ST_415_, lean_object* v_SG_416_, lean_object* v_Q_417_){
_start:
{
lean_object* v___f_418_; 
v___f_418_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__1), 4, 2);
lean_closure_set(v___f_418_, 0, v_inst_411_);
lean_closure_set(v___f_418_, 1, v_n_414_);
return v___f_418_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___boxed(lean_object* v_E_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_n_423_, lean_object* v_ST_424_, lean_object* v_SG_425_, lean_object* v_Q_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF(v_E_419_, v_inst_420_, v_inst_421_, v_inst_422_, v_n_423_, v_ST_424_, v_SG_425_, v_Q_426_);
lean_dec(v_Q_426_);
lean_dec(v_SG_425_);
lean_dec(v_ST_424_);
lean_dec(v_inst_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp(lean_object* v_E_428_, lean_object* v_K_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_n_434_, lean_object* v_Q_435_, lean_object* v_00_u0398_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_box(0);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp___boxed(lean_object* v_E_438_, lean_object* v_K_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_n_444_, lean_object* v_Q_445_, lean_object* v_00_u0398_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = lp_tree_Formalism_L2_Col_LevQFam_grp(v_E_438_, v_K_439_, v_inst_440_, v_inst_441_, v_inst_442_, v_inst_443_, v_n_444_, v_Q_445_, v_00_u0398_446_);
lean_dec_ref(v_00_u0398_446_);
lean_dec(v_Q_445_);
lean_dec(v_n_444_);
lean_dec_ref(v_inst_443_);
lean_dec(v_inst_442_);
lean_dec_ref(v_inst_440_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___redArg___lam__0(lean_object* v_00_u0398_448_, lean_object* v_P_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_451_; lean_object* v_lam_452_; lean_object* v___x_453_; 
v___x_451_ = lean_apply_1(v_00_u0398_448_, v_P_449_);
v_lam_452_ = lean_ctor_get(v___x_451_, 1);
lean_inc_ref(v_lam_452_);
lean_dec_ref(v___x_451_);
v___x_453_ = lean_apply_1(v_lam_452_, v___y_450_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___redArg(lean_object* v_inst_454_, lean_object* v_Q_455_, lean_object* v_00_u0398_456_){
_start:
{
lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___f_457_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_LevQFam_chr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_457_, 0, v_00_u0398_456_);
v___x_458_ = lp_mathlib_Multiset_attach___redArg(v_Q_455_);
v___x_459_ = lp_tree_Formalism_L2_Col_piChar___redArg(v_inst_454_, v___x_458_, v___f_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___redArg___boxed(lean_object* v_inst_460_, lean_object* v_Q_461_, lean_object* v_00_u0398_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = lp_tree_Formalism_L2_Col_LevQFam_chr___redArg(v_inst_460_, v_Q_461_, v_00_u0398_462_);
lean_dec_ref(v_inst_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr(lean_object* v_E_464_, lean_object* v_K_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_n_470_, lean_object* v_Q_471_, lean_object* v_00_u0398_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lp_tree_Formalism_L2_Col_LevQFam_chr___redArg(v_inst_469_, v_Q_471_, v_00_u0398_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_chr___boxed(lean_object* v_E_474_, lean_object* v_K_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_n_480_, lean_object* v_Q_481_, lean_object* v_00_u0398_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = lp_tree_Formalism_L2_Col_LevQFam_chr(v_E_474_, v_K_475_, v_inst_476_, v_inst_477_, v_inst_478_, v_inst_479_, v_n_480_, v_Q_481_, v_00_u0398_482_);
lean_dec(v_n_480_);
lean_dec_ref(v_inst_479_);
lean_dec(v_inst_478_);
lean_dec_ref(v_inst_476_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg___lam__0(lean_object* v_toMonoid_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; lean_object* v_toOne_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v___x_486_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_484_);
v_toOne_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_486_, 1);
lean_dec(v_unused_495_);
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_toOne_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
lean_inc(v_toOne_487_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_toOne_487_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_toOne_487_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_toOne_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg___lam__0___boxed(lean_object* v_toMonoid_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = lp_tree_Formalism_L2_Col_LevQFam_top___redArg___lam__0(v_toMonoid_496_, v_x_497_);
lean_dec_ref(v_x_497_);
lean_dec_ref(v_toMonoid_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg(lean_object* v_inst_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_toSemiring_502_; lean_object* v_toMonoid_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_500_ = lp_mathlib_Field_toSemifield___redArg(v_inst_499_);
v___x_501_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_500_);
v_toSemiring_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc_ref(v_toSemiring_502_);
lean_dec_ref(v___x_501_);
v_toMonoid_503_ = lean_ctor_get(v_toSemiring_502_, 1);
lean_inc_ref(v_toMonoid_503_);
lean_dec_ref(v_toSemiring_502_);
v___f_504_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_LevQFam_top___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_504_, 0, v_toMonoid_503_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___f_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___redArg___boxed(lean_object* v_inst_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = lp_tree_Formalism_L2_Col_LevQFam_top___redArg(v_inst_507_);
lean_dec_ref(v_inst_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top(lean_object* v_E_509_, lean_object* v_K_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_n_515_, lean_object* v_Q_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lp_tree_Formalism_L2_Col_LevQFam_top___redArg(v_inst_514_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_top___boxed(lean_object* v_E_519_, lean_object* v_K_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_n_525_, lean_object* v_Q_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = lp_tree_Formalism_L2_Col_LevQFam_top(v_E_519_, v_K_520_, v_inst_521_, v_inst_522_, v_inst_523_, v_inst_524_, v_n_525_, v_Q_526_, v_x_527_);
lean_dec(v_Q_526_);
lean_dec(v_n_525_);
lean_dec_ref(v_inst_524_);
lean_dec(v_inst_523_);
lean_dec_ref(v_inst_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___lam__0(lean_object* v_self_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_apply_1(v_self_529_, v___y_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2(lean_object* v_X_533_, lean_object* v_n_534_, lean_object* v_H_535_){
_start:
{
lean_object* v___f_536_; 
v___f_536_ = ((lean_object*)(lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___closed__0));
return v___f_536_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___boxed(lean_object* v_X_537_, lean_object* v_n_538_, lean_object* v_H_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2(v_X_537_, v_n_538_, v_H_539_);
lean_dec(v_n_538_);
lean_dec_ref(v_X_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___lam__0(lean_object* v_self_541_){
_start:
{
lean_object* v_fst_542_; 
v_fst_542_ = lean_ctor_get(v_self_541_, 0);
lean_inc(v_fst_542_);
return v_fst_542_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___lam__0___boxed(lean_object* v_self_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___lam__0(v_self_543_);
lean_dec_ref(v_self_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9(lean_object* v_X_546_, lean_object* v___x_547_, lean_object* v_n_548_, lean_object* v___x_549_, lean_object* v___x_550_){
_start:
{
lean_object* v___f_551_; 
v___f_551_ = ((lean_object*)(lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___closed__0));
return v___f_551_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___boxed(lean_object* v_X_552_, lean_object* v___x_553_, lean_object* v_n_554_, lean_object* v___x_555_, lean_object* v___x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9(v_X_552_, v___x_553_, v_n_554_, v___x_555_, v___x_556_);
lean_dec(v_n_554_);
lean_dec_ref(v_X_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg___lam__1(lean_object* v_g_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_apply_1(v_g_558_, v___y_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg___lam__0(lean_object* v_f_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_1(v_f_561_, v___y_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg(lean_object* v_f_564_, lean_object* v_g_565_){
_start:
{
lean_object* v___f_566_; lean_object* v___f_567_; lean_object* v___x_568_; 
v___f_566_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg___lam__0), 2, 1);
lean_closure_set(v___f_566_, 0, v_f_564_);
v___f_567_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg___lam__1), 2, 1);
lean_closure_set(v___f_567_, 0, v_g_565_);
v___x_568_ = lean_alloc_closure((void*)(lp_mathlib_Function_prod), 6, 5);
lean_closure_set(v___x_568_, 0, lean_box(0));
lean_closure_set(v___x_568_, 1, lean_box(0));
lean_closure_set(v___x_568_, 2, lean_box(0));
lean_closure_set(v___x_568_, 3, v___f_566_);
lean_closure_set(v___x_568_, 4, v___f_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___lam__0(lean_object* v_self_569_){
_start:
{
lean_object* v_snd_570_; 
v_snd_570_ = lean_ctor_get(v_self_569_, 1);
lean_inc(v_snd_570_);
return v_snd_570_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___lam__0___boxed(lean_object* v_self_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___lam__0(v_self_571_);
lean_dec_ref(v_self_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10(lean_object* v_X_574_, lean_object* v___x_575_, lean_object* v_n_576_, lean_object* v___x_577_, lean_object* v___x_578_){
_start:
{
lean_object* v___f_579_; 
v___f_579_ = ((lean_object*)(lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___closed__0));
return v___f_579_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___boxed(lean_object* v_X_580_, lean_object* v___x_581_, lean_object* v_n_582_, lean_object* v___x_583_, lean_object* v___x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10(v_X_580_, v___x_581_, v_n_582_, v___x_583_, v___x_584_);
lean_dec(v_n_582_);
lean_dec_ref(v_X_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4(lean_object* v_X_586_, lean_object* v___x_587_, lean_object* v_n_588_, lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v_f_591_, lean_object* v_g_592_){
_start:
{
lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; 
v___f_593_ = ((lean_object*)(lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__9___closed__0));
v___f_594_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_594_, 0, v___f_593_);
lean_closure_set(v___f_594_, 1, v_f_591_);
v___f_595_ = ((lean_object*)(lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__10___closed__0));
v___f_596_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_596_, 0, v___f_595_);
lean_closure_set(v___f_596_, 1, v_g_592_);
v___x_597_ = lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg(v___f_594_, v___f_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4___boxed(lean_object* v_X_598_, lean_object* v___x_599_, lean_object* v_n_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_f_603_, lean_object* v_g_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4(v_X_598_, v___x_599_, v_n_600_, v___x_601_, v___x_602_, v_f_603_, v_g_604_);
lean_dec(v_n_600_);
lean_dec_ref(v_X_598_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp___at___00Formalism_L2_Col_FrmG_incl_spec__1(lean_object* v_X_606_, lean_object* v_inst_607_, lean_object* v_n_608_, lean_object* v_Q_609_, lean_object* v_00_u0398_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_box(0);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LevQFam_grp___at___00Formalism_L2_Col_FrmG_incl_spec__1___boxed(lean_object* v_X_612_, lean_object* v_inst_613_, lean_object* v_n_614_, lean_object* v_Q_615_, lean_object* v_00_u0398_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = lp_tree_Formalism_L2_Col_LevQFam_grp___at___00Formalism_L2_Col_FrmG_incl_spec__1(v_X_612_, v_inst_613_, v_n_614_, v_Q_615_, v_00_u0398_616_);
lean_dec_ref(v_00_u0398_616_);
lean_dec(v_Q_615_);
lean_dec(v_n_614_);
lean_dec_ref(v_X_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg___lam__0(lean_object* v_f_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_apply_2(v_f_618_, v___y_619_, v___y_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg___lam__1(lean_object* v_g_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_apply_2(v_g_622_, v___y_623_, v___y_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg(lean_object* v_f_626_, lean_object* v_g_627_){
_start:
{
lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___x_630_; 
v___f_628_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg___lam__0), 3, 1);
lean_closure_set(v___f_628_, 0, v_f_626_);
v___f_629_ = lean_alloc_closure((void*)(lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg___lam__1), 3, 1);
lean_closure_set(v___f_629_, 0, v_g_627_);
v___x_630_ = lean_alloc_closure((void*)(lp_mathlib_Function_prod), 6, 5);
lean_closure_set(v___x_630_, 0, lean_box(0));
lean_closure_set(v___x_630_, 1, lean_box(0));
lean_closure_set(v___x_630_, 2, lean_box(0));
lean_closure_set(v___x_630_, 3, v___f_628_);
lean_closure_set(v___x_630_, 4, v___f_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___lam__0(lean_object* v_self_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_fst_633_; lean_object* v___x_634_; 
v_fst_633_ = lean_ctor_get(v_self_631_, 0);
lean_inc(v_fst_633_);
lean_dec_ref(v_self_631_);
v___x_634_ = lean_apply_1(v_fst_633_, v___y_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5(lean_object* v_X_636_, lean_object* v_n_637_, lean_object* v___x_638_, lean_object* v___x_639_){
_start:
{
lean_object* v___f_640_; 
v___f_640_ = ((lean_object*)(lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___closed__0));
return v___f_640_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___boxed(lean_object* v_X_641_, lean_object* v_n_642_, lean_object* v___x_643_, lean_object* v___x_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5(v_X_641_, v_n_642_, v___x_643_, v___x_644_);
lean_dec(v_n_642_);
lean_dec_ref(v_X_641_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___lam__0(lean_object* v_self_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_snd_648_; lean_object* v___x_649_; 
v_snd_648_ = lean_ctor_get(v_self_646_, 1);
lean_inc(v_snd_648_);
lean_dec_ref(v_self_646_);
v___x_649_ = lean_apply_1(v_snd_648_, v___y_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6(lean_object* v_X_651_, lean_object* v_n_652_, lean_object* v___x_653_, lean_object* v___x_654_){
_start:
{
lean_object* v___f_655_; 
v___f_655_ = ((lean_object*)(lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___closed__0));
return v___f_655_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___boxed(lean_object* v_X_656_, lean_object* v_n_657_, lean_object* v___x_658_, lean_object* v___x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6(v_X_656_, v_n_657_, v___x_658_, v___x_659_);
lean_dec(v_n_657_);
lean_dec_ref(v_X_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3(lean_object* v_X_661_, lean_object* v_n_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v_f_665_, lean_object* v_g_666_){
_start:
{
lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___x_671_; 
v___f_667_ = ((lean_object*)(lp_tree_MonoidHom_fst___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__5___closed__0));
v___f_668_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_668_, 0, v___f_667_);
lean_closure_set(v___f_668_, 1, v_f_665_);
v___f_669_ = ((lean_object*)(lp_tree_MonoidHom_snd___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__6___closed__0));
v___f_670_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_670_, 0, v___f_669_);
lean_closure_set(v___f_670_, 1, v_g_666_);
v___x_671_ = lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg(v___f_668_, v___f_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3___boxed(lean_object* v_X_672_, lean_object* v_n_673_, lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v_f_676_, lean_object* v_g_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3(v_X_672_, v_n_673_, v___x_674_, v___x_675_, v_f_676_, v_g_677_);
lean_dec(v_n_673_);
lean_dec_ref(v_X_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___redArg(lean_object* v_X_681_, lean_object* v_n_682_, lean_object* v_Q_683_, lean_object* v_00_u0398_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___f_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_685_ = lean_box(0);
v___f_686_ = ((lean_object*)(lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__0));
v___f_687_ = ((lean_object*)(lp_tree_Formalism_L2_Col_FrmG_incl___redArg___closed__1));
v___f_688_ = ((lean_object*)(lp_tree_Subgroup_subtype___at___00Formalism_L2_Col_FrmG_incl_spec__2___closed__0));
v___x_689_ = lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3(v_X_681_, v_n_682_, v___x_685_, v___x_685_, v___f_687_, v___f_688_);
v___x_690_ = lp_tree_MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4(v_X_681_, v___x_685_, v_n_682_, v___x_685_, v___x_685_, v___f_686_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___redArg___boxed(lean_object* v_X_691_, lean_object* v_n_692_, lean_object* v_Q_693_, lean_object* v_00_u0398_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = lp_tree_Formalism_L2_Col_FrmG_incl___redArg(v_X_691_, v_n_692_, v_Q_693_, v_00_u0398_694_);
lean_dec_ref(v_00_u0398_694_);
lean_dec(v_Q_693_);
lean_dec(v_n_692_);
lean_dec_ref(v_X_691_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl(lean_object* v_X_696_, lean_object* v_n_697_, lean_object* v_SG_698_, lean_object* v_Q_699_, lean_object* v_00_u039b_700_, lean_object* v_00_u0398_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lp_tree_Formalism_L2_Col_FrmG_incl___redArg(v_X_696_, v_n_697_, v_Q_699_, v_00_u0398_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_FrmG_incl___boxed(lean_object* v_X_703_, lean_object* v_n_704_, lean_object* v_SG_705_, lean_object* v_Q_706_, lean_object* v_00_u039b_707_, lean_object* v_00_u0398_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = lp_tree_Formalism_L2_Col_FrmG_incl(v_X_703_, v_n_704_, v_SG_705_, v_Q_706_, v_00_u039b_707_, v_00_u0398_708_);
lean_dec_ref(v_00_u0398_708_);
lean_dec_ref(v_00_u039b_707_);
lean_dec(v_Q_706_);
lean_dec(v_SG_705_);
lean_dec(v_n_704_);
lean_dec_ref(v_X_703_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__1(lean_object* v_X_710_, lean_object* v_n_711_, lean_object* v_M_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stabL___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__1___boxed(lean_object* v_X_714_, lean_object* v_n_715_, lean_object* v_M_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = lp_tree_Formalism_L2_Col_stabL___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__1(v_X_714_, v_n_715_, v_M_716_);
lean_dec(v_n_715_);
lean_dec_ref(v_X_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* lp_tree_Ideal_primeCompl___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__17(lean_object* v_X_718_, lean_object* v_P_719_, lean_object* v_hp_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(0);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* lp_tree_Ideal_primeCompl___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_X_722_, lean_object* v_P_723_, lean_object* v_hp_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = lp_tree_Ideal_primeCompl___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__17(v_X_722_, v_P_723_, v_hp_724_);
lean_dec_ref(v_X_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_locS___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__18(lean_object* v_X_726_, lean_object* v_S_727_, lean_object* v_L_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_box(0);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_locS___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__18___boxed(lean_object* v_X_730_, lean_object* v_S_731_, lean_object* v_L_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = lp_tree_Formalism_HermitianLatticesTheory_locS___at___00Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3_spec__18(v_X_730_, v_S_731_, v_L_732_);
lean_dec_ref(v_X_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___redArg(lean_object* v_X_734_, lean_object* v_p_735_, lean_object* v_L_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lean_box(0);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_X_738_, lean_object* v_p_739_, lean_object* v_L_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___redArg(v_X_738_, v_p_739_, v_L_740_);
lean_dec_ref(v_X_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__16(lean_object* v_X_742_, lean_object* v_00_u03c3_u2081_u2082_743_, lean_object* v_inst_744_, lean_object* v_f_745_, lean_object* v_p_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__16___boxed(lean_object* v_X_748_, lean_object* v_00_u03c3_u2081_u2082_749_, lean_object* v_inst_750_, lean_object* v_f_751_, lean_object* v_p_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__16(v_X_748_, v_00_u03c3_u2081_u2082_749_, v_inst_750_, v_f_751_, v_p_752_);
lean_dec(v_f_751_);
lean_dec(v_00_u03c3_u2081_u2082_749_);
lean_dec_ref(v_X_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__17(lean_object* v_X_754_, lean_object* v_p_755_, lean_object* v_s_756_, lean_object* v_hs_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_box(0);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__17___boxed(lean_object* v_X_759_, lean_object* v_p_760_, lean_object* v_s_761_, lean_object* v_hs_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14_spec__17(v_X_759_, v_p_760_, v_s_761_, v_hs_762_);
lean_dec_ref(v_X_759_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___redArg(lean_object* v_X_764_, lean_object* v_00_u03c4_u2081_u2082_765_, lean_object* v_f_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_box(0);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___redArg___boxed(lean_object* v_X_768_, lean_object* v_00_u03c4_u2081_u2082_769_, lean_object* v_f_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___redArg(v_X_768_, v_00_u03c4_u2081_u2082_769_, v_f_770_);
lean_dec(v_f_770_);
lean_dec(v_00_u03c4_u2081_u2082_769_);
lean_dec_ref(v_X_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg___lam__0(lean_object* v___x_772_, lean_object* v_f_773_, lean_object* v_x_774_, lean_object* v_b_775_){
_start:
{
lean_object* v_toCommSemiring_776_; lean_object* v___x_777_; lean_object* v_toMul_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_toCommSemiring_776_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_toCommSemiring_776_);
lean_dec_ref(v___x_772_);
v___x_777_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_776_);
v_toMul_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_toMul_778_);
lean_dec_ref(v___x_777_);
v___x_779_ = lean_apply_1(v_f_773_, v_b_775_);
v___x_780_ = lean_apply_2(v_toMul_778_, v___x_779_, v_x_774_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg(lean_object* v_X_781_, lean_object* v_f_782_, lean_object* v_x_783_){
_start:
{
lean_object* v_fieldE_784_; lean_object* v___x_785_; lean_object* v___f_786_; 
v_fieldE_784_ = lean_ctor_get(v_X_781_, 1);
v___x_785_ = lp_mathlib_Field_toSemifield___redArg(v_fieldE_784_);
v___f_786_ = lean_alloc_closure((void*)(lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg___lam__0), 4, 3);
lean_closure_set(v___f_786_, 0, v___x_785_);
lean_closure_set(v___f_786_, 1, v_f_782_);
lean_closure_set(v___f_786_, 2, v_x_783_);
return v___f_786_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg___boxed(lean_object* v_X_787_, lean_object* v_f_788_, lean_object* v_x_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg(v_X_787_, v_f_788_, v_x_789_);
lean_dec_ref(v_X_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13(lean_object* v_X_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___f_794_; lean_object* v___x_795_; 
v___f_794_ = ((lean_object*)(lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13___closed__0));
v___x_795_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg(v_X_792_, v___f_794_, v_x_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13___boxed(lean_object* v_X_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = lp_tree_LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13(v_X_796_, v_x_797_);
lean_dec_ref(v_X_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_toSemiring_799_, lean_object* v_X_800_, lean_object* v_x_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_box(0);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_toSemiring_803_, lean_object* v_X_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___lam__0(v_toSemiring_803_, v_X_804_, v_x_805_);
lean_dec(v_x_805_);
lean_dec_ref(v_X_804_);
lean_dec_ref(v_toSemiring_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__15(lean_object* v_X_807_, lean_object* v_I_808_, lean_object* v_p_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = lean_box(0);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_X_811_, lean_object* v_I_812_, lean_object* v_p_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = lp_tree_Submodule_pi___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__15(v_X_811_, v_I_812_, v_p_813_);
lean_dec_ref(v_p_813_);
lean_dec_ref(v_X_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg(lean_object* v_X_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lean_box(0);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_X_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___redArg(v_X_817_);
lean_dec_ref(v_X_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0(lean_object* v_X_819_, lean_object* v_n_820_, lean_object* v_P_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_box(0);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0___boxed(lean_object* v_X_823_, lean_object* v_n_824_, lean_object* v_P_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = lp_tree_Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0(v_X_823_, v_n_824_, v_P_825_);
lean_dec(v_n_824_);
lean_dec_ref(v_X_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0(lean_object* v_X_827_, lean_object* v_n_828_, lean_object* v_P_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0___boxed(lean_object* v_X_831_, lean_object* v_n_832_, lean_object* v_P_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = lp_tree_Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0(v_X_831_, v_n_832_, v_P_833_);
lean_dec(v_n_832_);
lean_dec_ref(v_X_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7(lean_object* v_X_835_, lean_object* v_n_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v_f_839_, lean_object* v_g_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___redArg(v_f_839_, v_g_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7___boxed(lean_object* v_X_842_, lean_object* v_n_843_, lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v_f_846_, lean_object* v_g_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__3_spec__7(v_X_842_, v_n_843_, v___x_844_, v___x_845_, v_f_846_, v_g_847_);
lean_dec(v_n_843_);
lean_dec_ref(v_X_842_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11(lean_object* v_X_849_, lean_object* v___x_850_, lean_object* v_n_851_, lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v_f_854_, lean_object* v_g_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___redArg(v_f_854_, v_g_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11___boxed(lean_object* v_X_857_, lean_object* v___x_858_, lean_object* v_n_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v_f_862_, lean_object* v_g_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = lp_tree_MonoidHom_prod___at___00MonoidHom_prodMap___at___00Formalism_L2_Col_FrmG_incl_spec__4_spec__11(v_X_857_, v___x_858_, v_n_859_, v___x_860_, v___x_861_, v_f_862_, v_g_863_);
lean_dec(v_n_859_);
lean_dec_ref(v_X_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2(lean_object* v_X_865_, lean_object* v_n_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_box(0);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2___boxed(lean_object* v_X_868_, lean_object* v_n_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = lp_tree_Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2(v_X_868_, v_n_869_);
lean_dec(v_n_869_);
lean_dec_ref(v_X_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3(lean_object* v_X_871_, lean_object* v_p_872_, lean_object* v_inst_873_, lean_object* v_L_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = lean_box(0);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3___boxed(lean_object* v_X_876_, lean_object* v_p_877_, lean_object* v_inst_878_, lean_object* v_L_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = lp_tree_Formalism_HermitianLatticesTheory_localization_u2082___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__3(v_X_876_, v_p_877_, v_inst_878_, v_L_879_);
lean_dec_ref(v_X_876_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14(lean_object* v_X_881_, lean_object* v_inst_882_, lean_object* v_f_883_, lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___redArg(v_X_881_, v_f_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14___boxed(lean_object* v_X_886_, lean_object* v_inst_887_, lean_object* v_f_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__13_spec__14(v_X_886_, v_inst_887_, v_f_888_, v_x_889_);
lean_dec_ref(v_X_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14(lean_object* v_X_891_, lean_object* v_00_u03c4_u2081_u2082_892_, lean_object* v_inst_893_, lean_object* v_f_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_box(0);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14___boxed(lean_object* v_X_896_, lean_object* v_00_u03c4_u2081_u2082_897_, lean_object* v_inst_898_, lean_object* v_f_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = lp_tree_LinearMap_range___at___00Formalism_L2_Col_stdLat___at___00Formalism_L2_Col_stdAt___at___00Formalism_L2_Col_GLint___at___00Formalism_L2_Col_FrmG_incl_spec__0_spec__0_spec__2_spec__14(v_X_896_, v_00_u03c4_u2081_u2082_897_, v_inst_898_, v_f_899_);
lean_dec(v_f_899_);
lean_dec(v_00_u03c4_u2081_u2082_897_);
lean_dec_ref(v_X_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___redArg___lam__0(lean_object* v_X_901_, lean_object* v_n_902_, lean_object* v_Q_903_, lean_object* v_00_u0398_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_112__overap_906_; lean_object* v___x_907_; 
v___x_112__overap_906_ = lp_tree_Formalism_L2_Col_FrmG_incl___redArg(v_X_901_, v_n_902_, v_Q_903_, v_00_u0398_904_);
v___x_907_ = lean_apply_1(v___x_112__overap_906_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___redArg___lam__0___boxed(lean_object* v_X_908_, lean_object* v_n_909_, lean_object* v_Q_910_, lean_object* v_00_u0398_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = lp_tree_Formalism_L2_Col_frmAct___redArg___lam__0(v_X_908_, v_n_909_, v_Q_910_, v_00_u0398_911_, v___y_912_);
lean_dec_ref(v_00_u0398_911_);
lean_dec(v_Q_910_);
lean_dec(v_n_909_);
lean_dec_ref(v_X_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___redArg(lean_object* v_X_914_, lean_object* v_n_915_, lean_object* v_Q_916_, lean_object* v_00_u0398_917_){
_start:
{
lean_object* v_fieldE_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___x_921_; 
v_fieldE_918_ = lean_ctor_get(v_X_914_, 1);
lean_inc_ref(v_fieldE_918_);
lean_inc(v_n_915_);
v___f_919_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_frmAct___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_919_, 0, v_X_914_);
lean_closure_set(v___f_919_, 1, v_n_915_);
lean_closure_set(v___f_919_, 2, v_Q_916_);
lean_closure_set(v___f_919_, 3, v_00_u0398_917_);
v___f_920_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_instMulActionProdSubtypeLinearEquivIdSpMemSubgroupUFGLGGLQDecoF___redArg___lam__1), 4, 2);
lean_closure_set(v___f_920_, 0, v_fieldE_918_);
lean_closure_set(v___f_920_, 1, v_n_915_);
v___x_921_ = lean_alloc_closure((void*)(lp_mathlib_SMul_comp_smul), 7, 5);
lean_closure_set(v___x_921_, 0, lean_box(0));
lean_closure_set(v___x_921_, 1, lean_box(0));
lean_closure_set(v___x_921_, 2, lean_box(0));
lean_closure_set(v___x_921_, 3, v___f_920_);
lean_closure_set(v___x_921_, 4, v___f_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct(lean_object* v_X_922_, lean_object* v_n_923_, lean_object* v_ST_924_, lean_object* v_SG_925_, lean_object* v_Q_926_, lean_object* v_00_u039b_927_, lean_object* v_00_u0398_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lp_tree_Formalism_L2_Col_frmAct___redArg(v_X_922_, v_n_923_, v_Q_926_, v_00_u0398_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_frmAct___boxed(lean_object* v_X_930_, lean_object* v_n_931_, lean_object* v_ST_932_, lean_object* v_SG_933_, lean_object* v_Q_934_, lean_object* v_00_u039b_935_, lean_object* v_00_u0398_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = lp_tree_Formalism_L2_Col_frmAct(v_X_930_, v_n_931_, v_ST_932_, v_SG_933_, v_Q_934_, v_00_u039b_935_, v_00_u0398_936_);
lean_dec_ref(v_00_u039b_935_);
lean_dec(v_SG_933_);
lean_dec(v_ST_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN___redArg(lean_object* v_inst_938_, lean_object* v_N_939_, lean_object* v_v_940_, lean_object* v_i_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_nat_dec_lt(v_i_941_, v_N_939_);
if (v___x_942_ == 0)
{
lean_object* v_toSemiring_943_; lean_object* v___x_944_; lean_object* v_toZero_945_; 
lean_dec(v_i_941_);
lean_dec(v_v_940_);
v_toSemiring_943_ = lean_ctor_get(v_inst_938_, 0);
lean_inc_ref(v_toSemiring_943_);
lean_dec_ref(v_inst_938_);
v___x_944_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_943_);
v_toZero_945_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_toZero_945_);
lean_dec_ref(v___x_944_);
return v_toZero_945_;
}
else
{
lean_object* v___x_946_; 
lean_dec_ref(v_inst_938_);
v___x_946_ = lean_apply_1(v_v_940_, v_i_941_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN___redArg___boxed(lean_object* v_inst_947_, lean_object* v_N_948_, lean_object* v_v_949_, lean_object* v_i_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = lp_tree_Formalism_L2_Col_Loc_atN___redArg(v_inst_947_, v_N_948_, v_v_949_, v_i_950_);
lean_dec(v_N_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN(lean_object* v_k_952_, lean_object* v_inst_953_, lean_object* v_N_954_, lean_object* v_v_955_, lean_object* v_i_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lp_tree_Formalism_L2_Col_Loc_atN___redArg(v_inst_953_, v_N_954_, v_v_955_, v_i_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_atN___boxed(lean_object* v_k_958_, lean_object* v_inst_959_, lean_object* v_N_960_, lean_object* v_v_961_, lean_object* v_i_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = lp_tree_Formalism_L2_Col_Loc_atN(v_k_958_, v_inst_959_, v_N_960_, v_v_961_, v_i_962_);
lean_dec(v_N_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN___redArg(lean_object* v_inst_964_, lean_object* v_i_965_, lean_object* v_l_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_eq(v_l_966_, v_i_965_);
if (v___x_967_ == 0)
{
lean_object* v_toSemiring_968_; lean_object* v___x_969_; lean_object* v_toZero_970_; 
v_toSemiring_968_ = lean_ctor_get(v_inst_964_, 0);
lean_inc_ref(v_toSemiring_968_);
lean_dec_ref(v_inst_964_);
v___x_969_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_968_);
v_toZero_970_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_toZero_970_);
lean_dec_ref(v___x_969_);
return v_toZero_970_;
}
else
{
lean_object* v___x_971_; lean_object* v_toAddMonoidWithOne_972_; lean_object* v_toOne_973_; 
v___x_971_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_964_);
v_toAddMonoidWithOne_972_ = lean_ctor_get(v___x_971_, 1);
lean_inc_ref(v_toAddMonoidWithOne_972_);
lean_dec_ref(v___x_971_);
v_toOne_973_ = lean_ctor_get(v_toAddMonoidWithOne_972_, 2);
lean_inc(v_toOne_973_);
lean_dec_ref(v_toAddMonoidWithOne_972_);
return v_toOne_973_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN___redArg___boxed(lean_object* v_inst_974_, lean_object* v_i_975_, lean_object* v_l_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = lp_tree_Formalism_L2_Col_Loc_eN___redArg(v_inst_974_, v_i_975_, v_l_976_);
lean_dec(v_l_976_);
lean_dec(v_i_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN(lean_object* v_k_978_, lean_object* v_inst_979_, lean_object* v_N_980_, lean_object* v_i_981_, lean_object* v_l_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lp_tree_Formalism_L2_Col_Loc_eN___redArg(v_inst_979_, v_i_981_, v_l_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_eN___boxed(lean_object* v_k_984_, lean_object* v_inst_985_, lean_object* v_N_986_, lean_object* v_i_987_, lean_object* v_l_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = lp_tree_Formalism_L2_Col_Loc_eN(v_k_984_, v_inst_985_, v_N_986_, v_i_987_, v_l_988_);
lean_dec(v_l_988_);
lean_dec(v_i_987_);
lean_dec(v_N_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_supp(lean_object* v_k_990_, lean_object* v_inst_991_, lean_object* v_N_992_, lean_object* v_s_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_box(0);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_supp___boxed(lean_object* v_k_995_, lean_object* v_inst_996_, lean_object* v_N_997_, lean_object* v_s_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = lp_tree_Formalism_L2_Col_Loc_supp(v_k_995_, v_inst_996_, v_N_997_, v_s_998_);
lean_dec(v_N_997_);
lean_dec_ref(v_inst_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Ufl(lean_object* v_k_1000_, lean_object* v_inst_1001_, lean_object* v_n_1002_, lean_object* v_c_1003_, lean_object* v_i_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_box(0);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Ufl___boxed(lean_object* v_k_1006_, lean_object* v_inst_1007_, lean_object* v_n_1008_, lean_object* v_c_1009_, lean_object* v_i_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = lp_tree_Formalism_L2_Col_Loc_Ufl(v_k_1006_, v_inst_1007_, v_n_1008_, v_c_1009_, v_i_1010_);
lean_dec(v_i_1010_);
lean_dec(v_c_1009_);
lean_dec(v_n_1008_);
lean_dec_ref(v_inst_1007_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___redArg___lam__0(lean_object* v_n_1012_, lean_object* v_toAddCommMonoid_1013_, lean_object* v_l_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_nat_dec_lt(v_l_1014_, v_n_1012_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v_toZero_1018_; 
lean_dec(v___y_1015_);
lean_dec(v_l_1014_);
v___x_1017_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_1013_);
v_toZero_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_toZero_1018_);
lean_dec_ref(v___x_1017_);
return v_toZero_1018_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_apply_1(v___y_1015_, v_l_1014_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___redArg___lam__0___boxed(lean_object* v_n_1020_, lean_object* v_toAddCommMonoid_1021_, lean_object* v_l_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = lp_tree_Formalism_L2_Col_Loc_inX___redArg___lam__0(v_n_1020_, v_toAddCommMonoid_1021_, v_l_1022_, v___y_1023_);
lean_dec_ref(v_toAddCommMonoid_1021_);
lean_dec(v_n_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___redArg(lean_object* v_inst_1025_, lean_object* v_n_1026_){
_start:
{
lean_object* v_toSemiring_1027_; lean_object* v_toAddCommMonoid_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; 
v_toSemiring_1027_ = lean_ctor_get(v_inst_1025_, 0);
lean_inc_ref(v_toSemiring_1027_);
lean_dec_ref(v_inst_1025_);
v_toAddCommMonoid_1028_ = lean_ctor_get(v_toSemiring_1027_, 0);
lean_inc_ref(v_toAddCommMonoid_1028_);
lean_dec_ref(v_toSemiring_1027_);
v___f_1029_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_inX___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1029_, 0, v_n_1026_);
lean_closure_set(v___f_1029_, 1, v_toAddCommMonoid_1028_);
v___f_1030_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1030_, 0, v___f_1029_);
return v___f_1030_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX(lean_object* v_k_1031_, lean_object* v_inst_1032_, lean_object* v_n_1033_, lean_object* v_c_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lp_tree_Formalism_L2_Col_Loc_inX___redArg(v_inst_1032_, v_n_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_inX___boxed(lean_object* v_k_1036_, lean_object* v_inst_1037_, lean_object* v_n_1038_, lean_object* v_c_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = lp_tree_Formalism_L2_Col_Loc_inX(v_k_1036_, v_inst_1037_, v_n_1038_, v_c_1039_);
lean_dec(v_c_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_R1(lean_object* v_k_1041_, lean_object* v_inst_1042_, lean_object* v_n_1043_, lean_object* v_c_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_box(0);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_R1___boxed(lean_object* v_k_1046_, lean_object* v_inst_1047_, lean_object* v_n_1048_, lean_object* v_c_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = lp_tree_Formalism_L2_Col_Loc_R1(v_k_1046_, v_inst_1047_, v_n_1048_, v_c_1049_);
lean_dec(v_c_1049_);
lean_dec(v_n_1048_);
lean_dec_ref(v_inst_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_fixX(lean_object* v_k_1051_, lean_object* v_inst_1052_, lean_object* v_n_1053_, lean_object* v_c_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_fixX___boxed(lean_object* v_k_1056_, lean_object* v_inst_1057_, lean_object* v_n_1058_, lean_object* v_c_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = lp_tree_Formalism_L2_Col_Loc_fixX(v_k_1056_, v_inst_1057_, v_n_1058_, v_c_1059_);
lean_dec(v_c_1059_);
lean_dec(v_n_1058_);
lean_dec_ref(v_inst_1057_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_N1(lean_object* v_k_1061_, lean_object* v_inst_1062_, lean_object* v_n_1063_, lean_object* v_c_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_N1___boxed(lean_object* v_k_1066_, lean_object* v_inst_1067_, lean_object* v_n_1068_, lean_object* v_c_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = lp_tree_Formalism_L2_Col_Loc_N1(v_k_1066_, v_inst_1067_, v_n_1068_, v_c_1069_);
lean_dec(v_c_1069_);
lean_dec(v_n_1068_);
lean_dec_ref(v_inst_1067_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg___lam__0(lean_object* v_r_1071_, lean_object* v_n_1072_, lean_object* v_c_1073_, lean_object* v___x_1074_, lean_object* v_inst_1075_, lean_object* v_i_1076_){
_start:
{
lean_object* v_toLinearMap_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_toLinearMap_1077_ = lean_ctor_get(v_r_1071_, 0);
lean_inc(v_toLinearMap_1077_);
lean_dec_ref(v_r_1071_);
v___x_1078_ = lean_nat_add(v_n_1072_, v_c_1073_);
v___x_1079_ = lean_nat_add(v_n_1072_, v_i_1076_);
v___x_1080_ = lean_nat_add(v___x_1079_, v___x_1074_);
lean_inc(v___x_1078_);
lean_inc_ref(v_inst_1075_);
v___x_1081_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_eN___boxed), 5, 4);
lean_closure_set(v___x_1081_, 0, lean_box(0));
lean_closure_set(v___x_1081_, 1, v_inst_1075_);
lean_closure_set(v___x_1081_, 2, v___x_1078_);
lean_closure_set(v___x_1081_, 3, v___x_1080_);
v___x_1082_ = lean_apply_1(v_toLinearMap_1077_, v___x_1081_);
v___x_1083_ = lp_tree_Formalism_L2_Col_Loc_atN___redArg(v_inst_1075_, v___x_1078_, v___x_1082_, v___x_1079_);
lean_dec(v___x_1078_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg___lam__0___boxed(lean_object* v_r_1084_, lean_object* v_n_1085_, lean_object* v_c_1086_, lean_object* v___x_1087_, lean_object* v_inst_1088_, lean_object* v_i_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg___lam__0(v_r_1084_, v_n_1085_, v_c_1086_, v___x_1087_, v_inst_1088_, v_i_1089_);
lean_dec(v_i_1089_);
lean_dec(v___x_1087_);
lean_dec(v_c_1086_);
lean_dec(v_n_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg(lean_object* v_inst_1091_, lean_object* v_n_1092_, lean_object* v_c_1093_, lean_object* v_r_1094_){
_start:
{
lean_object* v_toSemiring_1095_; lean_object* v_toAddCommMonoid_1096_; lean_object* v___x_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_toSemiring_1095_ = lean_ctor_get(v_inst_1091_, 0);
v_toAddCommMonoid_1096_ = lean_ctor_get(v_toSemiring_1095_, 0);
lean_inc_ref(v_toAddCommMonoid_1096_);
v___x_1097_ = lean_unsigned_to_nat(1u);
lean_inc(v_c_1093_);
v___f_1098_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1098_, 0, v_r_1094_);
lean_closure_set(v___f_1098_, 1, v_n_1092_);
lean_closure_set(v___f_1098_, 2, v_c_1093_);
lean_closure_set(v___f_1098_, 3, v___x_1097_);
lean_closure_set(v___f_1098_, 4, v_inst_1091_);
v___x_1099_ = lean_nat_sub(v_c_1093_, v___x_1097_);
lean_dec(v_c_1093_);
v___x_1100_ = l_List_range(v___x_1099_);
v___x_1101_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_1096_, v___x_1100_, v___f_1098_);
lean_dec_ref(v_toAddCommMonoid_1096_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_n1Arg(lean_object* v_k_1102_, lean_object* v_inst_1103_, lean_object* v_n_1104_, lean_object* v_c_1105_, lean_object* v_r_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lp_tree_Formalism_L2_Col_Loc_n1Arg___redArg(v_inst_1103_, v_n_1104_, v_c_1105_, v_r_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Cbe(lean_object* v_k_1108_, lean_object* v_inst_1109_, lean_object* v_n_1110_, lean_object* v_c_1111_, lean_object* v_J_1112_, lean_object* v_h_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_box(0);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_Cbe___boxed(lean_object* v_k_1115_, lean_object* v_inst_1116_, lean_object* v_n_1117_, lean_object* v_c_1118_, lean_object* v_J_1119_, lean_object* v_h_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = lp_tree_Formalism_L2_Col_Loc_Cbe(v_k_1115_, v_inst_1116_, v_n_1117_, v_c_1118_, v_J_1119_, v_h_1120_);
lean_dec_ref(v_h_1120_);
lean_dec(v_c_1118_);
lean_dec(v_n_1117_);
lean_dec_ref(v_inst_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_prX(lean_object* v_k_1122_, lean_object* v_inst_1123_, lean_object* v_n_1124_, lean_object* v_c_1125_, lean_object* v_C_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_prX___boxed(lean_object* v_k_1128_, lean_object* v_inst_1129_, lean_object* v_n_1130_, lean_object* v_c_1131_, lean_object* v_C_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = lp_tree_Formalism_L2_Col_Loc_prX(v_k_1128_, v_inst_1129_, v_n_1130_, v_c_1131_, v_C_1132_);
lean_dec(v_c_1131_);
lean_dec(v_n_1130_);
lean_dec_ref(v_inst_1129_);
return v_res_1133_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree(lean_object* v_n_x27_1134_, lean_object* v_n_1135_, lean_object* v_c_1136_, lean_object* v_l_1137_, lean_object* v_s_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_nat_dec_le(v_n_x27_1134_, v_s_1138_);
if (v___x_1139_ == 0)
{
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_nat_sub(v_s_1138_, v_n_x27_1134_);
v___x_1141_ = lean_nat_dec_eq(v___x_1140_, v_c_1136_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_dec_le(v___x_1142_, v___x_1140_);
if (v___x_1143_ == 0)
{
lean_dec(v___x_1140_);
return v___x_1143_;
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_nat_dec_lt(v_l_1137_, v_n_1135_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_nat_sub(v_l_1137_, v_n_1135_);
v___x_1146_ = lean_nat_dec_lt(v___x_1145_, v___x_1140_);
lean_dec(v___x_1140_);
lean_dec(v___x_1145_);
return v___x_1146_;
}
else
{
lean_dec(v___x_1140_);
return v___x_1144_;
}
}
}
else
{
lean_dec(v___x_1140_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree___boxed(lean_object* v_n_x27_1147_, lean_object* v_n_1148_, lean_object* v_c_1149_, lean_object* v_l_1150_, lean_object* v_s_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree(v_n_x27_1147_, v_n_1148_, v_c_1149_, v_l_1150_, v_s_1151_);
lean_dec(v_s_1151_);
lean_dec(v_l_1150_);
lean_dec(v_c_1149_);
lean_dec(v_n_1148_);
lean_dec(v_n_x27_1147_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___lam__0(lean_object* v_n_x27_1154_, lean_object* v_n_1155_, lean_object* v_c_1156_, lean_object* v_toSemiring_1157_, lean_object* v_inst_1158_, lean_object* v_xj_1159_, lean_object* v_t_1160_, lean_object* v_l_1161_, lean_object* v_s_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree(v_n_x27_1154_, v_n_1155_, v_c_1156_, v_l_1161_, v_s_1162_);
if (v___x_1163_ == 0)
{
uint8_t v___x_1164_; 
lean_dec(v_t_1160_);
v___x_1164_ = lean_nat_dec_lt(v_s_1162_, v_n_x27_1154_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
lean_dec(v_xj_1159_);
v___x_1165_ = lean_nat_sub(v_s_1162_, v_n_x27_1154_);
lean_dec(v_n_x27_1154_);
lean_dec(v_s_1162_);
v___x_1166_ = lean_nat_add(v_n_1155_, v___x_1165_);
lean_dec(v___x_1165_);
v___x_1167_ = lean_nat_dec_eq(v_l_1161_, v___x_1166_);
lean_dec(v___x_1166_);
lean_dec(v_l_1161_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v_toZero_1169_; 
lean_dec_ref(v_inst_1158_);
v___x_1168_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_1157_);
v_toZero_1169_ = lean_ctor_get(v___x_1168_, 1);
lean_inc(v_toZero_1169_);
lean_dec_ref(v___x_1168_);
return v_toZero_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v_toAddMonoidWithOne_1171_; lean_object* v_toOne_1172_; 
lean_dec_ref(v_toSemiring_1157_);
v___x_1170_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1158_);
v_toAddMonoidWithOne_1171_ = lean_ctor_get(v___x_1170_, 1);
lean_inc_ref(v_toAddMonoidWithOne_1171_);
lean_dec_ref(v___x_1170_);
v_toOne_1172_ = lean_ctor_get(v_toAddMonoidWithOne_1171_, 2);
lean_inc(v_toOne_1172_);
lean_dec_ref(v_toAddMonoidWithOne_1171_);
return v_toOne_1172_;
}
}
else
{
uint8_t v___x_1173_; 
lean_dec_ref(v_inst_1158_);
v___x_1173_ = lean_nat_dec_lt(v_l_1161_, v_n_1155_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v_toZero_1175_; 
lean_dec(v_s_1162_);
lean_dec(v_l_1161_);
lean_dec(v_xj_1159_);
lean_dec(v_n_x27_1154_);
v___x_1174_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_1157_);
v_toZero_1175_ = lean_ctor_get(v___x_1174_, 1);
lean_inc(v_toZero_1175_);
lean_dec_ref(v___x_1174_);
return v_toZero_1175_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_toLinearMap_1179_; lean_object* v___x_1180_; 
lean_inc(v_n_x27_1154_);
v___x_1176_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1176_, 0, v_n_x27_1154_);
v___x_1177_ = l_List_finRange(v_n_x27_1154_);
v___x_1178_ = lp_mathlib_LinearMap_toMatrix_x27___redArg(v_toSemiring_1157_, v___x_1176_, v___x_1177_);
v_toLinearMap_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_toLinearMap_1179_);
lean_dec_ref(v___x_1178_);
v___x_1180_ = lean_apply_3(v_toLinearMap_1179_, v_xj_1159_, v_l_1161_, v_s_1162_);
return v___x_1180_;
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v_xj_1159_);
lean_dec_ref(v_inst_1158_);
lean_dec_ref(v_toSemiring_1157_);
lean_dec(v_n_x27_1154_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_l_1161_);
lean_ctor_set(v___x_1181_, 1, v_s_1162_);
v___x_1182_ = lean_apply_1(v_t_1160_, v___x_1181_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___lam__0___boxed(lean_object* v_n_x27_1183_, lean_object* v_n_1184_, lean_object* v_c_1185_, lean_object* v_toSemiring_1186_, lean_object* v_inst_1187_, lean_object* v_xj_1188_, lean_object* v_t_1189_, lean_object* v_l_1190_, lean_object* v_s_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = lp_tree_Formalism_L2_Col_Loc_xx1___redArg___lam__0(v_n_x27_1183_, v_n_1184_, v_c_1185_, v_toSemiring_1186_, v_inst_1187_, v_xj_1188_, v_t_1189_, v_l_1190_, v_s_1191_);
lean_dec(v_c_1185_);
lean_dec(v_n_1184_);
return v_res_1192_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_Loc_xx1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg(lean_object* v_inst_1194_, lean_object* v_n_x27_1195_, lean_object* v_c_x27_1196_, lean_object* v_n_1197_, lean_object* v_c_1198_, lean_object* v_xj_1199_, lean_object* v_t_1200_){
_start:
{
lean_object* v_toSemiring_1201_; lean_object* v___x_1202_; lean_object* v_toFun_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_toLinearMap_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_toSemiring_1201_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc_ref_n(v_toSemiring_1201_, 2);
v___x_1202_ = lean_obj_once(&lp_tree_Formalism_L2_Col_Loc_xx1___redArg___closed__0, &lp_tree_Formalism_L2_Col_Loc_xx1___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Col_Loc_xx1___redArg___closed__0);
v_toFun_1203_ = lean_ctor_get(v___x_1202_, 0);
v___x_1204_ = lean_nat_add(v_n_x27_1195_, v_c_x27_1196_);
lean_inc(v___x_1204_);
v___x_1205_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1205_, 0, v___x_1204_);
v___x_1206_ = l_List_finRange(v___x_1204_);
v___x_1207_ = lp_mathlib_Matrix_toLin_x27___redArg(v_toSemiring_1201_, v___x_1205_, v___x_1206_);
v_toLinearMap_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_toLinearMap_1208_);
lean_dec_ref(v___x_1207_);
v___f_1209_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_xx1___redArg___lam__0___boxed), 9, 7);
lean_closure_set(v___f_1209_, 0, v_n_x27_1195_);
lean_closure_set(v___f_1209_, 1, v_n_1197_);
lean_closure_set(v___f_1209_, 2, v_c_1198_);
lean_closure_set(v___f_1209_, 3, v_toSemiring_1201_);
lean_closure_set(v___f_1209_, 4, v_inst_1194_);
lean_closure_set(v___f_1209_, 5, v_xj_1199_);
lean_closure_set(v___f_1209_, 6, v_t_1200_);
lean_inc(v_toFun_1203_);
v___x_1210_ = lean_apply_1(v_toFun_1203_, v___f_1209_);
v___x_1211_ = lean_apply_1(v_toLinearMap_1208_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___redArg___boxed(lean_object* v_inst_1212_, lean_object* v_n_x27_1213_, lean_object* v_c_x27_1214_, lean_object* v_n_1215_, lean_object* v_c_1216_, lean_object* v_xj_1217_, lean_object* v_t_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = lp_tree_Formalism_L2_Col_Loc_xx1___redArg(v_inst_1212_, v_n_x27_1213_, v_c_x27_1214_, v_n_1215_, v_c_1216_, v_xj_1217_, v_t_1218_);
lean_dec(v_c_x27_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1(lean_object* v_k_1220_, lean_object* v_inst_1221_, lean_object* v_n_x27_1222_, lean_object* v_c_x27_1223_, lean_object* v_n_1224_, lean_object* v_c_1225_, lean_object* v_xj_1226_, lean_object* v_t_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = lp_tree_Formalism_L2_Col_Loc_xx1___redArg(v_inst_1221_, v_n_x27_1222_, v_c_x27_1223_, v_n_1224_, v_c_1225_, v_xj_1226_, v_t_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_xx1___boxed(lean_object* v_k_1229_, lean_object* v_inst_1230_, lean_object* v_n_x27_1231_, lean_object* v_c_x27_1232_, lean_object* v_n_1233_, lean_object* v_c_1234_, lean_object* v_xj_1235_, lean_object* v_t_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = lp_tree_Formalism_L2_Col_Loc_xx1(v_k_1229_, v_inst_1230_, v_n_x27_1231_, v_c_x27_1232_, v_n_1233_, v_c_1234_, v_xj_1235_, v_t_1236_);
lean_dec(v_c_x27_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg___redArg___lam__0(lean_object* v_n_1238_, lean_object* v_c_1239_, lean_object* v_n_x27_1240_, lean_object* v_c_x27_1241_, lean_object* v_inst_1242_, lean_object* v_x_1243_, lean_object* v_i_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1245_ = lean_nat_add(v_n_1238_, v_c_1239_);
v___x_1246_ = lean_nat_add(v_n_x27_1240_, v_c_x27_1241_);
v___x_1247_ = lean_nat_add(v_n_x27_1240_, v_i_1244_);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v___x_1247_, v___x_1248_);
lean_dec(v___x_1247_);
lean_inc_ref(v_inst_1242_);
v___x_1250_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_eN___boxed), 5, 4);
lean_closure_set(v___x_1250_, 0, lean_box(0));
lean_closure_set(v___x_1250_, 1, v_inst_1242_);
lean_closure_set(v___x_1250_, 2, v___x_1246_);
lean_closure_set(v___x_1250_, 3, v___x_1249_);
v___x_1251_ = lean_apply_1(v_x_1243_, v___x_1250_);
v___x_1252_ = lean_nat_add(v_n_1238_, v_i_1244_);
v___x_1253_ = lp_tree_Formalism_L2_Col_Loc_atN___redArg(v_inst_1242_, v___x_1245_, v___x_1251_, v___x_1252_);
lean_dec(v___x_1245_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg___redArg___lam__0___boxed(lean_object* v_n_1254_, lean_object* v_c_1255_, lean_object* v_n_x27_1256_, lean_object* v_c_x27_1257_, lean_object* v_inst_1258_, lean_object* v_x_1259_, lean_object* v_i_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = lp_tree_Formalism_L2_Col_Loc_chArg___redArg___lam__0(v_n_1254_, v_c_1255_, v_n_x27_1256_, v_c_x27_1257_, v_inst_1258_, v_x_1259_, v_i_1260_);
lean_dec(v_i_1260_);
lean_dec(v_c_x27_1257_);
lean_dec(v_n_x27_1256_);
lean_dec(v_c_1255_);
lean_dec(v_n_1254_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg___redArg(lean_object* v_inst_1262_, lean_object* v_n_x27_1263_, lean_object* v_c_x27_1264_, lean_object* v_n_1265_, lean_object* v_c_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v_toSemiring_1268_; lean_object* v_toAddCommMonoid_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_toSemiring_1268_ = lean_ctor_get(v_inst_1262_, 0);
v_toAddCommMonoid_1269_ = lean_ctor_get(v_toSemiring_1268_, 0);
lean_inc_ref(v_toAddCommMonoid_1269_);
lean_inc(v_c_1266_);
v___f_1270_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_chArg___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1270_, 0, v_n_1265_);
lean_closure_set(v___f_1270_, 1, v_c_1266_);
lean_closure_set(v___f_1270_, 2, v_n_x27_1263_);
lean_closure_set(v___f_1270_, 3, v_c_x27_1264_);
lean_closure_set(v___f_1270_, 4, v_inst_1262_);
lean_closure_set(v___f_1270_, 5, v_x_1267_);
v___x_1271_ = l_List_range(v_c_1266_);
v___x_1272_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_1269_, v___x_1271_, v___f_1270_);
lean_dec_ref(v_toAddCommMonoid_1269_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_chArg(lean_object* v_k_1273_, lean_object* v_inst_1274_, lean_object* v_n_x27_1275_, lean_object* v_c_x27_1276_, lean_object* v_n_1277_, lean_object* v_c_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lp_tree_Formalism_L2_Col_Loc_chArg___redArg(v_inst_1274_, v_n_x27_1275_, v_c_x27_1276_, v_n_1277_, v_c_1278_, v_x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__0(lean_object* v_vals_1281_, lean_object* v_x_1282_){
_start:
{
lean_inc(v_vals_1281_);
return v_vals_1281_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__0___boxed(lean_object* v_vals_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__0(v_vals_1283_, v_x_1284_);
lean_dec_ref(v_x_1284_);
lean_dec(v_vals_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__1(lean_object* v_n_x27_1286_, lean_object* v_n_1287_, lean_object* v_c_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_fst_1290_; lean_object* v_snd_1291_; uint8_t v___x_1292_; 
v_fst_1290_ = lean_ctor_get(v_a_1289_, 0);
v_snd_1291_ = lean_ctor_get(v_a_1289_, 1);
v___x_1292_ = lp_tree_Formalism_L2_Col_Loc_instDecidableIsFree(v_n_x27_1286_, v_n_1287_, v_c_1288_, v_fst_1290_, v_snd_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__1___boxed(lean_object* v_n_x27_1293_, lean_object* v_n_1294_, lean_object* v_c_1295_, lean_object* v_a_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__1(v_n_x27_1293_, v_n_1294_, v_c_1295_, v_a_1296_);
lean_dec_ref(v_a_1296_);
lean_dec(v_c_1295_);
lean_dec(v_n_1294_);
lean_dec(v_n_x27_1293_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__2(lean_object* v_inst_1299_, lean_object* v_n_x27_1300_, lean_object* v_c_x27_1301_, lean_object* v_n_1302_, lean_object* v_c_1303_, lean_object* v_xj_1304_, lean_object* v_00_u03a6_1305_, lean_object* v_toNeg_1306_, lean_object* v_psi_1307_, lean_object* v_toMul_1308_, lean_object* v_t_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_inc(v_c_1303_);
lean_inc(v_n_1302_);
lean_inc(v_n_x27_1300_);
lean_inc_ref(v_inst_1299_);
v___x_1310_ = lp_tree_Formalism_L2_Col_Loc_xx1___redArg(v_inst_1299_, v_n_x27_1300_, v_c_x27_1301_, v_n_1302_, v_c_1303_, v_xj_1304_, v_t_1309_);
lean_inc(v___x_1310_);
v___x_1311_ = lean_apply_1(v_00_u03a6_1305_, v___x_1310_);
v___x_1312_ = lp_tree_Formalism_L2_Col_Loc_chArg___redArg(v_inst_1299_, v_n_x27_1300_, v_c_x27_1301_, v_n_1302_, v_c_1303_, v___x_1310_);
v___x_1313_ = lean_apply_1(v_toNeg_1306_, v___x_1312_);
v___x_1314_ = lean_apply_1(v_psi_1307_, v___x_1313_);
v___x_1315_ = lean_apply_2(v_toMul_1308_, v___x_1311_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__3(lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v_a_1318_, lean_object* v_b_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1320_, 0, v___x_1316_);
v___x_1321_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_1321_, 0, v___x_1317_);
v___x_1322_ = l_instDecidableEqProd___redArg(v___x_1320_, v___x_1321_, v_a_1318_, v_b_1319_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__3___boxed(lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_a_1325_, lean_object* v_b_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__3(v___x_1323_, v___x_1324_, v_a_1325_, v_b_1326_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg(lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_n_x27_1331_, lean_object* v_c_x27_1332_, lean_object* v_n_1333_, lean_object* v_c_1334_, lean_object* v_psi_1335_, lean_object* v_vals_1336_, lean_object* v_wt_1337_, lean_object* v_00_u03a6_1338_, lean_object* v_xj_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_toSemiring_1342_; lean_object* v___x_1343_; lean_object* v_toMonoid_1344_; lean_object* v_toMul_1345_; lean_object* v_toAddCommMonoid_1346_; lean_object* v_toNPow_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_toNeg_1350_; lean_object* v___f_1351_; lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1340_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1330_);
v___x_1341_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1340_);
v_toSemiring_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_ref_n(v_toSemiring_1342_, 2);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_1342_);
v_toMonoid_1344_ = lean_ctor_get(v_toSemiring_1342_, 1);
lean_inc_ref(v_toMonoid_1344_);
v_toMul_1345_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_n(v_toMul_1345_, 2);
lean_dec_ref(v___x_1343_);
v_toAddCommMonoid_1346_ = lean_ctor_get(v_toSemiring_1342_, 0);
lean_inc_ref(v_toAddCommMonoid_1346_);
lean_dec_ref(v_toSemiring_1342_);
v_toNPow_1347_ = lean_ctor_get(v_toMonoid_1344_, 2);
lean_inc(v_toNPow_1347_);
lean_dec_ref(v_toMonoid_1344_);
v___x_1348_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_1329_);
v___x_1349_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_1348_);
lean_dec_ref(v___x_1348_);
v_toNeg_1350_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_toNeg_1350_);
lean_dec_ref(v___x_1349_);
v___f_1351_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1351_, 0, v_vals_1336_);
lean_inc_n(v_c_1334_, 2);
lean_inc_n(v_n_1333_, 2);
lean_inc_n(v_n_x27_1331_, 2);
v___f_1352_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1352_, 0, v_n_x27_1331_);
lean_closure_set(v___f_1352_, 1, v_n_1333_);
lean_closure_set(v___f_1352_, 2, v_c_1334_);
lean_inc(v_c_x27_1332_);
v___f_1353_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1353_, 0, v_inst_1329_);
lean_closure_set(v___f_1353_, 1, v_n_x27_1331_);
lean_closure_set(v___f_1353_, 2, v_c_x27_1332_);
lean_closure_set(v___f_1353_, 3, v_n_1333_);
lean_closure_set(v___f_1353_, 4, v_c_1334_);
lean_closure_set(v___f_1353_, 5, v_xj_1339_);
lean_closure_set(v___f_1353_, 6, v_00_u03a6_1338_);
lean_closure_set(v___f_1353_, 7, v_toNeg_1350_);
lean_closure_set(v___f_1353_, 8, v_psi_1335_);
lean_closure_set(v___f_1353_, 9, v_toMul_1345_);
v___x_1354_ = lean_nat_add(v_n_1333_, v_c_1334_);
lean_dec(v_c_1334_);
lean_dec(v_n_1333_);
lean_inc(v___x_1354_);
v___x_1355_ = l_List_finRange(v___x_1354_);
v___x_1356_ = lean_nat_add(v_n_x27_1331_, v_c_x27_1332_);
lean_dec(v_c_x27_1332_);
lean_dec(v_n_x27_1331_);
lean_inc(v___x_1356_);
v___f_1357_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_E1___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1357_, 0, v___x_1354_);
lean_closure_set(v___f_1357_, 1, v___x_1356_);
v___x_1358_ = l_List_finRange(v___x_1356_);
v___x_1359_ = lp_mathlib_Multiset_product___redArg(v___x_1355_, v___x_1358_);
v___x_1360_ = lp_mathlib_Subtype_fintype___redArg(v___f_1352_, v___x_1359_);
v___x_1361_ = l_List_lengthTR___redArg(v___x_1360_);
v___x_1362_ = lean_apply_2(v_toNPow_1347_, v___x_1361_, v_wt_1337_);
v___x_1363_ = lp_mathlib_Fintype_piFinset___redArg(v___f_1357_, v___x_1360_, v___f_1351_);
v___x_1364_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_1346_, v___x_1363_, v___f_1353_);
lean_dec_ref(v_toAddCommMonoid_1346_);
v___x_1365_ = lean_apply_2(v_toMul_1345_, v___x_1362_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___redArg___boxed(lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_n_x27_1368_, lean_object* v_c_x27_1369_, lean_object* v_n_1370_, lean_object* v_c_1371_, lean_object* v_psi_1372_, lean_object* v_vals_1373_, lean_object* v_wt_1374_, lean_object* v_00_u03a6_1375_, lean_object* v_xj_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = lp_tree_Formalism_L2_Col_Loc_E1___redArg(v_inst_1366_, v_inst_1367_, v_n_x27_1368_, v_c_x27_1369_, v_n_1370_, v_c_1371_, v_psi_1372_, v_vals_1373_, v_wt_1374_, v_00_u03a6_1375_, v_xj_1376_);
lean_dec_ref(v_inst_1367_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1(lean_object* v_k_1378_, lean_object* v_K_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_n_x27_1382_, lean_object* v_c_x27_1383_, lean_object* v_n_1384_, lean_object* v_c_1385_, lean_object* v_psi_1386_, lean_object* v_vals_1387_, lean_object* v_wt_1388_, lean_object* v_00_u03a6_1389_, lean_object* v_xj_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lp_tree_Formalism_L2_Col_Loc_E1___redArg(v_inst_1380_, v_inst_1381_, v_n_x27_1382_, v_c_x27_1383_, v_n_1384_, v_c_1385_, v_psi_1386_, v_vals_1387_, v_wt_1388_, v_00_u03a6_1389_, v_xj_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Loc_E1___boxed(lean_object* v_k_1392_, lean_object* v_K_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_n_x27_1396_, lean_object* v_c_x27_1397_, lean_object* v_n_1398_, lean_object* v_c_1399_, lean_object* v_psi_1400_, lean_object* v_vals_1401_, lean_object* v_wt_1402_, lean_object* v_00_u03a6_1403_, lean_object* v_xj_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = lp_tree_Formalism_L2_Col_Loc_E1(v_k_1392_, v_K_1393_, v_inst_1394_, v_inst_1395_, v_n_x27_1396_, v_c_x27_1397_, v_n_1398_, v_c_1399_, v_psi_1400_, v_vals_1401_, v_wt_1402_, v_00_u03a6_1403_, v_xj_1404_);
lean_dec_ref(v_inst_1395_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_homAt(lean_object* v_E_1406_, lean_object* v_inst_1407_, lean_object* v_a_1408_, lean_object* v_b_1409_, lean_object* v_S_1410_, lean_object* v_N_1411_, lean_object* v_N_x27_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_homAt___boxed(lean_object* v_E_1414_, lean_object* v_inst_1415_, lean_object* v_a_1416_, lean_object* v_b_1417_, lean_object* v_S_1418_, lean_object* v_N_1419_, lean_object* v_N_x27_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = lp_tree_Formalism_L2_Col_homAt(v_E_1414_, v_inst_1415_, v_a_1416_, v_b_1417_, v_S_1418_, v_N_1419_, v_N_x27_1420_);
lean_dec(v_S_1418_);
lean_dec(v_b_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_inst_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_divLat(lean_object* v_E_1422_, lean_object* v_inst_1423_, lean_object* v_H_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_c_1427_, lean_object* v_M_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_divLat___boxed(lean_object* v_E_1430_, lean_object* v_inst_1431_, lean_object* v_H_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_c_1435_, lean_object* v_M_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = lp_tree_Formalism_L2_Col_divLat(v_E_1430_, v_inst_1431_, v_H_1432_, v_inst_1433_, v_inst_1434_, v_c_1435_, v_M_1436_);
lean_dec(v_c_1435_);
lean_dec(v_inst_1434_);
lean_dec_ref(v_inst_1433_);
lean_dec_ref(v_inst_1431_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mulLat(lean_object* v_E_1438_, lean_object* v_inst_1439_, lean_object* v_H_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_c_1443_, lean_object* v_M_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_box(0);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_mulLat___boxed(lean_object* v_E_1446_, lean_object* v_inst_1447_, lean_object* v_H_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_c_1451_, lean_object* v_M_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = lp_tree_Formalism_L2_Col_mulLat(v_E_1446_, v_inst_1447_, v_H_1448_, v_inst_1449_, v_inst_1450_, v_c_1451_, v_M_1452_);
lean_dec(v_c_1451_);
lean_dec(v_inst_1450_);
lean_dec_ref(v_inst_1449_);
lean_dec_ref(v_inst_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inFr___redArg(lean_object* v_f_1454_, lean_object* v_f_x27_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v_toLinearMap_1458_; lean_object* v_toLinearMap_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; 
v___x_1457_ = lp_mathlib_LinearEquiv_symm___redArg(v_f_x27_1455_);
v_toLinearMap_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_toLinearMap_1458_);
lean_dec_ref(v___x_1457_);
v_toLinearMap_1459_ = lean_ctor_get(v_f_1454_, 0);
lean_inc(v_toLinearMap_1459_);
lean_dec_ref(v_f_1454_);
v___f_1460_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1460_, 0, v_toLinearMap_1459_);
lean_closure_set(v___f_1460_, 1, v_x_1456_);
v___f_1461_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1461_, 0, v___f_1460_);
lean_closure_set(v___f_1461_, 1, v_toLinearMap_1458_);
return v___f_1461_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inFr(lean_object* v_E_1462_, lean_object* v_inst_1463_, lean_object* v_a_1464_, lean_object* v_b_1465_, lean_object* v_f_1466_, lean_object* v_f_x27_1467_, lean_object* v_x_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lp_tree_Formalism_L2_Col_inFr___redArg(v_f_1466_, v_f_x27_1467_, v_x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inFr___boxed(lean_object* v_E_1470_, lean_object* v_inst_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_, lean_object* v_f_1474_, lean_object* v_f_x27_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = lp_tree_Formalism_L2_Col_inFr(v_E_1470_, v_inst_1471_, v_a_1472_, v_b_1473_, v_f_1474_, v_f_x27_1475_, v_x_1476_);
lean_dec(v_b_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_inst_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_sclLat(lean_object* v_E_1478_, lean_object* v_inst_1479_, lean_object* v_P_1480_, lean_object* v_q_1481_, lean_object* v_N_1482_, lean_object* v_e_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_box(0);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_sclLat___boxed(lean_object* v_E_1485_, lean_object* v_inst_1486_, lean_object* v_P_1487_, lean_object* v_q_1488_, lean_object* v_N_1489_, lean_object* v_e_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = lp_tree_Formalism_L2_Col_LocE_sclLat(v_E_1485_, v_inst_1486_, v_P_1487_, v_q_1488_, v_N_1489_, v_e_1490_);
lean_dec_ref(v_e_1490_);
lean_dec(v_N_1489_);
lean_dec(v_q_1488_);
lean_dec_ref(v_inst_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fIdx(lean_object* v_k_u2080_1492_, lean_object* v_c_1493_, lean_object* v_n_1494_, lean_object* v_s_1495_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_lt(v_s_1495_, v_k_u2080_1492_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = lean_nat_add(v_k_u2080_1492_, v_c_1493_);
v___x_1498_ = lean_nat_dec_lt(v_s_1495_, v___x_1497_);
lean_dec(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_nat_sub(v_s_1495_, v_c_1493_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_nat_sub(v_s_1495_, v_k_u2080_1492_);
v___x_1501_ = lean_nat_add(v_n_1494_, v___x_1500_);
lean_dec(v___x_1500_);
return v___x_1501_;
}
}
else
{
lean_inc(v_s_1495_);
return v_s_1495_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fIdx___boxed(lean_object* v_k_u2080_1502_, lean_object* v_c_1503_, lean_object* v_n_1504_, lean_object* v_s_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = lp_tree_Formalism_L2_Col_LocE_fIdx(v_k_u2080_1502_, v_c_1503_, v_n_1504_, v_s_1505_);
lean_dec(v_s_1505_);
lean_dec(v_n_1504_);
lean_dec(v_c_1503_);
lean_dec(v_k_u2080_1502_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fPos(lean_object* v_k_u2080_1507_, lean_object* v_c_1508_, lean_object* v_n_1509_, lean_object* v_l_1510_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_lt(v_l_1510_, v_k_u2080_1507_);
if (v___x_1511_ == 0)
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_lt(v_l_1510_, v_n_1509_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_nat_sub(v_l_1510_, v_n_1509_);
v___x_1514_ = lean_nat_add(v_k_u2080_1507_, v___x_1513_);
lean_dec(v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_nat_add(v_l_1510_, v_c_1508_);
return v___x_1515_;
}
}
else
{
lean_inc(v_l_1510_);
return v_l_1510_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_fPos___boxed(lean_object* v_k_u2080_1516_, lean_object* v_c_1517_, lean_object* v_n_1518_, lean_object* v_l_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = lp_tree_Formalism_L2_Col_LocE_fPos(v_k_u2080_1516_, v_c_1517_, v_n_1518_, v_l_1519_);
lean_dec(v_l_1519_);
lean_dec(v_n_1518_);
lean_dec(v_c_1517_);
lean_dec(v_k_u2080_1516_);
return v_res_1520_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_LocE_scE___closed__0(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_nat_to_int(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_scE(lean_object* v_n_1523_, lean_object* v_ex_1524_, lean_object* v_l_1525_){
_start:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_lt(v_l_1525_, v_n_1523_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_nat_sub(v_l_1525_, v_n_1523_);
v___x_1528_ = lean_apply_1(v_ex_1524_, v___x_1527_);
v___x_1529_ = lean_nat_to_int(v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; 
lean_dec_ref(v_ex_1524_);
v___x_1530_ = lean_obj_once(&lp_tree_Formalism_L2_Col_LocE_scE___closed__0, &lp_tree_Formalism_L2_Col_LocE_scE___closed__0_once, _init_lp_tree_Formalism_L2_Col_LocE_scE___closed__0);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_scE___boxed(lean_object* v_n_1531_, lean_object* v_ex_1532_, lean_object* v_l_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = lp_tree_Formalism_L2_Col_LocE_scE(v_n_1531_, v_ex_1532_, v_l_1533_);
lean_dec(v_l_1533_);
lean_dec(v_n_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_lamY(lean_object* v_E_1535_, lean_object* v_inst_1536_, lean_object* v_P_1537_, lean_object* v_q_1538_, lean_object* v_n_1539_, lean_object* v_c_1540_, lean_object* v_ex_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_lamY___boxed(lean_object* v_E_1543_, lean_object* v_inst_1544_, lean_object* v_P_1545_, lean_object* v_q_1546_, lean_object* v_n_1547_, lean_object* v_c_1548_, lean_object* v_ex_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = lp_tree_Formalism_L2_Col_LocE_lamY(v_E_1543_, v_inst_1544_, v_P_1545_, v_q_1546_, v_n_1547_, v_c_1548_, v_ex_1549_);
lean_dec_ref(v_ex_1549_);
lean_dec(v_c_1548_);
lean_dec(v_n_1547_);
lean_dec(v_q_1546_);
lean_dec_ref(v_inst_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB___redArg(lean_object* v_inst_1551_, lean_object* v_q_1552_, lean_object* v_N_x27_1553_, lean_object* v_N_1554_, lean_object* v_k_u2080_1555_, lean_object* v_c_x27_1556_, lean_object* v_n_x27_1557_, lean_object* v_c_1558_, lean_object* v_n_1559_, lean_object* v_ex_x27_1560_, lean_object* v_ex_1561_, lean_object* v_x_1562_, lean_object* v_p_1563_, lean_object* v_p_x27_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_toSemiring_1567_; lean_object* v___x_1568_; lean_object* v_toMul_1569_; lean_object* v_toCommRing_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v_toZPow_1573_; lean_object* v_toRing_1574_; lean_object* v___x_1575_; lean_object* v_toAddMonoidWithOne_1576_; lean_object* v_toNatCast_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1565_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1551_);
v___x_1566_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1565_);
v_toSemiring_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc_ref(v_toSemiring_1567_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_1567_);
v_toMul_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_toMul_1569_);
lean_dec_ref(v___x_1568_);
v_toCommRing_1570_ = lean_ctor_get(v_inst_1551_, 0);
lean_inc_ref_n(v_toCommRing_1570_, 2);
v___x_1571_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1551_);
v___x_1572_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_1571_);
v_toZPow_1573_ = lean_ctor_get(v___x_1572_, 3);
lean_inc(v_toZPow_1573_);
lean_dec_ref(v___x_1572_);
v_toRing_1574_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_ref(v_toRing_1574_);
lean_dec_ref(v___x_1571_);
v___x_1575_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_1574_);
v_toAddMonoidWithOne_1576_ = lean_ctor_get(v___x_1575_, 1);
lean_inc_ref(v_toAddMonoidWithOne_1576_);
lean_dec_ref(v___x_1575_);
v_toNatCast_1577_ = lean_ctor_get(v_toAddMonoidWithOne_1576_, 0);
lean_inc(v_toNatCast_1577_);
lean_dec_ref(v_toAddMonoidWithOne_1576_);
v___x_1578_ = lp_tree_Formalism_L2_Col_LocE_fIdx(v_k_u2080_1555_, v_c_x27_1556_, v_n_x27_1557_, v_p_x27_1564_);
lean_inc(v___x_1578_);
v___x_1579_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Loc_eN___boxed), 5, 4);
lean_closure_set(v___x_1579_, 0, lean_box(0));
lean_closure_set(v___x_1579_, 1, v_toCommRing_1570_);
lean_closure_set(v___x_1579_, 2, v_N_x27_1553_);
lean_closure_set(v___x_1579_, 3, v___x_1578_);
v___x_1580_ = lean_apply_1(v_x_1562_, v___x_1579_);
v___x_1581_ = lp_tree_Formalism_L2_Col_LocE_fIdx(v_k_u2080_1555_, v_c_1558_, v_n_1559_, v_p_1563_);
lean_inc(v___x_1581_);
v___x_1582_ = lp_tree_Formalism_L2_Col_Loc_atN___redArg(v_toCommRing_1570_, v_N_1554_, v___x_1580_, v___x_1581_);
v___x_1583_ = lean_apply_1(v_toNatCast_1577_, v_q_1552_);
v___x_1584_ = lp_tree_Formalism_L2_Col_LocE_scE(v_n_x27_1557_, v_ex_x27_1560_, v___x_1578_);
lean_dec(v___x_1578_);
v___x_1585_ = lp_tree_Formalism_L2_Col_LocE_scE(v_n_1559_, v_ex_1561_, v___x_1581_);
lean_dec(v___x_1581_);
v___x_1586_ = lean_int_sub(v___x_1584_, v___x_1585_);
lean_dec(v___x_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_apply_2(v_toZPow_1573_, v___x_1586_, v___x_1583_);
v___x_1588_ = lean_apply_2(v_toMul_1569_, v___x_1582_, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB___redArg___boxed(lean_object* v_inst_1589_, lean_object* v_q_1590_, lean_object* v_N_x27_1591_, lean_object* v_N_1592_, lean_object* v_k_u2080_1593_, lean_object* v_c_x27_1594_, lean_object* v_n_x27_1595_, lean_object* v_c_1596_, lean_object* v_n_1597_, lean_object* v_ex_x27_1598_, lean_object* v_ex_1599_, lean_object* v_x_1600_, lean_object* v_p_1601_, lean_object* v_p_x27_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = lp_tree_Formalism_L2_Col_LocE_entB___redArg(v_inst_1589_, v_q_1590_, v_N_x27_1591_, v_N_1592_, v_k_u2080_1593_, v_c_x27_1594_, v_n_x27_1595_, v_c_1596_, v_n_1597_, v_ex_x27_1598_, v_ex_1599_, v_x_1600_, v_p_1601_, v_p_x27_1602_);
lean_dec(v_p_x27_1602_);
lean_dec(v_p_1601_);
lean_dec(v_n_1597_);
lean_dec(v_c_1596_);
lean_dec(v_n_x27_1595_);
lean_dec(v_c_x27_1594_);
lean_dec(v_k_u2080_1593_);
lean_dec(v_N_1592_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB(lean_object* v_E_1604_, lean_object* v_inst_1605_, lean_object* v_q_1606_, lean_object* v_N_x27_1607_, lean_object* v_N_1608_, lean_object* v_k_u2080_1609_, lean_object* v_c_x27_1610_, lean_object* v_n_x27_1611_, lean_object* v_c_1612_, lean_object* v_n_1613_, lean_object* v_ex_x27_1614_, lean_object* v_ex_1615_, lean_object* v_x_1616_, lean_object* v_p_1617_, lean_object* v_p_x27_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lp_tree_Formalism_L2_Col_LocE_entB___redArg(v_inst_1605_, v_q_1606_, v_N_x27_1607_, v_N_1608_, v_k_u2080_1609_, v_c_x27_1610_, v_n_x27_1611_, v_c_1612_, v_n_1613_, v_ex_x27_1614_, v_ex_1615_, v_x_1616_, v_p_1617_, v_p_x27_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_entB___boxed(lean_object* v_E_1620_, lean_object* v_inst_1621_, lean_object* v_q_1622_, lean_object* v_N_x27_1623_, lean_object* v_N_1624_, lean_object* v_k_u2080_1625_, lean_object* v_c_x27_1626_, lean_object* v_n_x27_1627_, lean_object* v_c_1628_, lean_object* v_n_1629_, lean_object* v_ex_x27_1630_, lean_object* v_ex_1631_, lean_object* v_x_1632_, lean_object* v_p_1633_, lean_object* v_p_x27_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = lp_tree_Formalism_L2_Col_LocE_entB(v_E_1620_, v_inst_1621_, v_q_1622_, v_N_x27_1623_, v_N_1624_, v_k_u2080_1625_, v_c_x27_1626_, v_n_x27_1627_, v_c_1628_, v_n_1629_, v_ex_x27_1630_, v_ex_1631_, v_x_1632_, v_p_1633_, v_p_x27_1634_);
lean_dec(v_p_x27_1634_);
lean_dec(v_p_1633_);
lean_dec(v_n_1629_);
lean_dec(v_c_1628_);
lean_dec(v_n_x27_1627_);
lean_dec(v_c_x27_1626_);
lean_dec(v_k_u2080_1625_);
lean_dec(v_N_1624_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_parL(lean_object* v_E_1636_, lean_object* v_inst_1637_, lean_object* v_P_1638_, lean_object* v_q_1639_, lean_object* v_kj_1640_, lean_object* v_n_1641_, lean_object* v_c_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_box(0);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_parL___boxed(lean_object* v_E_1644_, lean_object* v_inst_1645_, lean_object* v_P_1646_, lean_object* v_q_1647_, lean_object* v_kj_1648_, lean_object* v_n_1649_, lean_object* v_c_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = lp_tree_Formalism_L2_Col_LocE_parL(v_E_1644_, v_inst_1645_, v_P_1646_, v_q_1647_, v_kj_1648_, v_n_1649_, v_c_1650_);
lean_dec(v_c_1650_);
lean_dec(v_n_1649_);
lean_dec(v_kj_1648_);
lean_dec(v_q_1647_);
lean_dec_ref(v_inst_1645_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JQ(lean_object* v_E_1652_, lean_object* v_inst_1653_, lean_object* v_P_1654_, lean_object* v_q_1655_, lean_object* v_kj_1656_, lean_object* v_n_1657_, lean_object* v_c_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_box(0);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JQ___boxed(lean_object* v_E_1660_, lean_object* v_inst_1661_, lean_object* v_P_1662_, lean_object* v_q_1663_, lean_object* v_kj_1664_, lean_object* v_n_1665_, lean_object* v_c_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = lp_tree_Formalism_L2_Col_LocE_JQ(v_E_1660_, v_inst_1661_, v_P_1662_, v_q_1663_, v_kj_1664_, v_n_1665_, v_c_1666_);
lean_dec(v_c_1666_);
lean_dec(v_n_1665_);
lean_dec(v_kj_1664_);
lean_dec(v_q_1663_);
lean_dec_ref(v_inst_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagU(lean_object* v_E_1668_, lean_object* v_inst_1669_, lean_object* v_N_1670_, lean_object* v_M_1671_, lean_object* v_e_1672_, lean_object* v_r_1673_, lean_object* v_st_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_box(0);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagU___boxed(lean_object* v_E_1676_, lean_object* v_inst_1677_, lean_object* v_N_1678_, lean_object* v_M_1679_, lean_object* v_e_1680_, lean_object* v_r_1681_, lean_object* v_st_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = lp_tree_Formalism_L2_Col_LocE_flagU(v_E_1676_, v_inst_1677_, v_N_1678_, v_M_1679_, v_e_1680_, v_r_1681_, v_st_1682_);
lean_dec(v_r_1681_);
lean_dec(v_e_1680_);
lean_dec_ref(v_M_1679_);
lean_dec(v_N_1678_);
lean_dec_ref(v_inst_1677_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagG(lean_object* v_E_1684_, lean_object* v_inst_1685_, lean_object* v_P_1686_, lean_object* v_q_1687_, lean_object* v_k_u2080_1688_, lean_object* v_n_1689_, lean_object* v_c_1690_, lean_object* v_s_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_box(0);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagG___boxed(lean_object* v_E_1693_, lean_object* v_inst_1694_, lean_object* v_P_1695_, lean_object* v_q_1696_, lean_object* v_k_u2080_1697_, lean_object* v_n_1698_, lean_object* v_c_1699_, lean_object* v_s_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = lp_tree_Formalism_L2_Col_LocE_flagG(v_E_1693_, v_inst_1694_, v_P_1695_, v_q_1696_, v_k_u2080_1697_, v_n_1698_, v_c_1699_, v_s_1700_);
lean_dec(v_s_1700_);
lean_dec(v_c_1699_);
lean_dec(v_n_1698_);
lean_dec(v_k_u2080_1697_);
lean_dec(v_q_1696_);
lean_dec_ref(v_inst_1694_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___lam__0(lean_object* v_i_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_add(v_i_1702_, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___lam__0___boxed(lean_object* v_i_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___lam__0(v_i_1705_);
lean_dec(v_i_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg(lean_object* v_inst_1708_, lean_object* v_q_1709_, lean_object* v_k_u2080_1710_, lean_object* v_n_1711_, lean_object* v_c_1712_, lean_object* v_s_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v_toSemiring_1717_; lean_object* v___x_1718_; lean_object* v_toMul_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v_toZPow_1722_; lean_object* v_toRing_1723_; lean_object* v___x_1724_; lean_object* v_toAddMonoidWithOne_1725_; lean_object* v_toNatCast_1726_; lean_object* v_toCommRing_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1715_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1708_);
v___x_1716_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1715_);
v_toSemiring_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_ref(v_toSemiring_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_1717_);
v_toMul_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_toMul_1719_);
lean_dec_ref(v___x_1718_);
lean_inc_ref(v_inst_1708_);
v___x_1720_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1708_);
v___x_1721_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_1720_);
v_toZPow_1722_ = lean_ctor_get(v___x_1721_, 3);
lean_inc(v_toZPow_1722_);
lean_dec_ref(v___x_1721_);
v_toRing_1723_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_ref(v_toRing_1723_);
lean_dec_ref(v___x_1720_);
v___x_1724_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_1723_);
v_toAddMonoidWithOne_1725_ = lean_ctor_get(v___x_1724_, 1);
lean_inc_ref(v_toAddMonoidWithOne_1725_);
lean_dec_ref(v___x_1724_);
v_toNatCast_1726_ = lean_ctor_get(v_toAddMonoidWithOne_1725_, 0);
lean_inc(v_toNatCast_1726_);
lean_dec_ref(v_toAddMonoidWithOne_1725_);
v_toCommRing_1727_ = lean_ctor_get(v_inst_1708_, 0);
lean_inc_ref(v_toCommRing_1727_);
lean_dec_ref(v_inst_1708_);
v___f_1728_ = ((lean_object*)(lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___closed__0));
v___x_1729_ = lean_apply_1(v_toNatCast_1726_, v_q_1709_);
v___x_1730_ = lp_tree_Formalism_L2_Col_LocE_fIdx(v_k_u2080_1710_, v_c_1712_, v_n_1711_, v_s_1713_);
v___x_1731_ = lp_tree_Formalism_L2_Col_LocE_scE(v_n_1711_, v___f_1728_, v___x_1730_);
v___x_1732_ = lean_apply_2(v_toZPow_1722_, v___x_1731_, v___x_1729_);
v___x_1733_ = lp_tree_Formalism_L2_Col_Loc_eN___redArg(v_toCommRing_1727_, v___x_1730_, v_a_1714_);
lean_dec(v___x_1730_);
v___x_1734_ = lean_apply_2(v_toMul_1719_, v___x_1732_, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___redArg___boxed(lean_object* v_inst_1735_, lean_object* v_q_1736_, lean_object* v_k_u2080_1737_, lean_object* v_n_1738_, lean_object* v_c_1739_, lean_object* v_s_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = lp_tree_Formalism_L2_Col_LocE_bvecG___redArg(v_inst_1735_, v_q_1736_, v_k_u2080_1737_, v_n_1738_, v_c_1739_, v_s_1740_, v_a_1741_);
lean_dec(v_a_1741_);
lean_dec(v_s_1740_);
lean_dec(v_c_1739_);
lean_dec(v_n_1738_);
lean_dec(v_k_u2080_1737_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG(lean_object* v_E_1743_, lean_object* v_inst_1744_, lean_object* v_q_1745_, lean_object* v_k_u2080_1746_, lean_object* v_n_1747_, lean_object* v_c_1748_, lean_object* v_s_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = lp_tree_Formalism_L2_Col_LocE_bvecG___redArg(v_inst_1744_, v_q_1745_, v_k_u2080_1746_, v_n_1747_, v_c_1748_, v_s_1749_, v_a_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecG___boxed(lean_object* v_E_1752_, lean_object* v_inst_1753_, lean_object* v_q_1754_, lean_object* v_k_u2080_1755_, lean_object* v_n_1756_, lean_object* v_c_1757_, lean_object* v_s_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = lp_tree_Formalism_L2_Col_LocE_bvecG(v_E_1752_, v_inst_1753_, v_q_1754_, v_k_u2080_1755_, v_n_1756_, v_c_1757_, v_s_1758_, v_a_1759_);
lean_dec(v_a_1759_);
lean_dec(v_s_1758_);
lean_dec(v_c_1757_);
lean_dec(v_n_1756_);
lean_dec(v_k_u2080_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JG(lean_object* v_E_1761_, lean_object* v_inst_1762_, lean_object* v_P_1763_, lean_object* v_q_1764_, lean_object* v_k_u2080_1765_, lean_object* v_r_1766_, lean_object* v_t_1767_, lean_object* v_n_1768_, lean_object* v_c_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JG___boxed(lean_object* v_E_1771_, lean_object* v_inst_1772_, lean_object* v_P_1773_, lean_object* v_q_1774_, lean_object* v_k_u2080_1775_, lean_object* v_r_1776_, lean_object* v_t_1777_, lean_object* v_n_1778_, lean_object* v_c_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = lp_tree_Formalism_L2_Col_LocE_JG(v_E_1771_, v_inst_1772_, v_P_1773_, v_q_1774_, v_k_u2080_1775_, v_r_1776_, v_t_1777_, v_n_1778_, v_c_1779_);
lean_dec(v_c_1779_);
lean_dec(v_n_1778_);
lean_dec(v_t_1777_);
lean_dec(v_r_1776_);
lean_dec(v_k_u2080_1775_);
lean_dec(v_q_1774_);
lean_dec_ref(v_inst_1772_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsharp(lean_object* v_E_1781_, lean_object* v_inst_1782_, lean_object* v_P_1783_, lean_object* v_q_1784_, lean_object* v_k_u2080_1785_, lean_object* v_r_1786_, lean_object* v_t_1787_, lean_object* v_n_1788_, lean_object* v_c_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_box(0);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsharp___boxed(lean_object* v_E_1791_, lean_object* v_inst_1792_, lean_object* v_P_1793_, lean_object* v_q_1794_, lean_object* v_k_u2080_1795_, lean_object* v_r_1796_, lean_object* v_t_1797_, lean_object* v_n_1798_, lean_object* v_c_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = lp_tree_Formalism_L2_Col_LocE_JGsharp(v_E_1791_, v_inst_1792_, v_P_1793_, v_q_1794_, v_k_u2080_1795_, v_r_1796_, v_t_1797_, v_n_1798_, v_c_1799_);
lean_dec(v_c_1799_);
lean_dec(v_n_1798_);
lean_dec(v_t_1797_);
lean_dec(v_r_1796_);
lean_dec(v_k_u2080_1795_);
lean_dec(v_q_1794_);
lean_dec_ref(v_inst_1792_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bd5(lean_object* v_k_u2080_1801_, lean_object* v_rS_1802_, lean_object* v_s_1803_){
_start:
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = lean_nat_add(v_rS_1802_, v_k_u2080_1801_);
v___x_1805_ = lean_nat_dec_eq(v_s_1803_, v___x_1804_);
lean_dec(v___x_1804_);
if (v___x_1805_ == 0)
{
lean_inc(v_s_1803_);
return v_s_1803_;
}
else
{
lean_inc(v_rS_1802_);
return v_rS_1802_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bd5___boxed(lean_object* v_k_u2080_1806_, lean_object* v_rS_1807_, lean_object* v_s_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = lp_tree_Formalism_L2_Col_LocE_bd5(v_k_u2080_1806_, v_rS_1807_, v_s_1808_);
lean_dec(v_s_1808_);
lean_dec(v_rS_1807_);
lean_dec(v_k_u2080_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagS(lean_object* v_E_1810_, lean_object* v_inst_1811_, lean_object* v_P_1812_, lean_object* v_q_1813_, lean_object* v_k_u2080_1814_, lean_object* v_rS_1815_, lean_object* v_n_1816_, lean_object* v_c_1817_, lean_object* v_s_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_box(0);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_flagS___boxed(lean_object* v_E_1820_, lean_object* v_inst_1821_, lean_object* v_P_1822_, lean_object* v_q_1823_, lean_object* v_k_u2080_1824_, lean_object* v_rS_1825_, lean_object* v_n_1826_, lean_object* v_c_1827_, lean_object* v_s_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = lp_tree_Formalism_L2_Col_LocE_flagS(v_E_1820_, v_inst_1821_, v_P_1822_, v_q_1823_, v_k_u2080_1824_, v_rS_1825_, v_n_1826_, v_c_1827_, v_s_1828_);
lean_dec(v_s_1828_);
lean_dec(v_c_1827_);
lean_dec(v_n_1826_);
lean_dec(v_rS_1825_);
lean_dec(v_k_u2080_1824_);
lean_dec(v_q_1823_);
lean_dec_ref(v_inst_1821_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS___redArg(lean_object* v_inst_1830_, lean_object* v_q_1831_, lean_object* v_k_u2080_1832_, lean_object* v_rS_1833_, lean_object* v_n_1834_, lean_object* v_c_1835_, lean_object* v_s_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lp_tree_Formalism_L2_Col_symIdxInv(v_k_u2080_1832_, v_rS_1833_, v_s_1836_);
v___x_1839_ = lp_tree_Formalism_L2_Col_LocE_bvecG___redArg(v_inst_1830_, v_q_1831_, v_k_u2080_1832_, v_n_1834_, v_c_1835_, v___x_1838_, v_a_1837_);
lean_dec(v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS___redArg___boxed(lean_object* v_inst_1840_, lean_object* v_q_1841_, lean_object* v_k_u2080_1842_, lean_object* v_rS_1843_, lean_object* v_n_1844_, lean_object* v_c_1845_, lean_object* v_s_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = lp_tree_Formalism_L2_Col_LocE_bvecS___redArg(v_inst_1840_, v_q_1841_, v_k_u2080_1842_, v_rS_1843_, v_n_1844_, v_c_1845_, v_s_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec(v_s_1846_);
lean_dec(v_c_1845_);
lean_dec(v_n_1844_);
lean_dec(v_rS_1843_);
lean_dec(v_k_u2080_1842_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS(lean_object* v_E_1849_, lean_object* v_inst_1850_, lean_object* v_q_1851_, lean_object* v_k_u2080_1852_, lean_object* v_rS_1853_, lean_object* v_n_1854_, lean_object* v_c_1855_, lean_object* v_s_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = lp_tree_Formalism_L2_Col_LocE_bvecS___redArg(v_inst_1850_, v_q_1851_, v_k_u2080_1852_, v_rS_1853_, v_n_1854_, v_c_1855_, v_s_1856_, v_a_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_bvecS___boxed(lean_object* v_E_1859_, lean_object* v_inst_1860_, lean_object* v_q_1861_, lean_object* v_k_u2080_1862_, lean_object* v_rS_1863_, lean_object* v_n_1864_, lean_object* v_c_1865_, lean_object* v_s_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = lp_tree_Formalism_L2_Col_LocE_bvecS(v_E_1859_, v_inst_1860_, v_q_1861_, v_k_u2080_1862_, v_rS_1863_, v_n_1864_, v_c_1865_, v_s_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec(v_s_1866_);
lean_dec(v_c_1865_);
lean_dec(v_n_1864_);
lean_dec(v_rS_1863_);
lean_dec(v_k_u2080_1862_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsym(lean_object* v_E_1869_, lean_object* v_inst_1870_, lean_object* v_P_1871_, lean_object* v_q_1872_, lean_object* v_k_u2080_1873_, lean_object* v_rS_1874_, lean_object* v_r_1875_, lean_object* v_t_1876_, lean_object* v_n_1877_, lean_object* v_c_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_LocE_JGsym___boxed(lean_object* v_E_1880_, lean_object* v_inst_1881_, lean_object* v_P_1882_, lean_object* v_q_1883_, lean_object* v_k_u2080_1884_, lean_object* v_rS_1885_, lean_object* v_r_1886_, lean_object* v_t_1887_, lean_object* v_n_1888_, lean_object* v_c_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = lp_tree_Formalism_L2_Col_LocE_JGsym(v_E_1880_, v_inst_1881_, v_P_1882_, v_q_1883_, v_k_u2080_1884_, v_rS_1885_, v_r_1886_, v_t_1887_, v_n_1888_, v_c_1889_);
lean_dec(v_c_1889_);
lean_dec(v_n_1888_);
lean_dec(v_t_1887_);
lean_dec(v_r_1886_);
lean_dec(v_rS_1885_);
lean_dec(v_k_u2080_1884_);
lean_dec(v_q_1883_);
lean_dec_ref(v_inst_1881_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cOf(lean_object* v_R_1891_, lean_object* v_j_1892_){
_start:
{
lean_object* v_m_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_m_1893_ = lean_ctor_get(v_R_1891_, 2);
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = lean_nat_sub(v_m_1893_, v___x_1894_);
v___x_1896_ = lean_nat_sub(v___x_1895_, v_j_1892_);
lean_dec(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_cOf___boxed(lean_object* v_R_1897_, lean_object* v_j_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = lp_tree_Formalism_L2_Col_cOf(v_R_1897_, v_j_1898_);
lean_dec(v_j_1898_);
lean_dec_ref(v_R_1897_);
return v_res_1899_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_epsSg___closed__0(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = lean_nat_to_int(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_epsSg___closed__1(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_obj_once(&lp_tree_Formalism_L2_Col_epsSg___closed__0, &lp_tree_Formalism_L2_Col_epsSg___closed__0_once, _init_lp_tree_Formalism_L2_Col_epsSg___closed__0);
v___x_1903_ = lean_int_neg(v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_epsSg(void){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_obj_once(&lp_tree_Formalism_L2_Col_epsSg___closed__1, &lp_tree_Formalism_L2_Col_epsSg___closed__1_once, _init_lp_tree_Formalism_L2_Col_epsSg___closed__1);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg___lam__0(lean_object* v_toZero_1905_, lean_object* v_x_1906_){
_start:
{
lean_inc(v_toZero_1905_);
return v_toZero_1905_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg___lam__0___boxed(lean_object* v_toZero_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = lp_tree_Formalism_L2_Col_atNL___redArg___lam__0(v_toZero_1907_, v_x_1908_);
lean_dec(v_x_1908_);
lean_dec(v_toZero_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg(lean_object* v_inst_1910_, lean_object* v_N_1911_, lean_object* v_i_1912_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_nat_dec_lt(v_i_1912_, v_N_1911_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_toSemiring_1916_; lean_object* v_toAddCommMonoid_1917_; lean_object* v___x_1918_; lean_object* v_toZero_1919_; lean_object* v___f_1920_; 
lean_dec(v_i_1912_);
v___x_1914_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1910_);
v___x_1915_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1914_);
v_toSemiring_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_toSemiring_1916_);
lean_dec_ref(v___x_1915_);
v_toAddCommMonoid_1917_ = lean_ctor_get(v_toSemiring_1916_, 0);
lean_inc_ref(v_toAddCommMonoid_1917_);
lean_dec_ref(v_toSemiring_1916_);
v___x_1918_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_1917_);
lean_dec_ref(v_toAddCommMonoid_1917_);
v_toZero_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_toZero_1919_);
lean_dec_ref(v___x_1918_);
v___f_1920_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_atNL___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1920_, 0, v_toZero_1919_);
return v___f_1920_;
}
else
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_1921_, 0, lean_box(0));
lean_closure_set(v___x_1921_, 1, lean_box(0));
lean_closure_set(v___x_1921_, 2, v_i_1912_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___redArg___boxed(lean_object* v_inst_1922_, lean_object* v_N_1923_, lean_object* v_i_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = lp_tree_Formalism_L2_Col_atNL___redArg(v_inst_1922_, v_N_1923_, v_i_1924_);
lean_dec(v_N_1923_);
lean_dec_ref(v_inst_1922_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL(lean_object* v_E_1926_, lean_object* v_inst_1927_, lean_object* v_N_1928_, lean_object* v_i_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = lp_tree_Formalism_L2_Col_atNL___redArg(v_inst_1927_, v_N_1928_, v_i_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_atNL___boxed(lean_object* v_E_1931_, lean_object* v_inst_1932_, lean_object* v_N_1933_, lean_object* v_i_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = lp_tree_Formalism_L2_Col_atNL(v_E_1931_, v_inst_1932_, v_N_1933_, v_i_1934_);
lean_dec(v_N_1933_);
lean_dec_ref(v_inst_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol___redArg___lam__0(lean_object* v_toAddCommMonoid_1936_, lean_object* v___f_1937_, lean_object* v_x_u2080_1938_, lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_y_x27_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_toAddSemigroup_1944_; lean_object* v___x_265__overap_1945_; lean_object* v___x_1946_; lean_object* v___x_266__overap_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_toAddSemigroup_1944_ = lean_ctor_get(v_toAddCommMonoid_1936_, 0);
lean_inc(v_toAddSemigroup_1944_);
lean_dec_ref(v_toAddCommMonoid_1936_);
lean_inc(v___y_1942_);
v___x_265__overap_1945_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___f_1937_, v_x_u2080_1938_, v___y_1942_);
lean_inc(v___y_1943_);
v___x_1946_ = lean_apply_1(v___x_265__overap_1945_, v___y_1943_);
v___x_266__overap_1947_ = lp_mathlib_LinearMap_smulRight___redArg___lam__0(v___x_1939_, v___x_1940_, v_y_x27_1941_, v___y_1942_);
v___x_1948_ = lean_apply_1(v___x_266__overap_1947_, v___y_1943_);
v___x_1949_ = lean_apply_2(v_toAddSemigroup_1944_, v___x_1946_, v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol___redArg(lean_object* v_inst_1950_, lean_object* v_n_x27_1951_, lean_object* v_c_x27_1952_, lean_object* v_n_1953_, lean_object* v_x_u2080_1954_, lean_object* v_y_x27_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_toSemiring_1958_; lean_object* v_toAddCommMonoid_1959_; lean_object* v_toCommRing_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___f_1968_; lean_object* v___f_1969_; 
v___x_1956_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1950_);
v___x_1957_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1956_);
v_toSemiring_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_toSemiring_1958_);
lean_dec_ref(v___x_1957_);
v_toAddCommMonoid_1959_ = lean_ctor_get(v_toSemiring_1958_, 0);
lean_inc_ref(v_toAddCommMonoid_1959_);
v_toCommRing_1960_ = lean_ctor_get(v_inst_1950_, 0);
v___x_1961_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_1958_);
lean_dec_ref(v_toSemiring_1958_);
v___x_1962_ = lp_mathlib_Pi_Function_module___redArg(v___x_1961_);
lean_inc_ref(v_toCommRing_1960_);
v___x_1963_ = lp_tree_Formalism_L2_Col_Loc_inX___redArg(v_toCommRing_1960_, v_n_1953_);
lean_inc(v_c_x27_1952_);
lean_inc(v_n_x27_1951_);
v___x_1964_ = lean_alloc_closure((void*)(l_Fin_castAdd___boxed), 3, 2);
lean_closure_set(v___x_1964_, 0, v_n_x27_1951_);
lean_closure_set(v___x_1964_, 1, v_c_x27_1952_);
v___f_1965_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_funLeft___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1965_, 0, v___x_1964_);
v___x_1966_ = lean_nat_add(v_n_x27_1951_, v_c_x27_1952_);
lean_dec(v_c_x27_1952_);
v___x_1967_ = lp_tree_Formalism_L2_Col_atNL___redArg(v_inst_1950_, v___x_1966_, v_n_x27_1951_);
lean_dec(v___x_1966_);
lean_dec_ref(v_inst_1950_);
v___f_1968_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_joinCol___redArg___lam__0), 8, 6);
lean_closure_set(v___f_1968_, 0, v_toAddCommMonoid_1959_);
lean_closure_set(v___f_1968_, 1, v___f_1965_);
lean_closure_set(v___f_1968_, 2, v_x_u2080_1954_);
lean_closure_set(v___f_1968_, 3, v___x_1967_);
lean_closure_set(v___f_1968_, 4, v___x_1962_);
lean_closure_set(v___f_1968_, 5, v_y_x27_1955_);
v___f_1969_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1969_, 0, v___f_1968_);
lean_closure_set(v___f_1969_, 1, v___x_1963_);
return v___f_1969_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol(lean_object* v_E_1970_, lean_object* v_inst_1971_, lean_object* v_n_x27_1972_, lean_object* v_c_x27_1973_, lean_object* v_n_1974_, lean_object* v_c_1975_, lean_object* v_x_u2080_1976_, lean_object* v_y_x27_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lp_tree_Formalism_L2_Col_joinCol___redArg(v_inst_1971_, v_n_x27_1972_, v_c_x27_1973_, v_n_1974_, v_x_u2080_1976_, v_y_x27_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_joinCol___boxed(lean_object* v_E_1979_, lean_object* v_inst_1980_, lean_object* v_n_x27_1981_, lean_object* v_c_x27_1982_, lean_object* v_n_1983_, lean_object* v_c_1984_, lean_object* v_x_u2080_1985_, lean_object* v_y_x27_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = lp_tree_Formalism_L2_Col_joinCol(v_E_1979_, v_inst_1980_, v_n_x27_1981_, v_c_x27_1982_, v_n_1983_, v_c_1984_, v_x_u2080_1985_, v_y_x27_1986_);
lean_dec(v_c_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp___lam__0(lean_object* v_i_1988_){
_start:
{
lean_inc(v_i_1988_);
return v_i_1988_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp___lam__0___boxed(lean_object* v_i_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = lp_tree_Formalism_L2_Col_prXp___lam__0(v_i_1989_);
lean_dec(v_i_1989_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp(lean_object* v_E_1994_, lean_object* v_inst_1995_, lean_object* v_R_1996_){
_start:
{
lean_object* v___f_1997_; 
v___f_1997_ = ((lean_object*)(lp_tree_Formalism_L2_Col_prXp___closed__1));
return v___f_1997_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_prXp___boxed(lean_object* v_E_1998_, lean_object* v_inst_1999_, lean_object* v_R_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = lp_tree_Formalism_L2_Col_prXp(v_E_1998_, v_inst_1999_, v_R_2000_);
lean_dec_ref(v_R_2000_);
lean_dec_ref(v_inst_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ybCpl(lean_object* v_X_2002_, lean_object* v_Pr_2003_, lean_object* v_R_2004_, lean_object* v_W_2005_, lean_object* v_sel_2006_, lean_object* v_S_2007_, lean_object* v_mu_2008_, lean_object* v_cst_2009_, lean_object* v_L_2010_, lean_object* v_u_2011_, lean_object* v_m2_2012_, lean_object* v_b_2013_, lean_object* v_hY_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_box(0);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ybCpl___boxed(lean_object* v_X_2016_, lean_object* v_Pr_2017_, lean_object* v_R_2018_, lean_object* v_W_2019_, lean_object* v_sel_2020_, lean_object* v_S_2021_, lean_object* v_mu_2022_, lean_object* v_cst_2023_, lean_object* v_L_2024_, lean_object* v_u_2025_, lean_object* v_m2_2026_, lean_object* v_b_2027_, lean_object* v_hY_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = lp_tree_Formalism_L2_Col_ybCpl(v_X_2016_, v_Pr_2017_, v_R_2018_, v_W_2019_, v_sel_2020_, v_S_2021_, v_mu_2022_, v_cst_2023_, v_L_2024_, v_u_2025_, v_m2_2026_, v_b_2027_, v_hY_2028_);
lean_dec(v_b_2027_);
lean_dec(v_m2_2026_);
lean_dec(v_u_2025_);
lean_dec_ref(v_L_2024_);
lean_dec_ref(v_cst_2023_);
lean_dec_ref(v_mu_2022_);
lean_dec_ref(v_sel_2020_);
lean_dec_ref(v_W_2019_);
lean_dec_ref(v_R_2018_);
lean_dec_ref(v_Pr_2017_);
lean_dec_ref(v_X_2016_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toFinPl___redArg(lean_object* v_w_2030_){
_start:
{
return v_w_2030_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toFinPl(lean_object* v_K_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_w_2034_){
_start:
{
return v_w_2034_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toFinPl___boxed(lean_object* v_K_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_w_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = lp_tree_Formalism_L2_Col_toFinPl(v_K_2035_, v_inst_2036_, v_inst_2037_, v_w_2038_);
lean_dec_ref(v_inst_2036_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofFinPl___redArg(lean_object* v_w_2040_){
_start:
{
return v_w_2040_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofFinPl(lean_object* v_K_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_w_2044_){
_start:
{
return v_w_2044_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofFinPl___boxed(lean_object* v_K_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_w_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = lp_tree_Formalism_L2_Col_ofFinPl(v_K_2045_, v_inst_2046_, v_inst_2047_, v_w_2048_);
lean_dec_ref(v_inst_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___redArg___lam__0(lean_object* v_gain_2050_, lean_object* v_w_2051_, lean_object* v_F_2052_, lean_object* v_j_2053_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; 
lean_inc(v_j_2053_);
v___x_2054_ = lean_apply_2(v_gain_2050_, v_j_2053_, v_w_2051_);
v___x_2055_ = lean_apply_2(v_F_2052_, v_j_2053_, v_w_2051_);
v___f_2056_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_2056_, 0, v___x_2054_);
lean_closure_set(v___f_2056_, 1, v___x_2055_);
return v___f_2056_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___redArg___lam__1(lean_object* v_Eu_2057_, lean_object* v_w_2058_, lean_object* v_j_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_apply_2(v_Eu_2057_, v_j_2059_, v_w_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___redArg(lean_object* v_m_2061_, lean_object* v_gain_2062_, lean_object* v_F_2063_, lean_object* v_Eu_2064_, lean_object* v_w_2065_){
_start:
{
lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; 
v___f_2066_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_sgSumOf___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2066_, 0, v_gain_2062_);
lean_closure_set(v___f_2066_, 1, v_w_2065_);
lean_closure_set(v___f_2066_, 2, v_F_2063_);
v___f_2067_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_sgSumOf___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2067_, 0, v_Eu_2064_);
lean_closure_set(v___f_2067_, 1, v_w_2065_);
v___x_2068_ = lp_mathlib_Real_instAddCommMonoid;
v___x_2069_ = lp_mathlib_Nat_instLocallyFiniteOrder;
v___x_2070_ = lean_unsigned_to_nat(1u);
v___x_2071_ = lp_mathlib_Finset_Icc___redArg(v___x_2069_, v___x_2070_, v_m_2061_);
lean_inc(v___x_2071_);
v___x_2072_ = lp_mathlib_Finset_sum___redArg(v___x_2068_, v___x_2071_, v___f_2066_);
v___x_2073_ = lp_mathlib_Finset_sum___redArg(v___x_2068_, v___x_2071_, v___f_2067_);
v___f_2074_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_2074_, 0, v___x_2073_);
v___f_2075_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_2075_, 0, v___x_2072_);
lean_closure_set(v___f_2075_, 1, v___f_2074_);
return v___f_2075_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf(lean_object* v_K_2076_, lean_object* v_inst_2077_, lean_object* v_m_2078_, lean_object* v_gain_2079_, lean_object* v_F_2080_, lean_object* v_Eu_2081_, lean_object* v_w_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lp_tree_Formalism_L2_Col_sgSumOf___redArg(v_m_2078_, v_gain_2079_, v_F_2080_, v_Eu_2081_, v_w_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sgSumOf___boxed(lean_object* v_K_2084_, lean_object* v_inst_2085_, lean_object* v_m_2086_, lean_object* v_gain_2087_, lean_object* v_F_2088_, lean_object* v_Eu_2089_, lean_object* v_w_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = lp_tree_Formalism_L2_Col_sgSumOf(v_K_2084_, v_inst_2085_, v_m_2086_, v_gain_2087_, v_F_2088_, v_Eu_2089_, v_w_2090_);
lean_dec_ref(v_inst_2085_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_sumLat(lean_object* v_K_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_N_2095_, lean_object* v_n_2096_, lean_object* v_hN_2097_, lean_object* v_M_x27_2098_, lean_object* v_t_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_box(0);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Br_sumLat___boxed(lean_object* v_K_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_N_2104_, lean_object* v_n_2105_, lean_object* v_hN_2106_, lean_object* v_M_x27_2107_, lean_object* v_t_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = lp_tree_Formalism_L2_Col_Br_sumLat(v_K_2101_, v_inst_2102_, v_inst_2103_, v_N_2104_, v_n_2105_, v_hN_2106_, v_M_x27_2107_, v_t_2108_);
lean_dec(v_t_2108_);
lean_dec(v_n_2105_);
lean_dec(v_N_2104_);
lean_dec_ref(v_inst_2102_);
return v_res_2109_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ScaledRamifiedLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsSym(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefModB(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ScaledRamifiedLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefModB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Formalism_L2_Col_epsSg = _init_lp_tree_Formalism_L2_Col_epsSg();
lean_mark_persistent(lp_tree_Formalism_L2_Col_epsSg);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
