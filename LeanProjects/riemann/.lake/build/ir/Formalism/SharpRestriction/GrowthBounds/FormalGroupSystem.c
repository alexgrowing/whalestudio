// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.GrowthBounds.Imports public import Formalism.SharpRestriction.GrowthBounds.DataG public import Formalism.SharpRestriction.GrowthBounds.DataGChain public import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Int_instAddCommMonoid;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_G_Fills_Pj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lp_mathlib_Nat_log(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instLocallyFiniteOrder;
lean_object* lp_mathlib_Finset_Icc___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_NN___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_al(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_al___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_cap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_cap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Rp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Rp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_posSub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_posSub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_intK(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_intK___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(lean_object* v_k1_3_, lean_object* v_lam0_4_, lean_object* v_s_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_dec_le(v___x_9_, v_i_6_);
if (v___x_10_ == 0)
{
lean_dec(v_s_5_);
lean_dec_ref(v_lam0_4_);
goto v___jp_7_;
}
else
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_nat_add(v_k1_3_, v___x_9_);
v___x_12_ = lean_nat_dec_le(v_i_6_, v___x_11_);
lean_dec(v___x_11_);
if (v___x_12_ == 0)
{
lean_dec(v_s_5_);
lean_dec_ref(v_lam0_4_);
goto v___jp_7_;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_nat_sub(v_i_6_, v___x_9_);
v___x_14_ = lean_apply_2(v_lam0_4_, v_s_5_, v___x_13_);
return v___x_14_;
}
}
v___jp_7_:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0, &lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___boxed(lean_object* v_k1_15_, lean_object* v_lam0_16_, lean_object* v_s_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(v_k1_15_, v_lam0_16_, v_s_17_, v_i_18_);
lean_dec(v_i_18_);
lean_dec(v_k1_15_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI(lean_object* v_n_x27_20_, lean_object* v_k1_21_, lean_object* v_lam0_22_, lean_object* v_s_23_, lean_object* v_i_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(v_k1_21_, v_lam0_22_, v_s_23_, v_i_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___boxed(lean_object* v_n_x27_26_, lean_object* v_k1_27_, lean_object* v_lam0_28_, lean_object* v_s_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI(v_n_x27_26_, v_k1_27_, v_lam0_28_, v_s_29_, v_i_30_);
lean_dec(v_i_30_);
lean_dec(v_k1_27_);
lean_dec(v_n_x27_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(lean_object* v_k1_32_, lean_object* v_t_33_, lean_object* v_j_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_k1_32_, v___x_35_);
v___x_37_ = lean_nat_add(v_t_33_, v___x_35_);
v___x_38_ = lean_nat_mul(v_j_34_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_nat_add(v___x_36_, v___x_38_);
lean_dec(v___x_38_);
lean_dec(v___x_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_NN___boxed(lean_object* v_k1_40_, lean_object* v_t_41_, lean_object* v_j_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_k1_40_, v_t_41_, v_j_42_);
lean_dec(v_j_42_);
lean_dec(v_t_41_);
lean_dec(v_k1_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(lean_object* v_k1_44_, lean_object* v_t_45_, lean_object* v_lam0_46_, lean_object* v_w_47_, lean_object* v_j_48_, lean_object* v_s_49_, lean_object* v_i_50_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_69_; 
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_dec_le(v___x_53_, v_i_50_);
if (v___x_69_ == 0)
{
lean_dec_ref(v_lam0_46_);
goto v___jp_54_;
}
else
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_nat_add(v_k1_44_, v___x_53_);
v___x_71_ = lean_nat_dec_le(v_i_50_, v___x_70_);
lean_dec(v___x_70_);
if (v___x_71_ == 0)
{
lean_dec_ref(v_lam0_46_);
goto v___jp_54_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_inc(v_s_49_);
v___x_72_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(v_k1_44_, v_lam0_46_, v_s_49_, v_i_50_);
v___x_73_ = lean_apply_2(v_w_47_, v_j_48_, v_s_49_);
v___x_74_ = lean_int_add(v___x_72_, v___x_73_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
return v___x_74_;
}
}
v___jp_51_:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0, &lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0);
return v___x_52_;
}
v___jp_54_:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_nat_add(v_k1_44_, v___x_53_);
v___x_56_ = lean_nat_dec_lt(v___x_55_, v_i_50_);
lean_dec(v___x_55_);
if (v___x_56_ == 0)
{
lean_dec(v_s_49_);
lean_dec(v_j_48_);
lean_dec_ref(v_w_47_);
goto v___jp_51_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_k1_44_, v_t_45_, v_j_48_);
v___x_58_ = lean_nat_dec_le(v_i_50_, v___x_57_);
lean_dec(v___x_57_);
if (v___x_58_ == 0)
{
lean_dec(v_s_49_);
lean_dec(v_j_48_);
lean_dec_ref(v_w_47_);
goto v___jp_51_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_add(v_k1_44_, v___x_59_);
v___x_61_ = lean_nat_sub(v_i_50_, v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = lean_nat_add(v_t_45_, v___x_53_);
v___x_63_ = lean_nat_div(v___x_61_, v___x_62_);
lean_dec(v___x_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_nat_add(v___x_63_, v___x_53_);
lean_dec(v___x_63_);
lean_inc_ref(v_w_47_);
lean_inc(v_s_49_);
v___x_65_ = lean_apply_2(v_w_47_, v___x_64_, v_s_49_);
v___x_66_ = lean_int_neg(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_apply_2(v_w_47_, v_j_48_, v_s_49_);
v___x_68_ = lean_int_add(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg___boxed(lean_object* v_k1_75_, lean_object* v_t_76_, lean_object* v_lam0_77_, lean_object* v_w_78_, lean_object* v_j_79_, lean_object* v_s_80_, lean_object* v_i_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(v_k1_75_, v_t_76_, v_lam0_77_, v_w_78_, v_j_79_, v_s_80_, v_i_81_);
lean_dec(v_i_81_);
lean_dec(v_t_76_);
lean_dec(v_k1_75_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu(lean_object* v_n_x27_83_, lean_object* v_k1_84_, lean_object* v_t_85_, lean_object* v_lam0_86_, lean_object* v_w_87_, lean_object* v_j_88_, lean_object* v_s_89_, lean_object* v_i_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(v_k1_84_, v_t_85_, v_lam0_86_, v_w_87_, v_j_88_, v_s_89_, v_i_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___boxed(lean_object* v_n_x27_92_, lean_object* v_k1_93_, lean_object* v_t_94_, lean_object* v_lam0_95_, lean_object* v_w_96_, lean_object* v_j_97_, lean_object* v_s_98_, lean_object* v_i_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu(v_n_x27_92_, v_k1_93_, v_t_94_, v_lam0_95_, v_w_96_, v_j_97_, v_s_98_, v_i_99_);
lean_dec(v_i_99_);
lean_dec(v_t_94_);
lean_dec(v_k1_93_);
lean_dec(v_n_x27_92_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_al(lean_object* v_n_x27_101_, lean_object* v_k1_102_, lean_object* v_TT_103_, lean_object* v_lam0_104_, lean_object* v_s_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_106_, 0, v_n_x27_101_);
lean_inc(v_s_105_);
v___x_107_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_106_, v_s_105_, v_TT_103_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec(v_s_105_);
lean_dec_ref(v_lam0_104_);
v___x_108_ = lean_obj_once(&lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0, &lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = lean_unsigned_to_nat(1u);
lean_inc(v_s_105_);
lean_inc_ref(v_lam0_104_);
v___x_110_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(v_k1_102_, v_lam0_104_, v_s_105_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(2u);
v___x_112_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(v_k1_102_, v_lam0_104_, v_s_105_, v___x_111_);
v___x_113_ = lean_int_sub(v___x_110_, v___x_112_);
lean_dec(v___x_112_);
lean_dec(v___x_110_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_al___boxed(lean_object* v_n_x27_114_, lean_object* v_k1_115_, lean_object* v_TT_116_, lean_object* v_lam0_117_, lean_object* v_s_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_al(v_n_x27_114_, v_k1_115_, v_TT_116_, v_lam0_117_, v_s_118_);
lean_dec(v_k1_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_cap(lean_object* v_n_x27_120_, lean_object* v_k1_121_, lean_object* v_t_122_, lean_object* v_TT_123_, lean_object* v_lam0_124_, lean_object* v_w_125_, lean_object* v_j_126_, lean_object* v_s_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_128_, 0, v_n_x27_120_);
lean_inc(v_s_127_);
v___x_129_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_128_, v_s_127_, v_TT_123_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(v_k1_121_, v_t_122_, v_lam0_124_, v_w_125_, v_j_126_, v_s_127_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(2u);
v___x_133_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(v_k1_121_, v_t_122_, v_lam0_124_, v_w_125_, v_j_126_, v_s_127_, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_cap___boxed(lean_object* v_n_x27_134_, lean_object* v_k1_135_, lean_object* v_t_136_, lean_object* v_TT_137_, lean_object* v_lam0_138_, lean_object* v_w_139_, lean_object* v_j_140_, lean_object* v_s_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_cap(v_n_x27_134_, v_k1_135_, v_t_136_, v_TT_137_, v_lam0_138_, v_w_139_, v_j_140_, v_s_141_);
lean_dec(v_t_136_);
lean_dec(v_k1_135_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz___lam__0(lean_object* v_k1_143_, lean_object* v_t_144_, lean_object* v_lam0_145_, lean_object* v_w_146_, lean_object* v_j_147_, lean_object* v_s_148_, lean_object* v_i_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(v_k1_143_, v_t_144_, v_lam0_145_, v_w_146_, v_j_147_, v_s_148_, v_i_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz___lam__0___boxed(lean_object* v_k1_151_, lean_object* v_t_152_, lean_object* v_lam0_153_, lean_object* v_w_154_, lean_object* v_j_155_, lean_object* v_s_156_, lean_object* v_i_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz___lam__0(v_k1_151_, v_t_152_, v_lam0_153_, v_w_154_, v_j_155_, v_s_156_, v_i_157_);
lean_dec(v_i_157_);
lean_dec(v_t_152_);
lean_dec(v_k1_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz(lean_object* v_n_x27_159_, lean_object* v_k1_160_, lean_object* v_t_161_, lean_object* v_TT_162_, lean_object* v_lam0_163_, lean_object* v_w_164_, lean_object* v_j_165_, lean_object* v_s_166_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_inc(v_s_166_);
lean_inc(v_j_165_);
lean_inc_ref(v_lam0_163_);
lean_inc(v_t_161_);
lean_inc(v_k1_160_);
v___f_167_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz___lam__0___boxed), 7, 6);
lean_closure_set(v___f_167_, 0, v_k1_160_);
lean_closure_set(v___f_167_, 1, v_t_161_);
lean_closure_set(v___f_167_, 2, v_lam0_163_);
lean_closure_set(v___f_167_, 3, v_w_164_);
lean_closure_set(v___f_167_, 4, v_j_165_);
lean_closure_set(v___f_167_, 5, v_s_166_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_k1_160_, v_t_161_, v_j_165_);
lean_dec(v_j_165_);
lean_dec(v_t_161_);
v___x_170_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_168_, v___x_169_);
lean_dec(v___x_169_);
v___x_171_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_170_, v___f_167_);
v___x_172_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_al(v_n_x27_159_, v_k1_160_, v_TT_162_, v_lam0_163_, v_s_166_);
lean_dec(v_k1_160_);
v___x_173_ = lean_int_sub(v___x_171_, v___x_172_);
lean_dec(v___x_172_);
lean_dec(v___x_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp(lean_object* v_p_174_, lean_object* v_x_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_obj_once(&lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0, &lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg___closed__0);
v___x_178_ = lean_int_dec_le(v_x_175_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = l_Int_toNat(v_x_175_);
v___x_180_ = lp_mathlib_Nat_log(v_p_174_, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v___x_180_, v___x_181_);
lean_dec(v___x_180_);
return v___x_182_;
}
else
{
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp___boxed(lean_object* v_p_183_, lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp(v_p_183_, v_x_184_);
lean_dec(v_x_184_);
lean_dec(v_p_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__0(lean_object* v_n_x27_186_, lean_object* v_k1_187_, lean_object* v_TT_188_, lean_object* v_lam0_189_, lean_object* v_p_190_, lean_object* v_s_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_al(v_n_x27_186_, v_k1_187_, v_TT_188_, v_lam0_189_, v_s_191_);
v___x_193_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp(v_p_190_, v___x_192_);
lean_dec(v___x_192_);
v___x_194_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_193_);
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_195_, v___x_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__0___boxed(lean_object* v_n_x27_197_, lean_object* v_k1_198_, lean_object* v_TT_199_, lean_object* v_lam0_200_, lean_object* v_p_201_, lean_object* v_s_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__0(v_n_x27_197_, v_k1_198_, v_TT_199_, v_lam0_200_, v_p_201_, v_s_202_);
lean_dec(v_p_201_);
lean_dec(v_k1_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__1(lean_object* v_k1_204_, lean_object* v_t_205_, lean_object* v_j_206_, lean_object* v_n_x27_207_, lean_object* v_TT_208_, lean_object* v_lam0_209_, lean_object* v_p_210_, lean_object* v_w_211_, lean_object* v_s_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___f_228_; 
v___x_213_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_k1_204_, v_t_205_, v_j_206_);
v___x_214_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_213_);
lean_inc(v_s_212_);
lean_inc_ref(v_lam0_209_);
lean_inc(v_TT_208_);
lean_inc(v_n_x27_207_);
v___x_215_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_al(v_n_x27_207_, v_k1_204_, v_TT_208_, v_lam0_209_, v_s_212_);
v___x_216_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp(v_p_210_, v___x_215_);
lean_dec(v___x_215_);
v___x_217_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_216_);
lean_inc_ref(v___x_214_);
v___f_218_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_218_, 0, v___x_214_);
lean_closure_set(v___f_218_, 1, v___x_217_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_sub(v_j_206_, v___x_219_);
v___x_221_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_k1_204_, v_t_205_, v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_221_);
v___f_223_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_223_, 0, v___x_222_);
lean_closure_set(v___f_223_, 1, v___x_214_);
v___x_224_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lsz(v_n_x27_207_, v_k1_204_, v_t_205_, v_TT_208_, v_lam0_209_, v_w_211_, v_j_206_, v_s_212_);
v___x_225_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lgp(v_p_210_, v___x_224_);
lean_dec(v___x_224_);
v___x_226_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_225_);
v___f_227_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_227_, 0, v___f_223_);
lean_closure_set(v___f_227_, 1, v___x_226_);
v___f_228_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_228_, 0, v___f_218_);
lean_closure_set(v___f_228_, 1, v___f_227_);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__1___boxed(lean_object* v_k1_229_, lean_object* v_t_230_, lean_object* v_j_231_, lean_object* v_n_x27_232_, lean_object* v_TT_233_, lean_object* v_lam0_234_, lean_object* v_p_235_, lean_object* v_w_236_, lean_object* v_s_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__1(v_k1_229_, v_t_230_, v_j_231_, v_n_x27_232_, v_TT_233_, v_lam0_234_, v_p_235_, v_w_236_, v_s_237_);
lean_dec(v_p_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_de(lean_object* v_n_x27_239_, lean_object* v_k1_240_, lean_object* v_p_241_, lean_object* v_t_242_, lean_object* v_TT_243_, lean_object* v_lam0_244_, lean_object* v_w_245_, lean_object* v_j_246_){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___f_252_; 
lean_inc(v_p_241_);
lean_inc_ref(v_lam0_244_);
lean_inc_n(v_TT_243_, 2);
lean_inc(v_k1_240_);
lean_inc_n(v_n_x27_239_, 2);
v___f_247_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__0___boxed), 6, 5);
lean_closure_set(v___f_247_, 0, v_n_x27_239_);
lean_closure_set(v___f_247_, 1, v_k1_240_);
lean_closure_set(v___f_247_, 2, v_TT_243_);
lean_closure_set(v___f_247_, 3, v_lam0_244_);
lean_closure_set(v___f_247_, 4, v_p_241_);
v___f_248_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_de___lam__1___boxed), 9, 8);
lean_closure_set(v___f_248_, 0, v_k1_240_);
lean_closure_set(v___f_248_, 1, v_t_242_);
lean_closure_set(v___f_248_, 2, v_j_246_);
lean_closure_set(v___f_248_, 3, v_n_x27_239_);
lean_closure_set(v___f_248_, 4, v_TT_243_);
lean_closure_set(v___f_248_, 5, v_lam0_244_);
lean_closure_set(v___f_248_, 6, v_p_241_);
lean_closure_set(v___f_248_, 7, v_w_245_);
v___x_249_ = l_List_finRange(v_n_x27_239_);
v___x_250_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_249_, v___f_248_);
v___x_251_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v_TT_243_, v___f_247_);
v___f_252_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_252_, 0, v___x_250_);
lean_closure_set(v___f_252_, 1, v___x_251_);
return v___f_252_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(lean_object* v_s_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = lean_unsigned_to_nat(2u);
v___x_255_ = lean_nat_mod(v_s_253_, v___x_254_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_dec_eq(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg___boxed(lean_object* v_s_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_s_258_);
lean_dec(v_s_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1(lean_object* v_n_x27_261_, lean_object* v_s_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_s_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___boxed(lean_object* v_n_x27_264_, lean_object* v_s_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1(v_n_x27_264_, v_s_265_);
lean_dec(v_s_265_);
lean_dec(v_n_x27_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___redArg(lean_object* v_s_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_s_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___redArg___boxed(lean_object* v_s_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___redArg(v_s_270_);
lean_dec(v_s_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos(lean_object* v_n_x27_273_, lean_object* v_s_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_s_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___boxed(lean_object* v_n_x27_276_, lean_object* v_s_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos(v_n_x27_276_, v_s_277_);
lean_dec(v_s_277_);
lean_dec(v_n_x27_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__0(lean_object* v_n_x27_280_, lean_object* v_s_281_, lean_object* v_s_x27_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_nat_add(v_s_x27_282_, v_n_x27_280_);
v___x_284_ = lean_nat_sub(v___x_283_, v_s_281_);
lean_dec(v___x_283_);
v___x_285_ = lean_nat_mod(v___x_284_, v_n_x27_280_);
lean_dec(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__0___boxed(lean_object* v_n_x27_286_, lean_object* v_s_287_, lean_object* v_s_x27_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__0(v_n_x27_286_, v_s_287_, v_s_x27_288_);
lean_dec(v_s_x27_288_);
lean_dec(v_s_287_);
lean_dec(v_n_x27_286_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__1(lean_object* v_s_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_292_ = lean_unsigned_to_nat(2u);
v___x_293_ = lean_nat_mod(v_a_291_, v___x_292_);
v___x_294_ = lean_nat_mod(v_s_290_, v___x_292_);
v___x_295_ = lean_nat_dec_eq(v___x_293_, v___x_294_);
lean_dec(v___x_294_);
lean_dec(v___x_293_);
if (v___x_295_ == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 1;
return v___x_296_;
}
else
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__1___boxed(lean_object* v_s_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__1(v_s_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec(v_s_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet(lean_object* v_n_x27_302_, lean_object* v_TT_303_, lean_object* v_s_304_){
_start:
{
lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc(v_s_304_);
v___f_305_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_305_, 0, v_n_x27_302_);
lean_closure_set(v___f_305_, 1, v_s_304_);
v___f_306_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_dSet___lam__1___boxed), 2, 1);
lean_closure_set(v___f_306_, 0, v_s_304_);
v___x_307_ = lp_mathlib_Multiset_filter___redArg(v___f_306_, v_TT_303_);
v___x_308_ = lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(v___f_305_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__0(lean_object* v_w_309_, lean_object* v_j_310_, lean_object* v_s_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_apply_2(v_w_309_, v_j_310_, v_s_311_);
return v___x_312_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__1(lean_object* v_a_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_a_313_);
if (v___x_314_ == 0)
{
uint8_t v___x_315_; 
v___x_315_ = 1;
return v___x_315_;
}
else
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__1___boxed(lean_object* v_a_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__1(v_a_317_);
lean_dec(v_a_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2(lean_object* v_k1_320_, lean_object* v_lam0_321_, lean_object* v_s_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_lamI___redArg(v_k1_320_, v_lam0_321_, v_s_322_, v_a_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2___boxed(lean_object* v_k1_325_, lean_object* v_lam0_326_, lean_object* v_s_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2(v_k1_325_, v_lam0_326_, v_s_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec(v_k1_325_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__3(lean_object* v_k1_330_, lean_object* v_lam0_331_, lean_object* v_i_332_, lean_object* v_s_333_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___f_334_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2___boxed), 4, 3);
lean_closure_set(v___f_334_, 0, v_k1_330_);
lean_closure_set(v___f_334_, 1, v_lam0_331_);
lean_closure_set(v___f_334_, 2, v_s_333_);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_335_, v_i_332_);
v___x_337_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_336_, v___f_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__3___boxed(lean_object* v_k1_338_, lean_object* v_lam0_339_, lean_object* v_i_340_, lean_object* v_s_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__3(v_k1_338_, v_lam0_339_, v_i_340_, v_s_341_);
lean_dec(v_i_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1___redArg(lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
if (lean_obj_tag(v_a_343_) == 0)
{
lean_object* v___x_345_; 
v___x_345_ = l_List_reverse___redArg(v_a_344_);
return v___x_345_;
}
else
{
lean_object* v_head_346_; lean_object* v_tail_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_357_; 
v_head_346_ = lean_ctor_get(v_a_343_, 0);
v_tail_347_ = lean_ctor_get(v_a_343_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_a_343_);
if (v_isSharedCheck_357_ == 0)
{
v___x_349_ = v_a_343_;
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_tail_347_);
lean_inc(v_head_346_);
lean_dec(v_a_343_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
uint8_t v___x_351_; 
v___x_351_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_head_346_);
if (v___x_351_ == 0)
{
lean_del_object(v___x_349_);
lean_dec(v_head_346_);
v_a_343_ = v_tail_347_;
goto _start;
}
else
{
lean_object* v___x_354_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_a_344_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_head_346_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_a_344_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v_a_343_ = v_tail_347_;
v_a_344_ = v___x_354_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(lean_object* v_n_x27_358_, lean_object* v_s_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1___redArg(v_s_359_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg___boxed(lean_object* v_n_x27_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(v_n_x27_362_, v_s_363_);
lean_dec(v_n_x27_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime(lean_object* v_n_x27_366_, lean_object* v_k1_367_, lean_object* v_lam0_368_, lean_object* v_w_369_, lean_object* v_j_370_, lean_object* v_i_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___f_372_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__0), 3, 2);
lean_closure_set(v___f_372_, 0, v_w_369_);
lean_closure_set(v___f_372_, 1, v_j_370_);
v___f_373_ = ((lean_object*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___closed__0));
lean_inc(v_i_371_);
v___f_374_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__3___boxed), 4, 3);
lean_closure_set(v___f_374_, 0, v_k1_367_);
lean_closure_set(v___f_374_, 1, v_lam0_368_);
lean_closure_set(v___f_374_, 2, v_i_371_);
lean_inc(v_n_x27_366_);
v___x_375_ = l_List_finRange(v_n_x27_366_);
lean_inc(v___x_375_);
v___x_376_ = lp_mathlib_Multiset_filter___redArg(v___f_373_, v___x_375_);
v___x_377_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_376_, v___f_374_);
v___x_378_ = lean_nat_to_int(v_i_371_);
v___x_379_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(v_n_x27_366_, v___x_375_);
lean_dec(v_n_x27_366_);
v___x_380_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_379_, v___f_372_);
v___x_381_ = lean_int_mul(v___x_378_, v___x_380_);
lean_dec(v___x_380_);
lean_dec(v___x_378_);
v___x_382_ = lean_int_add(v___x_377_, v___x_381_);
lean_dec(v___x_381_);
lean_dec(v___x_377_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___redArg(lean_object* v_n_x27_383_, lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(v_n_x27_383_, v_s_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___redArg___boxed(lean_object* v_n_x27_386_, lean_object* v_s_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___redArg(v_n_x27_386_, v_s_387_);
lean_dec(v_n_x27_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0(lean_object* v_n_x27_389_, lean_object* v_p_390_, lean_object* v_s_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(v_n_x27_389_, v_s_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0___boxed(lean_object* v_n_x27_393_, lean_object* v_p_394_, lean_object* v_s_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = lp_tree_Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0(v_n_x27_393_, v_p_394_, v_s_395_);
lean_dec(v_n_x27_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0(lean_object* v_n_x27_397_, lean_object* v_p_398_, lean_object* v_s_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(v_n_x27_397_, v_s_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___boxed(lean_object* v_n_x27_401_, lean_object* v_p_402_, lean_object* v_s_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0(v_n_x27_401_, v_p_402_, v_s_403_);
lean_dec(v_n_x27_401_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1(lean_object* v_n_x27_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1___redArg(v_a_406_, v_a_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1___boxed(lean_object* v_n_x27_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0_spec__1(v_n_x27_409_, v_a_410_, v_a_411_);
lean_dec(v_n_x27_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___lam__1(lean_object* v_k1_413_, lean_object* v_lam0_414_, lean_object* v_r_415_, lean_object* v_w_416_, lean_object* v_j_417_, lean_object* v_s_418_){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_inc(v_s_418_);
lean_inc(v_k1_413_);
v___f_419_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___lam__2___boxed), 4, 3);
lean_closure_set(v___f_419_, 0, v_k1_413_);
lean_closure_set(v___f_419_, 1, v_lam0_414_);
lean_closure_set(v___f_419_, 2, v_s_418_);
lean_inc(v_r_415_);
v___x_420_ = lean_nat_to_int(v_r_415_);
v___x_421_ = lean_apply_2(v_w_416_, v_j_417_, v_s_418_);
v___x_422_ = lean_int_mul(v___x_420_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_unsigned_to_nat(2u);
v___x_424_ = lean_nat_add(v_k1_413_, v___x_423_);
v___x_425_ = lean_nat_sub(v___x_424_, v_r_415_);
lean_dec(v_r_415_);
lean_dec(v___x_424_);
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_k1_413_, v___x_426_);
lean_dec(v_k1_413_);
v___x_428_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_425_, v___x_427_);
lean_dec(v___x_427_);
lean_dec(v___x_425_);
v___x_429_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_428_, v___f_419_);
v___x_430_ = lean_int_add(v___x_422_, v___x_429_);
lean_dec(v___x_429_);
lean_dec(v___x_422_);
return v___x_430_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___closed__0(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_to_int(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ(lean_object* v_n_x27_433_, lean_object* v_k1_434_, lean_object* v_t_435_, lean_object* v_r_436_, lean_object* v_lam0_437_, lean_object* v_w_438_, lean_object* v_j_439_){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc(v_j_439_);
lean_inc(v_r_436_);
v___f_440_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___lam__1), 6, 5);
lean_closure_set(v___f_440_, 0, v_k1_434_);
lean_closure_set(v___f_440_, 1, v_lam0_437_);
lean_closure_set(v___f_440_, 2, v_r_436_);
lean_closure_set(v___f_440_, 3, v_w_438_);
lean_closure_set(v___f_440_, 4, v_j_439_);
lean_inc(v_n_x27_433_);
v___x_441_ = l_List_finRange(v_n_x27_433_);
v___x_442_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_FormalGroupSystem_Nprime_spec__0_spec__0___redArg(v_n_x27_433_, v___x_441_);
v___x_443_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_442_, v___f_440_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_shiftr(v_n_x27_433_, v___x_444_);
lean_dec(v_n_x27_433_);
v___x_446_ = lean_nat_to_int(v___x_445_);
v___x_447_ = lean_nat_to_int(v_r_436_);
v___x_448_ = lean_int_mul(v___x_446_, v___x_447_);
lean_dec(v___x_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_nat_to_int(v_j_439_);
v___x_450_ = lean_int_mul(v___x_448_, v___x_449_);
lean_dec(v___x_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_nat_to_int(v_t_435_);
v___x_452_ = lean_obj_once(&lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___closed__0, &lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___closed__0_once, _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_PrZ___closed__0);
v___x_453_ = lean_int_add(v___x_451_, v___x_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_int_mul(v___x_450_, v___x_453_);
lean_dec(v___x_453_);
lean_dec(v___x_450_);
v___x_455_ = lean_int_add(v___x_443_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_443_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Rp(lean_object* v_p_456_, lean_object* v_inst_457_, lean_object* v_K_x27_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_vp_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Rp___boxed(lean_object* v_p_463_, lean_object* v_inst_464_, lean_object* v_K_x27_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_vp_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Rp(v_p_463_, v_inst_464_, v_K_x27_465_, v_inst_466_, v_inst_467_, v_vp_468_);
lean_dec(v_vp_468_);
lean_dec_ref(v_inst_467_);
lean_dec_ref(v_inst_466_);
lean_dec(v_p_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_posSub(lean_object* v_n_x27_470_, lean_object* v_s_471_, lean_object* v_d_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_nat_mul(v_n_x27_470_, v_d_472_);
v___x_474_ = lean_nat_add(v_s_471_, v___x_473_);
lean_dec(v___x_473_);
v___x_475_ = lean_nat_sub(v___x_474_, v_d_472_);
lean_dec(v___x_474_);
v___x_476_ = lean_nat_mod(v___x_475_, v_n_x27_470_);
lean_dec(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_posSub___boxed(lean_object* v_n_x27_477_, lean_object* v_s_478_, lean_object* v_d_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_posSub(v_n_x27_477_, v_s_478_, v_d_479_);
lean_dec(v_d_479_);
lean_dec(v_s_478_);
lean_dec(v_n_x27_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___redArg(lean_object* v_X_481_){
_start:
{
lean_object* v_Fl_482_; lean_object* v_t_483_; 
v_Fl_482_ = lean_ctor_get(v_X_481_, 1);
v_t_483_ = lean_ctor_get(v_Fl_482_, 4);
lean_inc(v_t_483_);
return v_t_483_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___redArg___boxed(lean_object* v_X_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___redArg(v_X_484_);
lean_dec_ref(v_X_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t(lean_object* v_p_486_, lean_object* v_inst_487_, lean_object* v_X_488_){
_start:
{
lean_object* v_Fl_489_; lean_object* v_t_490_; 
v_Fl_489_ = lean_ctor_get(v_X_488_, 1);
v_t_490_ = lean_ctor_get(v_Fl_489_, 4);
lean_inc(v_t_490_);
return v_t_490_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t___boxed(lean_object* v_p_491_, lean_object* v_inst_492_, lean_object* v_X_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_t(v_p_491_, v_inst_492_, v_X_493_);
lean_dec_ref(v_X_493_);
lean_dec(v_p_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___redArg(lean_object* v_X_495_){
_start:
{
lean_object* v_Fl_496_; lean_object* v_mm_497_; 
v_Fl_496_ = lean_ctor_get(v_X_495_, 1);
v_mm_497_ = lean_ctor_get(v_Fl_496_, 5);
lean_inc(v_mm_497_);
return v_mm_497_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___redArg___boxed(lean_object* v_X_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___redArg(v_X_498_);
lean_dec_ref(v_X_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm(lean_object* v_p_500_, lean_object* v_inst_501_, lean_object* v_X_502_){
_start:
{
lean_object* v_Fl_503_; lean_object* v_mm_504_; 
v_Fl_503_ = lean_ctor_get(v_X_502_, 1);
v_mm_504_ = lean_ctor_get(v_Fl_503_, 5);
lean_inc(v_mm_504_);
return v_mm_504_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm___boxed(lean_object* v_p_505_, lean_object* v_inst_506_, lean_object* v_X_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_mm(v_p_505_, v_inst_506_, v_X_507_);
lean_dec_ref(v_X_507_);
lean_dec(v_p_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT___redArg(lean_object* v_X_509_, lean_object* v_v_510_){
_start:
{
lean_object* v_Fl_511_; lean_object* v_TT_512_; lean_object* v___x_513_; 
v_Fl_511_ = lean_ctor_get(v_X_509_, 1);
lean_inc_ref(v_Fl_511_);
lean_dec_ref(v_X_509_);
v_TT_512_ = lean_ctor_get(v_Fl_511_, 0);
lean_inc(v_TT_512_);
lean_dec_ref(v_Fl_511_);
v___x_513_ = lean_apply_1(v_TT_512_, v_v_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT(lean_object* v_p_514_, lean_object* v_inst_515_, lean_object* v_X_516_, lean_object* v_v_517_){
_start:
{
lean_object* v_Fl_518_; lean_object* v_TT_519_; lean_object* v___x_520_; 
v_Fl_518_ = lean_ctor_get(v_X_516_, 1);
lean_inc_ref(v_Fl_518_);
lean_dec_ref(v_X_516_);
v_TT_519_ = lean_ctor_get(v_Fl_518_, 0);
lean_inc(v_TT_519_);
lean_dec_ref(v_Fl_518_);
v___x_520_ = lean_apply_1(v_TT_519_, v_v_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT___boxed(lean_object* v_p_521_, lean_object* v_inst_522_, lean_object* v_X_523_, lean_object* v_v_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_TT(v_p_521_, v_inst_522_, v_X_523_, v_v_524_);
lean_dec(v_p_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w___redArg(lean_object* v_X_526_, lean_object* v_v_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_Fl_530_; lean_object* v_w_531_; lean_object* v___x_532_; 
v_Fl_530_ = lean_ctor_get(v_X_526_, 1);
lean_inc_ref(v_Fl_530_);
lean_dec_ref(v_X_526_);
v_w_531_ = lean_ctor_get(v_Fl_530_, 6);
lean_inc_ref(v_w_531_);
lean_dec_ref(v_Fl_530_);
v___x_532_ = lean_apply_3(v_w_531_, v_v_527_, v_a_528_, v_a_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w(lean_object* v_p_533_, lean_object* v_inst_534_, lean_object* v_X_535_, lean_object* v_v_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_Fl_539_; lean_object* v_w_540_; lean_object* v___x_541_; 
v_Fl_539_ = lean_ctor_get(v_X_535_, 1);
lean_inc_ref(v_Fl_539_);
lean_dec_ref(v_X_535_);
v_w_540_ = lean_ctor_get(v_Fl_539_, 6);
lean_inc_ref(v_w_540_);
lean_dec_ref(v_Fl_539_);
v___x_541_ = lean_apply_3(v_w_540_, v_v_536_, v_a_537_, v_a_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w___boxed(lean_object* v_p_542_, lean_object* v_inst_543_, lean_object* v_X_544_, lean_object* v_v_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w(v_p_542_, v_inst_543_, v_X_544_, v_v_545_, v_a_546_, v_a_547_);
lean_dec(v_p_542_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___redArg(lean_object* v_p_549_, lean_object* v_X_550_, lean_object* v_j_551_){
_start:
{
lean_object* v_G_552_; lean_object* v_Fl_553_; lean_object* v___x_554_; 
v_G_552_ = lean_ctor_get(v_X_550_, 0);
lean_inc_ref(v_G_552_);
v_Fl_553_ = lean_ctor_get(v_X_550_, 1);
lean_inc_ref(v_Fl_553_);
lean_dec_ref(v_X_550_);
v___x_554_ = lp_tree_Formalism_MainNotions_G_Fills_Pj(v_p_549_, v_G_552_, v_Fl_553_, v_j_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___redArg___boxed(lean_object* v_p_555_, lean_object* v_X_556_, lean_object* v_j_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___redArg(v_p_555_, v_X_556_, v_j_557_);
lean_dec(v_j_557_);
lean_dec(v_p_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj(lean_object* v_p_559_, lean_object* v_inst_560_, lean_object* v_X_561_, lean_object* v_j_562_){
_start:
{
lean_object* v_G_563_; lean_object* v_Fl_564_; lean_object* v___x_565_; 
v_G_563_ = lean_ctor_get(v_X_561_, 0);
lean_inc_ref(v_G_563_);
v_Fl_564_ = lean_ctor_get(v_X_561_, 1);
lean_inc_ref(v_Fl_564_);
lean_dec_ref(v_X_561_);
v___x_565_ = lp_tree_Formalism_MainNotions_G_Fills_Pj(v_p_559_, v_G_563_, v_Fl_564_, v_j_562_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj___boxed(lean_object* v_p_566_, lean_object* v_inst_567_, lean_object* v_X_568_, lean_object* v_j_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Pj(v_p_566_, v_inst_567_, v_X_568_, v_j_569_);
lean_dec(v_j_569_);
lean_dec(v_p_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz___redArg(lean_object* v_X_571_, lean_object* v_j_572_){
_start:
{
lean_object* v_Ch_573_; lean_object* v___x_574_; 
v_Ch_573_ = lean_ctor_get(v_X_571_, 3);
lean_inc_ref(v_Ch_573_);
lean_dec_ref(v_X_571_);
v___x_574_ = lean_apply_1(v_Ch_573_, v_j_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz(lean_object* v_p_575_, lean_object* v_inst_576_, lean_object* v_X_577_, lean_object* v_j_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz___redArg(v_X_577_, v_j_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz___boxed(lean_object* v_p_580_, lean_object* v_inst_581_, lean_object* v_X_582_, lean_object* v_j_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_Kz(v_p_580_, v_inst_581_, v_X_582_, v_j_583_);
lean_dec(v_p_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___redArg(lean_object* v_v_585_){
_start:
{
lean_inc(v_v_585_);
return v_v_585_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___redArg___boxed(lean_object* v_v_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___redArg(v_v_586_);
lean_dec(v_v_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ(lean_object* v_p_588_, lean_object* v_inst_589_, lean_object* v_X_590_, lean_object* v_j_591_, lean_object* v_v_592_){
_start:
{
lean_inc(v_v_592_);
return v_v_592_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ___boxed(lean_object* v_p_593_, lean_object* v_inst_594_, lean_object* v_X_595_, lean_object* v_j_596_, lean_object* v_v_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vJ(v_p_593_, v_inst_594_, v_X_595_, v_j_596_, v_v_597_);
lean_dec(v_v_597_);
lean_dec(v_j_596_);
lean_dec_ref(v_X_595_);
lean_dec(v_p_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___redArg(lean_object* v_v_599_){
_start:
{
lean_inc(v_v_599_);
return v_v_599_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___redArg___boxed(lean_object* v_v_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___redArg(v_v_600_);
lean_dec(v_v_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB(lean_object* v_p_602_, lean_object* v_inst_603_, lean_object* v_X_604_, lean_object* v_j_605_, lean_object* v_v_606_){
_start:
{
lean_inc(v_v_606_);
return v_v_606_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB___boxed(lean_object* v_p_607_, lean_object* v_inst_608_, lean_object* v_X_609_, lean_object* v_j_610_, lean_object* v_v_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vB(v_p_607_, v_inst_608_, v_X_609_, v_j_610_, v_v_611_);
lean_dec(v_v_611_);
lean_dec(v_j_610_);
lean_dec_ref(v_X_609_);
lean_dec(v_p_607_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_intK(lean_object* v_p_613_, lean_object* v_inst_614_, lean_object* v_X_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_intK___boxed(lean_object* v_p_617_, lean_object* v_inst_618_, lean_object* v_X_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_intK(v_p_617_, v_inst_618_, v_X_619_);
lean_dec_ref(v_X_619_);
lean_dec(v_p_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv___redArg(lean_object* v_X_621_, lean_object* v_v_622_, lean_object* v_s_623_){
_start:
{
lean_object* v_G_624_; lean_object* v_P_625_; lean_object* v_Fl_626_; lean_object* v_n_x27_627_; lean_object* v_m_628_; lean_object* v_lam0_629_; lean_object* v_TT_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_G_624_ = lean_ctor_get(v_X_621_, 0);
v_P_625_ = lean_ctor_get(v_G_624_, 3);
lean_inc_ref(v_P_625_);
v_Fl_626_ = lean_ctor_get(v_X_621_, 1);
lean_inc_ref(v_Fl_626_);
lean_dec_ref(v_X_621_);
v_n_x27_627_ = lean_ctor_get(v_P_625_, 2);
lean_inc_ref(v_n_x27_627_);
v_m_628_ = lean_ctor_get(v_P_625_, 9);
lean_inc(v_m_628_);
v_lam0_629_ = lean_ctor_get(v_P_625_, 11);
lean_inc_ref(v_lam0_629_);
lean_dec_ref(v_P_625_);
v_TT_630_ = lean_ctor_get(v_Fl_626_, 0);
lean_inc(v_TT_630_);
lean_dec_ref(v_Fl_626_);
lean_inc_n(v_v_622_, 2);
v___x_631_ = lean_apply_1(v_n_x27_627_, v_v_622_);
v___x_632_ = lean_apply_1(v_TT_630_, v_v_622_);
v___x_633_ = lean_apply_1(v_lam0_629_, v_v_622_);
v___x_634_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_al(v___x_631_, v_m_628_, v___x_632_, v___x_633_, v_s_623_);
lean_dec(v_m_628_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv(lean_object* v_p_635_, lean_object* v_inst_636_, lean_object* v_X_637_, lean_object* v_v_638_, lean_object* v_s_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv___redArg(v_X_637_, v_v_638_, v_s_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv___boxed(lean_object* v_p_641_, lean_object* v_inst_642_, lean_object* v_X_643_, lean_object* v_v_644_, lean_object* v_s_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv(v_p_641_, v_inst_642_, v_X_643_, v_v_644_, v_s_645_);
lean_dec(v_p_641_);
return v_res_646_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg___closed__0(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_nat_to_int(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg(lean_object* v_p_649_, lean_object* v_X_650_, lean_object* v_v_651_, lean_object* v_i_652_){
_start:
{
lean_object* v_G_653_; lean_object* v_Fl_654_; lean_object* v_fieldK_655_; lean_object* v_P_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_toZPow_659_; lean_object* v_toRing_660_; lean_object* v___x_661_; lean_object* v_toAddMonoidWithOne_662_; lean_object* v_toNatCast_663_; lean_object* v_n_x27_664_; lean_object* v_t_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_G_653_ = lean_ctor_get(v_X_650_, 0);
lean_inc_ref(v_G_653_);
v_Fl_654_ = lean_ctor_get(v_X_650_, 1);
lean_inc_ref(v_Fl_654_);
lean_dec_ref(v_X_650_);
v_fieldK_655_ = lean_ctor_get(v_G_653_, 1);
lean_inc_ref(v_fieldK_655_);
v_P_656_ = lean_ctor_get(v_G_653_, 3);
lean_inc_ref(v_P_656_);
lean_dec_ref(v_G_653_);
v___x_657_ = lp_mathlib_Field_toDivisionRing___redArg(v_fieldK_655_);
v___x_658_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_657_);
v_toZPow_659_ = lean_ctor_get(v___x_658_, 3);
lean_inc(v_toZPow_659_);
lean_dec_ref(v___x_658_);
v_toRing_660_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_toRing_660_);
lean_dec_ref(v___x_657_);
v___x_661_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_660_);
v_toAddMonoidWithOne_662_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_toAddMonoidWithOne_662_);
lean_dec_ref(v___x_661_);
v_toNatCast_663_ = lean_ctor_get(v_toAddMonoidWithOne_662_, 0);
lean_inc(v_toNatCast_663_);
lean_dec_ref(v_toAddMonoidWithOne_662_);
v_n_x27_664_ = lean_ctor_get(v_P_656_, 2);
lean_inc_ref(v_n_x27_664_);
lean_dec_ref(v_P_656_);
v_t_665_ = lean_ctor_get(v_Fl_654_, 4);
lean_inc(v_t_665_);
lean_dec_ref(v_Fl_654_);
v___x_666_ = lean_apply_1(v_toNatCast_663_, v_p_649_);
v___x_667_ = lean_apply_1(v_n_x27_664_, v_v_651_);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_shiftr(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_nat_to_int(v___x_669_);
v___x_671_ = lean_nat_to_int(v_t_665_);
v___x_672_ = lean_obj_once(&lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg___closed__0, &lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg___closed__0);
v___x_673_ = lean_nat_to_int(v_i_652_);
v___x_674_ = lean_int_mul(v___x_672_, v___x_673_);
lean_dec(v___x_673_);
v___x_675_ = lean_int_sub(v___x_671_, v___x_674_);
lean_dec(v___x_674_);
lean_dec(v___x_671_);
v___x_676_ = lean_int_mul(v___x_670_, v___x_675_);
lean_dec(v___x_675_);
lean_dec(v___x_670_);
v___x_677_ = lean_apply_2(v_toZPow_659_, v___x_676_, v___x_666_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh(lean_object* v_p_678_, lean_object* v_inst_679_, lean_object* v_X_680_, lean_object* v_v_681_, lean_object* v_i_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg(v_p_678_, v_X_680_, v_v_681_, v_i_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF___redArg(lean_object* v_p_684_, lean_object* v_X_685_, lean_object* v_v_686_, lean_object* v_m_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_G_689_; lean_object* v_fieldK_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_toSemiring_693_; lean_object* v___x_694_; lean_object* v_toMul_695_; lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_G_689_ = lean_ctor_get(v_X_685_, 0);
v_fieldK_690_ = lean_ctor_get(v_G_689_, 1);
v___x_691_ = lp_mathlib_Field_toSemifield___redArg(v_fieldK_690_);
v___x_692_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_691_);
v_toSemiring_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref(v_toSemiring_693_);
lean_dec_ref(v___x_692_);
v___x_694_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_693_);
v_toMul_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_toMul_695_);
lean_dec_ref(v___x_694_);
v_fst_696_ = lean_ctor_get(v_x_688_, 0);
lean_inc(v_fst_696_);
v_snd_697_ = lean_ctor_get(v_x_688_, 1);
lean_inc(v_snd_697_);
lean_dec_ref(v_x_688_);
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_fst_696_, v___x_698_);
lean_dec(v_fst_696_);
v___x_700_ = lean_apply_1(v_m_687_, v___x_699_);
v___x_701_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_qh___redArg(v_p_684_, v_X_685_, v_v_686_, v_snd_697_);
v___x_702_ = lean_apply_2(v_toMul_695_, v___x_700_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF(lean_object* v_p_703_, lean_object* v_inst_704_, lean_object* v_X_705_, lean_object* v_v_706_, lean_object* v_m_707_, lean_object* v_j_708_, lean_object* v_x_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF___redArg(v_p_703_, v_X_705_, v_v_706_, v_m_707_, v_x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF___boxed(lean_object* v_p_711_, lean_object* v_inst_712_, lean_object* v_X_713_, lean_object* v_v_714_, lean_object* v_m_715_, lean_object* v_j_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_FF(v_p_711_, v_inst_712_, v_X_713_, v_v_714_, v_m_715_, v_j_716_, v_x_717_);
lean_dec(v_j_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___redArg___lam__1(lean_object* v_X_719_, lean_object* v_v_720_, lean_object* v_s_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alv___redArg(v_X_719_, v_v_720_, v_s_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___redArg(lean_object* v_X_723_, lean_object* v_v_724_){
_start:
{
lean_object* v___x_725_; lean_object* v_Fl_726_; lean_object* v_TT_727_; lean_object* v___f_728_; lean_object* v___f_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_725_ = lp_mathlib_Int_instAddCommMonoid;
v_Fl_726_ = lean_ctor_get(v_X_723_, 1);
v_TT_727_ = lean_ctor_get(v_Fl_726_, 0);
lean_inc(v_TT_727_);
v___f_728_ = ((lean_object*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___closed__0));
lean_inc(v_v_724_);
v___f_729_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___redArg___lam__1), 3, 2);
lean_closure_set(v___f_729_, 0, v_X_723_);
lean_closure_set(v___f_729_, 1, v_v_724_);
v___x_730_ = lean_apply_1(v_TT_727_, v_v_724_);
v___x_731_ = lp_mathlib_Multiset_filter___redArg(v___f_728_, v___x_730_);
v___x_732_ = lp_mathlib_Finset_sum___redArg(v___x_725_, v___x_731_, v___f_729_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven(lean_object* v_p_733_, lean_object* v_inst_734_, lean_object* v_X_735_, lean_object* v_v_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___redArg(v_X_735_, v_v_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven___boxed(lean_object* v_p_738_, lean_object* v_inst_739_, lean_object* v_X_740_, lean_object* v_v_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_alEven(v_p_738_, v_inst_739_, v_X_740_, v_v_741_);
lean_dec(v_p_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg___lam__1(lean_object* v_Fl_743_, lean_object* v_v_744_, lean_object* v_l_745_, lean_object* v_s_746_){
_start:
{
lean_object* v_w_747_; lean_object* v___x_748_; 
v_w_747_ = lean_ctor_get(v_Fl_743_, 6);
lean_inc_ref(v_w_747_);
lean_dec_ref(v_Fl_743_);
v___x_748_ = lean_apply_3(v_w_747_, v_v_744_, v_l_745_, v_s_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg(lean_object* v_X_749_, lean_object* v_v_750_, lean_object* v_l_751_){
_start:
{
lean_object* v___x_752_; lean_object* v_G_753_; lean_object* v_P_754_; lean_object* v_Fl_755_; lean_object* v_n_x27_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_752_ = lp_mathlib_Int_instAddCommMonoid;
v_G_753_ = lean_ctor_get(v_X_749_, 0);
v_P_754_ = lean_ctor_get(v_G_753_, 3);
lean_inc_ref(v_P_754_);
v_Fl_755_ = lean_ctor_get(v_X_749_, 1);
lean_inc_ref(v_Fl_755_);
lean_dec_ref(v_X_749_);
v_n_x27_756_ = lean_ctor_get(v_P_754_, 2);
lean_inc_ref(v_n_x27_756_);
lean_dec_ref(v_P_754_);
v___f_757_ = ((lean_object*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Nprime___closed__0));
lean_inc(v_v_750_);
v___f_758_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg___lam__1), 4, 3);
lean_closure_set(v___f_758_, 0, v_Fl_755_);
lean_closure_set(v___f_758_, 1, v_v_750_);
lean_closure_set(v___f_758_, 2, v_l_751_);
v___x_759_ = lean_apply_1(v_n_x27_756_, v_v_750_);
lean_inc(v___x_759_);
v___x_760_ = l_List_finRange(v___x_759_);
lean_inc(v___x_760_);
v___x_761_ = lp_mathlib_Multiset_filter___redArg(v___f_757_, v___x_760_);
lean_inc_ref(v___f_758_);
v___x_762_ = lp_mathlib_Finset_sum___redArg(v___x_752_, v___x_761_, v___f_758_);
v___x_763_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___boxed), 2, 1);
lean_closure_set(v___x_763_, 0, v___x_759_);
v___x_764_ = lp_mathlib_Multiset_filter___redArg(v___x_763_, v___x_760_);
v___x_765_ = lp_mathlib_Finset_sum___redArg(v___x_752_, v___x_764_, v___f_758_);
v___x_766_ = lean_int_sub(v___x_762_, v___x_765_);
lean_dec(v___x_765_);
lean_dec(v___x_762_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm(lean_object* v_p_767_, lean_object* v_inst_768_, lean_object* v_X_769_, lean_object* v_v_770_, lean_object* v_l_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg(v_X_769_, v_v_770_, v_l_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___boxed(lean_object* v_p_773_, lean_object* v_inst_774_, lean_object* v_X_775_, lean_object* v_v_776_, lean_object* v_l_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm(v_p_773_, v_inst_774_, v_X_775_, v_v_776_, v_l_777_);
lean_dec(v_p_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt___redArg(lean_object* v_v_779_, lean_object* v_x_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_apply_1(v_x_780_, v_v_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt(lean_object* v_p_782_, lean_object* v_inst_783_, lean_object* v_X_784_, lean_object* v_v_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_apply_1(v_x_787_, v_v_785_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt___boxed(lean_object* v_p_789_, lean_object* v_inst_790_, lean_object* v_X_791_, lean_object* v_v_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_latAt(v_p_789_, v_inst_790_, v_X_791_, v_v_792_, v_x_793_, v_x_794_);
lean_dec(v_x_793_);
lean_dec_ref(v_X_791_);
lean_dec(v_p_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg(lean_object* v_p_796_, lean_object* v_X_797_, lean_object* v_v_798_, lean_object* v_j_799_, lean_object* v_s_800_, lean_object* v_i_801_){
_start:
{
lean_object* v_G_802_; lean_object* v_P_803_; lean_object* v_Fl_804_; lean_object* v_m_805_; lean_object* v_lam0_806_; lean_object* v_t_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_G_802_ = lean_ctor_get(v_X_797_, 0);
v_P_803_ = lean_ctor_get(v_G_802_, 3);
v_Fl_804_ = lean_ctor_get(v_X_797_, 1);
v_m_805_ = lean_ctor_get(v_P_803_, 9);
lean_inc(v_m_805_);
v_lam0_806_ = lean_ctor_get(v_P_803_, 11);
v_t_807_ = lean_ctor_get(v_Fl_804_, 4);
lean_inc(v_t_807_);
lean_inc_ref(v_lam0_806_);
lean_inc(v_v_798_);
v___x_808_ = lean_apply_1(v_lam0_806_, v_v_798_);
v___x_809_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_w___boxed), 6, 4);
lean_closure_set(v___x_809_, 0, v_p_796_);
lean_closure_set(v___x_809_, 1, lean_box(0));
lean_closure_set(v___x_809_, 2, v_X_797_);
lean_closure_set(v___x_809_, 3, v_v_798_);
v___x_810_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_nu___redArg(v_m_805_, v_t_807_, v___x_808_, v___x_809_, v_j_799_, v_s_800_, v_i_801_);
lean_dec(v_t_807_);
lean_dec(v_m_805_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg___boxed(lean_object* v_p_811_, lean_object* v_X_812_, lean_object* v_v_813_, lean_object* v_j_814_, lean_object* v_s_815_, lean_object* v_i_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg(v_p_811_, v_X_812_, v_v_813_, v_j_814_, v_s_815_, v_i_816_);
lean_dec(v_i_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv(lean_object* v_p_818_, lean_object* v_inst_819_, lean_object* v_X_820_, lean_object* v_v_821_, lean_object* v_j_822_, lean_object* v_s_823_, lean_object* v_i_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg(v_p_818_, v_X_820_, v_v_821_, v_j_822_, v_s_823_, v_i_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___boxed(lean_object* v_p_826_, lean_object* v_inst_827_, lean_object* v_X_828_, lean_object* v_v_829_, lean_object* v_j_830_, lean_object* v_s_831_, lean_object* v_i_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv(v_p_826_, v_inst_827_, v_X_828_, v_v_829_, v_j_830_, v_s_831_, v_i_832_);
lean_dec(v_i_832_);
return v_res_833_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg___lam__0(lean_object* v_c_834_, lean_object* v_p_835_, lean_object* v_X_836_, lean_object* v_v_837_, lean_object* v_j_838_, lean_object* v_s_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = lean_nat_to_int(v_c_834_);
v___x_842_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_nuv___redArg(v_p_835_, v_X_836_, v_v_837_, v_j_838_, v_s_839_, v_a_840_);
v___x_843_ = lean_int_dec_lt(v___x_841_, v___x_842_);
lean_dec(v___x_842_);
lean_dec(v___x_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg___lam__0___boxed(lean_object* v_c_844_, lean_object* v_p_845_, lean_object* v_X_846_, lean_object* v_v_847_, lean_object* v_j_848_, lean_object* v_s_849_, lean_object* v_a_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg___lam__0(v_c_844_, v_p_845_, v_X_846_, v_v_847_, v_j_848_, v_s_849_, v_a_850_);
lean_dec(v_a_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg(lean_object* v_p_853_, lean_object* v_X_854_, lean_object* v_v_855_, lean_object* v_j_856_, lean_object* v_s_857_, lean_object* v_c_858_){
_start:
{
lean_object* v___x_859_; lean_object* v_G_860_; lean_object* v_P_861_; lean_object* v_Fl_862_; lean_object* v_m_863_; lean_object* v_t_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_859_ = lp_mathlib_Nat_instLocallyFiniteOrder;
v_G_860_ = lean_ctor_get(v_X_854_, 0);
v_P_861_ = lean_ctor_get(v_G_860_, 3);
v_Fl_862_ = lean_ctor_get(v_X_854_, 1);
v_m_863_ = lean_ctor_get(v_P_861_, 9);
lean_inc(v_m_863_);
v_t_864_ = lean_ctor_get(v_Fl_862_, 4);
lean_inc(v_t_864_);
lean_inc(v_j_856_);
v___f_865_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_865_, 0, v_c_858_);
lean_closure_set(v___f_865_, 1, v_p_853_);
lean_closure_set(v___f_865_, 2, v_X_854_);
lean_closure_set(v___f_865_, 3, v_v_855_);
lean_closure_set(v___f_865_, 4, v_j_856_);
lean_closure_set(v___f_865_, 5, v_s_857_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_m_863_, v_t_864_, v_j_856_);
lean_dec(v_j_856_);
lean_dec(v_t_864_);
lean_dec(v_m_863_);
v___x_868_ = lp_mathlib_Finset_Icc___redArg(v___x_859_, v___x_866_, v___x_867_);
v___x_869_ = lp_mathlib_Multiset_filter___redArg(v___f_865_, v___x_868_);
v___x_870_ = l_List_lengthTR___redArg(v___x_869_);
lean_dec(v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt(lean_object* v_p_871_, lean_object* v_inst_872_, lean_object* v_X_873_, lean_object* v_v_874_, lean_object* v_j_875_, lean_object* v_s_876_, lean_object* v_c_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg(v_p_871_, v_X_873_, v_v_874_, v_j_875_, v_s_876_, v_c_877_);
return v___x_878_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__0(lean_object* v_I_879_, lean_object* v_v_880_, lean_object* v_s_881_, lean_object* v_c_882_, lean_object* v___x_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = lean_apply_4(v_I_879_, v_v_880_, v_s_881_, v_c_882_, v_a_884_);
v___x_886_ = lean_nat_dec_lt(v___x_885_, v___x_883_);
lean_dec(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__0___boxed(lean_object* v_I_887_, lean_object* v_v_888_, lean_object* v_s_889_, lean_object* v_c_890_, lean_object* v___x_891_, lean_object* v_a_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__0(v_I_887_, v_v_888_, v_s_889_, v_c_890_, v___x_891_, v_a_892_);
lean_dec(v___x_891_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__1(lean_object* v_I_895_, lean_object* v_v_896_, lean_object* v_s_897_, lean_object* v_c_898_, lean_object* v_i0_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
lean_inc(v_v_896_);
v___x_901_ = lean_apply_4(v_I_895_, v_v_896_, v_s_897_, v_c_898_, v_a_900_);
v___x_902_ = lean_apply_1(v_i0_899_, v_v_896_);
v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
lean_dec(v___x_902_);
lean_dec(v___x_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__1___boxed(lean_object* v_I_904_, lean_object* v_v_905_, lean_object* v_s_906_, lean_object* v_c_907_, lean_object* v_i0_908_, lean_object* v_a_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__1(v_I_904_, v_v_905_, v_s_906_, v_c_907_, v_i0_908_, v_a_909_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg(lean_object* v_p_912_, lean_object* v_X_913_, lean_object* v_j_914_, lean_object* v_I_915_, lean_object* v_i0_916_, lean_object* v_v_917_, lean_object* v_s_918_, lean_object* v_c_919_){
_start:
{
uint8_t v___x_920_; 
v___x_920_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_instDecidableIsOddPos___aux__1___redArg(v_s_918_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___y_927_; uint8_t v___x_932_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_j_914_, v___x_921_);
lean_inc(v_c_919_);
lean_inc(v_s_918_);
lean_inc_n(v_v_917_, 2);
v___x_923_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg(v_p_912_, v_X_913_, v_v_917_, v___x_922_, v_s_918_, v_c_919_);
v___x_924_ = lean_apply_1(v_i0_916_, v_v_917_);
lean_inc(v___x_924_);
v___f_925_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_925_, 0, v_I_915_);
lean_closure_set(v___f_925_, 1, v_v_917_);
lean_closure_set(v___f_925_, 2, v_s_918_);
lean_closure_set(v___f_925_, 3, v_c_919_);
lean_closure_set(v___f_925_, 4, v___x_924_);
v___x_932_ = lean_nat_dec_le(v___x_923_, v___x_924_);
if (v___x_932_ == 0)
{
v___y_927_ = v___x_924_;
goto v___jp_926_;
}
else
{
lean_dec(v___x_924_);
lean_inc(v___x_923_);
v___y_927_ = v___x_923_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_928_ = l_List_range(v___x_923_);
v___x_929_ = lp_mathlib_Multiset_filter___redArg(v___f_925_, v___x_928_);
v___x_930_ = l_List_lengthTR___redArg(v___x_929_);
lean_dec(v___x_929_);
v___x_931_ = lean_nat_sub(v___y_927_, v___x_930_);
lean_dec(v___x_930_);
lean_dec(v___y_927_);
return v___x_931_;
}
}
else
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_inc(v_c_919_);
lean_inc(v_s_918_);
lean_inc(v_v_917_);
v___f_933_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_933_, 0, v_I_915_);
lean_closure_set(v___f_933_, 1, v_v_917_);
lean_closure_set(v___f_933_, 2, v_s_918_);
lean_closure_set(v___f_933_, 3, v_c_919_);
lean_closure_set(v___f_933_, 4, v_i0_916_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_j_914_, v___x_934_);
v___x_936_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colHt___redArg(v_p_912_, v_X_913_, v_v_917_, v___x_935_, v_s_918_, v_c_919_);
v___x_937_ = l_List_range(v___x_936_);
v___x_938_ = lp_mathlib_Multiset_filter___redArg(v___f_933_, v___x_937_);
v___x_939_ = l_List_lengthTR___redArg(v___x_938_);
lean_dec(v___x_938_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg___boxed(lean_object* v_p_940_, lean_object* v_X_941_, lean_object* v_j_942_, lean_object* v_I_943_, lean_object* v_i0_944_, lean_object* v_v_945_, lean_object* v_s_946_, lean_object* v_c_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg(v_p_940_, v_X_941_, v_j_942_, v_I_943_, v_i0_944_, v_v_945_, v_s_946_, v_c_947_);
lean_dec(v_j_942_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp(lean_object* v_p_949_, lean_object* v_inst_950_, lean_object* v_X_951_, lean_object* v_j_952_, lean_object* v_I_953_, lean_object* v_i0_954_, lean_object* v_v_955_, lean_object* v_s_956_, lean_object* v_c_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___redArg(v_p_949_, v_X_951_, v_j_952_, v_I_953_, v_i0_954_, v_v_955_, v_s_956_, v_c_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp___boxed(lean_object* v_p_959_, lean_object* v_inst_960_, lean_object* v_X_961_, lean_object* v_j_962_, lean_object* v_I_963_, lean_object* v_i0_964_, lean_object* v_v_965_, lean_object* v_s_966_, lean_object* v_c_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_colExp(v_p_959_, v_inst_960_, v_X_961_, v_j_962_, v_I_963_, v_i0_964_, v_v_965_, v_s_966_, v_c_967_);
lean_dec(v_j_962_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS___redArg___lam__0(lean_object* v_Y_969_, lean_object* v_La_970_, lean_object* v_toNatCast_971_, lean_object* v_p_972_, lean_object* v_j_973_, lean_object* v_X_974_, lean_object* v_toZPow_975_, lean_object* v_v_976_){
_start:
{
lean_object* v_len_977_; lean_object* v_snd_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_len_977_ = lean_ctor_get(v_Y_969_, 10);
lean_inc_ref(v_len_977_);
lean_dec_ref(v_Y_969_);
v_snd_978_ = lean_ctor_get(v_La_970_, 1);
lean_inc(v_snd_978_);
lean_dec_ref(v_La_970_);
v___x_979_ = lean_apply_1(v_toNatCast_971_, v_p_972_);
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_add(v_j_973_, v___x_980_);
lean_inc(v_v_976_);
v___x_982_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg(v_X_974_, v_v_976_, v___x_981_);
v___x_983_ = lean_apply_3(v_len_977_, v_v_976_, v_j_973_, v_snd_978_);
v___x_984_ = lean_int_mul(v___x_982_, v___x_983_);
lean_dec(v___x_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_apply_2(v_toZPow_975_, v___x_984_, v___x_979_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS___redArg(lean_object* v_p_986_, lean_object* v_X_987_, lean_object* v_Y_988_, lean_object* v_j_989_, lean_object* v_La_990_){
_start:
{
lean_object* v_G_991_; lean_object* v_fieldK_992_; lean_object* v_P_993_; lean_object* v_toCommRing_994_; lean_object* v___x_995_; lean_object* v_nV_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_toZPow_999_; lean_object* v_toRing_1000_; lean_object* v___x_1001_; lean_object* v_toAddMonoidWithOne_1002_; lean_object* v_toNatCast_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; 
v_G_991_ = lean_ctor_get(v_X_987_, 0);
v_fieldK_992_ = lean_ctor_get(v_G_991_, 1);
v_P_993_ = lean_ctor_get(v_G_991_, 3);
v_toCommRing_994_ = lean_ctor_get(v_fieldK_992_, 0);
v___x_995_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_994_);
v_nV_996_ = lean_ctor_get(v_P_993_, 1);
lean_inc_ref(v_fieldK_992_);
v___x_997_ = lp_mathlib_Field_toDivisionRing___redArg(v_fieldK_992_);
v___x_998_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_997_);
v_toZPow_999_ = lean_ctor_get(v___x_998_, 3);
lean_inc(v_toZPow_999_);
lean_dec_ref(v___x_998_);
v_toRing_1000_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_toRing_1000_);
lean_dec_ref(v___x_997_);
v___x_1001_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_1000_);
v_toAddMonoidWithOne_1002_ = lean_ctor_get(v___x_1001_, 1);
lean_inc_ref(v_toAddMonoidWithOne_1002_);
lean_dec_ref(v___x_1001_);
v_toNatCast_1003_ = lean_ctor_get(v_toAddMonoidWithOne_1002_, 0);
lean_inc(v_toNatCast_1003_);
lean_dec_ref(v_toAddMonoidWithOne_1002_);
lean_inc(v_nV_996_);
v___x_1004_ = l_List_finRange(v_nV_996_);
v___f_1005_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS___redArg___lam__0), 8, 7);
lean_closure_set(v___f_1005_, 0, v_Y_988_);
lean_closure_set(v___f_1005_, 1, v_La_990_);
lean_closure_set(v___f_1005_, 2, v_toNatCast_1003_);
lean_closure_set(v___f_1005_, 3, v_p_986_);
lean_closure_set(v___f_1005_, 4, v_j_989_);
lean_closure_set(v___f_1005_, 5, v_X_987_);
lean_closure_set(v___f_1005_, 6, v_toZPow_999_);
v___x_1006_ = lp_mathlib_Finset_prod___redArg(v___x_995_, v___x_1004_, v___f_1005_);
lean_dec_ref(v___x_995_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS(lean_object* v_p_1007_, lean_object* v_inst_1008_, lean_object* v_X_1009_, lean_object* v_Y_1010_, lean_object* v_j_1011_, lean_object* v_La_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eS___redArg(v_p_1007_, v_X_1009_, v_Y_1010_, v_j_1011_, v_La_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg___lam__0(lean_object* v_Y_1014_, lean_object* v_La_x27_1015_, lean_object* v_toNatCast_1016_, lean_object* v_p_1017_, lean_object* v_j_1018_, lean_object* v_X_1019_, lean_object* v_toZPow_1020_, lean_object* v_v_1021_){
_start:
{
lean_object* v_len_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_len_1022_ = lean_ctor_get(v_Y_1014_, 10);
lean_inc_ref(v_len_1022_);
lean_dec_ref(v_Y_1014_);
v_snd_1023_ = lean_ctor_get(v_La_x27_1015_, 1);
lean_inc(v_snd_1023_);
lean_dec_ref(v_La_x27_1015_);
v___x_1024_ = lean_apply_1(v_toNatCast_1016_, v_p_1017_);
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_add(v_j_1018_, v___x_1025_);
lean_inc(v___x_1026_);
lean_inc(v_v_1021_);
v___x_1027_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Sys_vm___redArg(v_X_1019_, v_v_1021_, v___x_1026_);
v___x_1028_ = lean_apply_3(v_len_1022_, v_v_1021_, v___x_1026_, v_snd_1023_);
v___x_1029_ = lean_int_mul(v___x_1027_, v___x_1028_);
lean_dec(v___x_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_apply_2(v_toZPow_1020_, v___x_1029_, v___x_1024_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg___lam__0___boxed(lean_object* v_Y_1031_, lean_object* v_La_x27_1032_, lean_object* v_toNatCast_1033_, lean_object* v_p_1034_, lean_object* v_j_1035_, lean_object* v_X_1036_, lean_object* v_toZPow_1037_, lean_object* v_v_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg___lam__0(v_Y_1031_, v_La_x27_1032_, v_toNatCast_1033_, v_p_1034_, v_j_1035_, v_X_1036_, v_toZPow_1037_, v_v_1038_);
lean_dec(v_j_1035_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg(lean_object* v_p_1040_, lean_object* v_X_1041_, lean_object* v_Y_1042_, lean_object* v_j_1043_, lean_object* v_La_x27_1044_){
_start:
{
lean_object* v_G_1045_; lean_object* v_fieldK_1046_; lean_object* v_P_1047_; lean_object* v_toCommRing_1048_; lean_object* v___x_1049_; lean_object* v_nV_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_toZPow_1053_; lean_object* v_toRing_1054_; lean_object* v___x_1055_; lean_object* v_toAddMonoidWithOne_1056_; lean_object* v_toNatCast_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
v_G_1045_ = lean_ctor_get(v_X_1041_, 0);
v_fieldK_1046_ = lean_ctor_get(v_G_1045_, 1);
v_P_1047_ = lean_ctor_get(v_G_1045_, 3);
v_toCommRing_1048_ = lean_ctor_get(v_fieldK_1046_, 0);
v___x_1049_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_1048_);
v_nV_1050_ = lean_ctor_get(v_P_1047_, 1);
lean_inc_ref(v_fieldK_1046_);
v___x_1051_ = lp_mathlib_Field_toDivisionRing___redArg(v_fieldK_1046_);
v___x_1052_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_1051_);
v_toZPow_1053_ = lean_ctor_get(v___x_1052_, 3);
lean_inc(v_toZPow_1053_);
lean_dec_ref(v___x_1052_);
v_toRing_1054_ = lean_ctor_get(v___x_1051_, 0);
lean_inc_ref(v_toRing_1054_);
lean_dec_ref(v___x_1051_);
v___x_1055_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_1054_);
v_toAddMonoidWithOne_1056_ = lean_ctor_get(v___x_1055_, 1);
lean_inc_ref(v_toAddMonoidWithOne_1056_);
lean_dec_ref(v___x_1055_);
v_toNatCast_1057_ = lean_ctor_get(v_toAddMonoidWithOne_1056_, 0);
lean_inc(v_toNatCast_1057_);
lean_dec_ref(v_toAddMonoidWithOne_1056_);
lean_inc(v_nV_1050_);
v___x_1058_ = l_List_finRange(v_nV_1050_);
v___f_1059_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1059_, 0, v_Y_1042_);
lean_closure_set(v___f_1059_, 1, v_La_x27_1044_);
lean_closure_set(v___f_1059_, 2, v_toNatCast_1057_);
lean_closure_set(v___f_1059_, 3, v_p_1040_);
lean_closure_set(v___f_1059_, 4, v_j_1043_);
lean_closure_set(v___f_1059_, 5, v_X_1041_);
lean_closure_set(v___f_1059_, 6, v_toZPow_1053_);
v___x_1060_ = lp_mathlib_Finset_prod___redArg(v___x_1049_, v___x_1058_, v___f_1059_);
lean_dec_ref(v___x_1049_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT(lean_object* v_p_1061_, lean_object* v_inst_1062_, lean_object* v_X_1063_, lean_object* v_Y_1064_, lean_object* v_j_1065_, lean_object* v_La_x27_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_eT___redArg(v_p_1061_, v_X_1063_, v_Y_1064_, v_j_1065_, v_La_x27_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___redArg(lean_object* v_X_1068_, lean_object* v_Y_1069_, lean_object* v_v_1070_, lean_object* v_j_1071_, lean_object* v_L_1072_, lean_object* v_L_x27_1073_){
_start:
{
lean_object* v_G_1074_; lean_object* v_P_1075_; lean_object* v_Fl_1076_; lean_object* v_m_1077_; lean_object* v_t_1078_; lean_object* v_len_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_G_1074_ = lean_ctor_get(v_X_1068_, 0);
v_P_1075_ = lean_ctor_get(v_G_1074_, 3);
v_Fl_1076_ = lean_ctor_get(v_X_1068_, 1);
v_m_1077_ = lean_ctor_get(v_P_1075_, 9);
v_t_1078_ = lean_ctor_get(v_Fl_1076_, 4);
v_len_1079_ = lean_ctor_get(v_Y_1069_, 10);
lean_inc_ref_n(v_len_1079_, 2);
lean_dec_ref(v_Y_1069_);
v___x_1080_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_m_1077_, v_t_1078_, v_j_1071_);
v___x_1081_ = lean_nat_to_int(v___x_1080_);
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = lean_nat_add(v_j_1071_, v___x_1082_);
lean_inc(v___x_1083_);
lean_inc(v_v_1070_);
v___x_1084_ = lean_apply_3(v_len_1079_, v_v_1070_, v___x_1083_, v_L_x27_1073_);
v___x_1085_ = lean_int_mul(v___x_1081_, v___x_1084_);
lean_dec(v___x_1084_);
lean_dec(v___x_1081_);
v___x_1086_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_NN(v_m_1077_, v_t_1078_, v___x_1083_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_nat_to_int(v___x_1086_);
v___x_1088_ = lean_apply_3(v_len_1079_, v_v_1070_, v_j_1071_, v_L_1072_);
v___x_1089_ = lean_int_mul(v___x_1087_, v___x_1088_);
lean_dec(v___x_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_int_sub(v___x_1085_, v___x_1089_);
lean_dec(v___x_1089_);
lean_dec(v___x_1085_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___redArg___boxed(lean_object* v_X_1091_, lean_object* v_Y_1092_, lean_object* v_v_1093_, lean_object* v_j_1094_, lean_object* v_L_1095_, lean_object* v_L_x27_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___redArg(v_X_1091_, v_Y_1092_, v_v_1093_, v_j_1094_, v_L_1095_, v_L_x27_1096_);
lean_dec_ref(v_X_1091_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE(lean_object* v_p_1098_, lean_object* v_inst_1099_, lean_object* v_X_1100_, lean_object* v_Y_1101_, lean_object* v_v_1102_, lean_object* v_j_1103_, lean_object* v_L_1104_, lean_object* v_L_x27_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___redArg(v_X_1100_, v_Y_1101_, v_v_1102_, v_j_1103_, v_L_1104_, v_L_x27_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE___boxed(lean_object* v_p_1107_, lean_object* v_inst_1108_, lean_object* v_X_1109_, lean_object* v_Y_1110_, lean_object* v_v_1111_, lean_object* v_j_1112_, lean_object* v_L_1113_, lean_object* v_L_x27_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_Pend_volE(v_p_1107_, v_inst_1108_, v_X_1109_, v_Y_1110_, v_v_1111_, v_j_1112_, v_L_1113_, v_L_x27_1114_);
lean_dec_ref(v_X_1109_);
lean_dec(v_p_1107_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg___lam__0(lean_object* v_u_1116_, lean_object* v_l_x27_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_apply_1(v_u_1116_, v_l_x27_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg(lean_object* v_inst_1119_, lean_object* v_u_1120_, lean_object* v_m_1121_, lean_object* v_l_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_toSemiring_1126_; lean_object* v___x_1127_; lean_object* v_toMul_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_toInv_1132_; lean_object* v_toCommRing_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1123_ = lp_mathlib_Nat_instLocallyFiniteOrder;
v___x_1124_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1119_);
lean_inc_ref(v___x_1124_);
v___x_1125_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_1124_);
v_toSemiring_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_toSemiring_1126_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_1126_);
v_toMul_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_toMul_1128_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_1124_);
lean_dec_ref(v___x_1124_);
v___x_1130_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_1129_);
v___x_1131_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_1130_);
lean_dec_ref(v___x_1130_);
v_toInv_1132_ = lean_ctor_get(v___x_1131_, 1);
lean_inc(v_toInv_1132_);
lean_dec_ref(v___x_1131_);
v_toCommRing_1133_ = lean_ctor_get(v_inst_1119_, 0);
v___f_1134_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1134_, 0, v_u_1120_);
lean_inc(v_l_1122_);
v___x_1135_ = lean_apply_1(v_m_1121_, v_l_1122_);
v___x_1136_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_1133_);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_sub(v_l_1122_, v___x_1137_);
lean_dec(v_l_1122_);
v___x_1139_ = lp_mathlib_Finset_Icc___redArg(v___x_1123_, v___x_1137_, v___x_1138_);
v___x_1140_ = lp_mathlib_Finset_prod___redArg(v___x_1136_, v___x_1139_, v___f_1134_);
lean_dec_ref(v___x_1136_);
v___x_1141_ = lean_apply_1(v_toInv_1132_, v___x_1140_);
v___x_1142_ = lean_apply_2(v_toMul_1128_, v___x_1135_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg___boxed(lean_object* v_inst_1143_, lean_object* v_u_1144_, lean_object* v_m_1145_, lean_object* v_l_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg(v_inst_1143_, v_u_1144_, v_m_1145_, v_l_1146_);
lean_dec_ref(v_inst_1143_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat(lean_object* v_K_1148_, lean_object* v_inst_1149_, lean_object* v_u_1150_, lean_object* v_m_1151_, lean_object* v_l_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___redArg(v_inst_1149_, v_u_1150_, v_m_1151_, v_l_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat___boxed(lean_object* v_K_1154_, lean_object* v_inst_1155_, lean_object* v_u_1156_, lean_object* v_m_1157_, lean_object* v_l_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = lp_tree_Formalism_MainNotions_FormalGroupSystem_mHat(v_K_1154_, v_inst_1155_, v_u_1156_, v_m_1157_, v_l_1158_);
lean_dec_ref(v_inst_1155_);
return v_res_1159_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_Imports(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataGChain(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SelectionLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_FormalGroupSystem(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataGChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_SelectionLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
