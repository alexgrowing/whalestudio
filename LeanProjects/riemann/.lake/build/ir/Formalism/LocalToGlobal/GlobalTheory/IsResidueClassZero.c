// Lean compiler output
// Module: Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Divisibility.Numbers public import Formalism.LocalRingCardinality.DataErr public import Formalism.LocalRingCardinality.DataMink public import Formalism.SharpRestriction.GrowthBounds.DefsInst public import Formalism.SizeWindowBrackets.GaloisToProductIsIso public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
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
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
extern lean_object* lp_tree_Formalism_LFunctionChainParameters_LHost_sgn2;
lean_object* lp_tree_Formalism_HC_Frame_iotaInv___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_batteries_List_pwFilter___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
uint8_t lp_tree_Formalism_BasicNotions_instDecidableEqPrimeClass(uint8_t, uint8_t);
uint8_t lp_mathlib_Nat_instDecidablePredOdd(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_tree_Formalism_L2_DIV_NumDatum_bT(lean_object*, lean_object*);
lean_object* l_Rat_floor(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_DIV_NumDatum_eQ(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_wG(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lp_tree_Formalism_L2_DIV_NumDatum_uW(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_rhoVec(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_tree_Formalism_L2_DIV_NumDatum_w(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_DIV_NumDatum_aT(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_Nm(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_Nm___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_lifts(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_lifts___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_partner(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_fill(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_stepP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_Nv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_wPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_bZ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_off(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_off___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_DGamM(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_DGamM___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_lamQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_elt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_elt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_eltBar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_eltBar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__1;
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__2;
static lean_once_cell_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_wHost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_wHost___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_ttHost(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_ttHost___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aHost(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(4u);
v___x_2_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG(lean_object* v_B_3_){
_start:
{
lean_object* v_Sc_4_; lean_object* v___x_5_; lean_object* v___f_6_; 
v_Sc_4_ = lean_ctor_get(v_B_3_, 6);
lean_inc(v_Sc_4_);
lean_dec_ref(v_B_3_);
v___x_5_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG___closed__0);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_6_, 0, v___x_5_);
lean_closure_set(v___f_6_, 1, v_Sc_4_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_Nm(lean_object* v_B_7_){
_start:
{
lean_object* v_R_8_; lean_object* v_m_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_R_8_ = lean_ctor_get(v_B_7_, 0);
v_m_9_ = lean_ctor_get(v_R_8_, 2);
v___x_10_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_8_, v_m_9_);
v___x_11_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_Nm___boxed(lean_object* v_B_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_Nm(v_B_12_);
lean_dec_ref(v_B_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_lifts(lean_object* v_B_14_){
_start:
{
lean_object* v_R_15_; lean_object* v_m_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_R_15_ = lean_ctor_get(v_B_14_, 0);
v_m_16_ = lean_ctor_get(v_R_15_, 2);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_17_, v_m_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_lifts___boxed(lean_object* v_B_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_lifts(v_B_19_);
lean_dec_ref(v_B_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_partner(lean_object* v_B_21_, lean_object* v_h_22_, lean_object* v_p_23_, lean_object* v_t_24_, lean_object* v_e_25_){
_start:
{
lean_object* v_R_26_; lean_object* v_cls_27_; uint8_t v___y_29_; lean_object* v___x_39_; uint8_t v___x_40_; uint8_t v___x_41_; uint8_t v___x_42_; 
v_R_26_ = lean_ctor_get(v_B_21_, 0);
lean_inc_ref(v_R_26_);
v_cls_27_ = lean_ctor_get(v_B_21_, 4);
lean_inc_ref(v_cls_27_);
lean_dec_ref(v_B_21_);
v___x_39_ = lean_apply_1(v_cls_27_, v_p_23_);
v___x_40_ = 1;
v___x_41_ = lean_unbox(v___x_39_);
v___x_42_ = lp_tree_Formalism_BasicNotions_instDecidableEqPrimeClass(v___x_41_, v___x_40_);
if (v___x_42_ == 0)
{
v___y_29_ = v___x_42_;
goto v___jp_28_;
}
else
{
uint8_t v___x_43_; 
v___x_43_ = lp_mathlib_Nat_instDecidablePredOdd(v_e_25_);
v___y_29_ = v___x_43_;
goto v___jp_28_;
}
v___jp_28_:
{
lean_object* v_toFrame_30_; lean_object* v_grp_31_; lean_object* v_toAddMonoid_32_; lean_object* v_toAddSemigroup_33_; lean_object* v_toNSMul_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_toFrame_30_ = lean_ctor_get(v_R_26_, 0);
lean_inc_ref(v_toFrame_30_);
lean_dec_ref(v_R_26_);
v_grp_31_ = lean_ctor_get(v_toFrame_30_, 2);
lean_inc_ref(v_grp_31_);
lean_dec_ref(v_toFrame_30_);
v_toAddMonoid_32_ = lean_ctor_get(v_grp_31_, 0);
lean_inc_ref(v_toAddMonoid_32_);
lean_dec_ref(v_grp_31_);
v_toAddSemigroup_33_ = lean_ctor_get(v_toAddMonoid_32_, 0);
lean_inc(v_toAddSemigroup_33_);
v_toNSMul_34_ = lean_ctor_get(v_toAddMonoid_32_, 2);
lean_inc(v_toNSMul_34_);
lean_dec_ref(v_toAddMonoid_32_);
v___x_35_ = lean_apply_2(v_toNSMul_34_, v_e_25_, v_h_22_);
v___x_36_ = lean_apply_2(v_toAddSemigroup_33_, v_t_24_, v___x_35_);
v___x_37_ = lean_box(v___y_29_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_fill(lean_object* v_B_44_, lean_object* v_b_45_, lean_object* v_oj_46_, lean_object* v_z_47_){
_start:
{
lean_object* v___y_49_; lean_object* v_fst_54_; uint8_t v___x_55_; 
v_fst_54_ = lean_ctor_get(v_z_47_, 0);
v___x_55_ = lean_unbox(v_fst_54_);
if (v___x_55_ == 0)
{
lean_object* v_R_56_; lean_object* v_snd_57_; lean_object* v_TT_58_; lean_object* v_toFrame_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_R_56_ = lean_ctor_get(v_B_44_, 0);
lean_inc_ref(v_R_56_);
v_snd_57_ = lean_ctor_get(v_z_47_, 1);
v_TT_58_ = lean_ctor_get(v_B_44_, 5);
lean_inc(v_TT_58_);
lean_dec_ref(v_B_44_);
v_toFrame_59_ = lean_ctor_get(v_R_56_, 0);
lean_inc_ref(v_toFrame_59_);
lean_dec_ref(v_R_56_);
v___x_60_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_60_, 0, v_toFrame_59_);
lean_inc(v_snd_57_);
v___x_61_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_60_, v_snd_57_, v_TT_58_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_b_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_inc(v_snd_57_);
v___x_62_ = lean_apply_1(v_b_45_, v_snd_57_);
v___x_63_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_62_);
v___y_49_ = v___x_63_;
goto v___jp_48_;
}
}
else
{
lean_dec_ref(v_b_45_);
lean_dec_ref(v_B_44_);
goto v___jp_52_;
}
v___jp_48_:
{
lean_object* v___x_50_; lean_object* v___f_51_; 
v___x_50_ = lean_apply_1(v_oj_46_, v_z_47_);
v___f_51_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_51_, 0, v___y_49_);
lean_closure_set(v___f_51_, 1, v___x_50_);
return v___f_51_;
}
v___jp_52_:
{
lean_object* v___x_53_; 
v___x_53_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_49_ = v___x_53_;
goto v___jp_48_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_stepP(lean_object* v_B_64_, lean_object* v_h_65_, lean_object* v_p_66_){
_start:
{
lean_object* v_R_67_; lean_object* v_cls_68_; lean_object* v___x_69_; uint8_t v___x_70_; uint8_t v___x_71_; uint8_t v___x_72_; 
v_R_67_ = lean_ctor_get(v_B_64_, 0);
lean_inc_ref(v_R_67_);
v_cls_68_ = lean_ctor_get(v_B_64_, 4);
lean_inc_ref(v_cls_68_);
lean_dec_ref(v_B_64_);
v___x_69_ = lean_apply_1(v_cls_68_, v_p_66_);
v___x_70_ = 1;
v___x_71_ = lean_unbox(v___x_69_);
v___x_72_ = lp_tree_Formalism_BasicNotions_instDecidableEqPrimeClass(v___x_71_, v___x_70_);
if (v___x_72_ == 0)
{
lean_dec_ref(v_R_67_);
return v_h_65_;
}
else
{
lean_object* v_toFrame_73_; lean_object* v_grp_74_; lean_object* v_toAddMonoid_75_; lean_object* v_toNSMul_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_toFrame_73_ = lean_ctor_get(v_R_67_, 0);
lean_inc_ref(v_toFrame_73_);
lean_dec_ref(v_R_67_);
v_grp_74_ = lean_ctor_get(v_toFrame_73_, 2);
lean_inc_ref(v_grp_74_);
lean_dec_ref(v_toFrame_73_);
v_toAddMonoid_75_ = lean_ctor_get(v_grp_74_, 0);
lean_inc_ref(v_toAddMonoid_75_);
lean_dec_ref(v_grp_74_);
v_toNSMul_76_ = lean_ctor_get(v_toAddMonoid_75_, 2);
lean_inc(v_toNSMul_76_);
lean_dec_ref(v_toAddMonoid_75_);
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_apply_2(v_toNSMul_76_, v___x_77_, v_h_65_);
return v___x_78_;
}
}
}
LEAN_EXPORT uint8_t lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___lam__0(lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_nat_dec_eq(v_a_79_, v_b_80_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___lam__0(v_a_84_, v_b_85_);
lean_dec(v_b_85_);
lean_dec(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_l_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; 
v___f_90_ = ((lean_object*)(lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_91_ = lp_batteries_List_pwFilter___redArg(v___f_90_, v_l_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1(lean_object* v___x_92_, lean_object* v_s_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg(v_s_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1___boxed(lean_object* v___x_95_, lean_object* v_s_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1(v___x_95_, v_s_96_);
lean_dec_ref(v___x_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0(lean_object* v___x_98_, lean_object* v_s_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg(v_s_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0___boxed(lean_object* v___x_101_, lean_object* v_s_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0(v___x_101_, v_s_102_);
lean_dec_ref(v___x_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg(lean_object* v___x_104_, lean_object* v_f_105_, lean_object* v_s_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lp_mathlib_Multiset_map___redArg(v_f_105_, v_s_106_);
v___x_108_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg___boxed(lean_object* v___x_109_, lean_object* v_f_110_, lean_object* v_s_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg(v___x_109_, v_f_110_, v_s_111_);
lean_dec_ref(v___x_109_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps(lean_object* v_B_113_, lean_object* v_I_114_, lean_object* v_h_115_, lean_object* v_p_116_){
_start:
{
lean_object* v_R_117_; lean_object* v_toFrame_118_; lean_object* v_bs_119_; lean_object* v_ord_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_R_117_ = lean_ctor_get(v_B_113_, 0);
v_toFrame_118_ = lean_ctor_get(v_R_117_, 0);
lean_inc_ref(v_toFrame_118_);
v_bs_119_ = lean_ctor_get(v_I_114_, 0);
lean_inc_ref(v_bs_119_);
lean_dec_ref(v_I_114_);
v_ord_120_ = lean_ctor_get(v_toFrame_118_, 1);
v___x_121_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_stepP(v_B_113_, v_h_115_, v_p_116_);
v___x_122_ = lean_apply_1(v_bs_119_, v___x_121_);
lean_inc(v_ord_120_);
v___x_123_ = l_List_finRange(v_ord_120_);
v___x_124_ = lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg(v_toFrame_118_, v___x_122_, v___x_123_);
lean_dec_ref(v_toFrame_118_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0(lean_object* v___x_125_, lean_object* v_00_u03b1_126_, lean_object* v_f_127_, lean_object* v_s_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___redArg(v___x_125_, v_f_127_, v_s_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0___boxed(lean_object* v___x_130_, lean_object* v_00_u03b1_131_, lean_object* v_f_132_, lean_object* v_s_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_tree_Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0(v___x_130_, v_00_u03b1_131_, v_f_132_, v_s_133_);
lean_dec_ref(v___x_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2(lean_object* v___x_135_, lean_object* v_l_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___redArg(v_l_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v___x_138_, lean_object* v_l_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_L2_GlobalTheoryTheory_Arith_Loc_reps_spec__0_spec__0_spec__1_spec__2(v___x_138_, v_l_139_);
lean_dec_ref(v___x_138_);
return v_res_140_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn___lam__0(lean_object* v_I_141_, lean_object* v_B_142_, lean_object* v_h_143_, lean_object* v_p_144_, lean_object* v_t0_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_bs_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_bs_147_ = lean_ctor_get(v_I_141_, 0);
lean_inc_ref(v_bs_147_);
lean_dec_ref(v_I_141_);
v___x_148_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_stepP(v_B_142_, v_h_143_, v_p_144_);
v___x_149_ = lean_apply_2(v_bs_147_, v___x_148_, v_a_146_);
v___x_150_ = lean_nat_dec_eq(v___x_149_, v_t0_145_);
lean_dec(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn___lam__0___boxed(lean_object* v_I_151_, lean_object* v_B_152_, lean_object* v_h_153_, lean_object* v_p_154_, lean_object* v_t0_155_, lean_object* v_a_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn___lam__0(v_I_151_, v_B_152_, v_h_153_, v_p_154_, v_t0_155_, v_a_156_);
lean_dec(v_t0_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn(lean_object* v_B_159_, lean_object* v_I_160_, lean_object* v_h_161_, lean_object* v_p_162_, lean_object* v_t0_163_){
_start:
{
lean_object* v_TT_164_; lean_object* v___f_165_; lean_object* v___x_166_; 
v_TT_164_ = lean_ctor_get(v_B_159_, 5);
lean_inc(v_TT_164_);
v___f_165_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn___lam__0___boxed), 6, 5);
lean_closure_set(v___f_165_, 0, v_I_160_);
lean_closure_set(v___f_165_, 1, v_B_159_);
lean_closure_set(v___f_165_, 2, v_h_161_);
lean_closure_set(v___f_165_, 3, v_p_162_);
lean_closure_set(v___f_165_, 4, v_t0_163_);
v___x_166_ = lp_mathlib_Multiset_filter___redArg(v___f_165_, v_TT_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_Nv(lean_object* v_B_167_, lean_object* v_I_168_, lean_object* v_h_169_, lean_object* v_p_170_, lean_object* v_t0_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_topsOn(v_B_167_, v_I_168_, v_h_169_, v_p_170_, v_t0_171_);
v___x_173_ = l_List_lengthTR___redArg(v___x_172_);
lean_dec(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_wPos(lean_object* v_B_174_, lean_object* v_h_175_, lean_object* v_t0_176_, lean_object* v_a_177_, lean_object* v_i_178_){
_start:
{
lean_object* v_R_179_; lean_object* v_toFrame_180_; lean_object* v_grp_181_; lean_object* v_toAddMonoid_182_; lean_object* v_toAddSemigroup_183_; lean_object* v_toNSMul_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_R_179_ = lean_ctor_get(v_B_174_, 0);
lean_inc_ref(v_R_179_);
lean_dec_ref(v_B_174_);
v_toFrame_180_ = lean_ctor_get(v_R_179_, 0);
lean_inc_ref(v_toFrame_180_);
lean_dec_ref(v_R_179_);
v_grp_181_ = lean_ctor_get(v_toFrame_180_, 2);
lean_inc_ref(v_grp_181_);
lean_dec_ref(v_toFrame_180_);
v_toAddMonoid_182_ = lean_ctor_get(v_grp_181_, 0);
lean_inc_ref(v_toAddMonoid_182_);
lean_dec_ref(v_grp_181_);
v_toAddSemigroup_183_ = lean_ctor_get(v_toAddMonoid_182_, 0);
lean_inc(v_toAddSemigroup_183_);
v_toNSMul_184_ = lean_ctor_get(v_toAddMonoid_182_, 2);
lean_inc(v_toNSMul_184_);
lean_dec_ref(v_toAddMonoid_182_);
v___x_185_ = lean_apply_2(v_toNSMul_184_, v_i_178_, v_h_175_);
v___x_186_ = lean_apply_2(v_toAddSemigroup_183_, v_t0_176_, v___x_185_);
v___x_187_ = lean_apply_1(v_a_177_, v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(2u);
v___x_189_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al(lean_object* v_B_190_, lean_object* v_a_191_, lean_object* v_s_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; 
v___x_193_ = lean_apply_1(v_a_191_, v_s_192_);
v___x_194_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_193_);
v___x_195_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Loc_al___closed__0);
v___x_196_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Base_cG(v_B_190_);
v___f_197_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_197_, 0, v___x_195_);
lean_closure_set(v___f_197_, 1, v___x_196_);
v___f_198_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_198_, 0, v___f_197_);
v___f_199_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_199_, 0, v___x_194_);
lean_closure_set(v___f_199_, 1, v___f_198_);
return v___f_199_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_200_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0(lean_object* v_H_202_, lean_object* v_u_203_){
_start:
{
lean_object* v_art_204_; lean_object* v___x_205_; lean_object* v_fst_206_; lean_object* v_snd_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_235_; 
v_art_204_ = lean_ctor_get(v_H_202_, 8);
lean_inc_ref(v_art_204_);
lean_dec_ref(v_H_202_);
v___x_205_ = lean_apply_1(v_art_204_, v_u_203_);
v_fst_206_ = lean_ctor_get(v___x_205_, 0);
v_snd_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_235_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_235_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snd_207_);
lean_inc(v_fst_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_235_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_234_; 
v_fst_211_ = lean_ctor_get(v_fst_206_, 0);
v_snd_212_ = lean_ctor_get(v_fst_206_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_fst_206_);
if (v_isSharedCheck_234_ == 0)
{
v___x_214_ = v_fst_206_;
v_isShared_215_ = v_isSharedCheck_234_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_snd_212_);
lean_inc(v_fst_211_);
lean_dec(v_fst_206_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_234_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v_toFun_217_; lean_object* v___x_218_; lean_object* v_toFun_219_; lean_object* v___x_175__overap_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_177__overap_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_216_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__0);
v_toFun_217_ = lean_ctor_get(v___x_216_, 0);
v___x_218_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__1, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__1_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0___closed__1);
v_toFun_219_ = lean_ctor_get(v___x_218_, 0);
v___x_175__overap_220_ = lp_tree_Formalism_LFunctionChainParameters_LHost_sgn2;
v___x_221_ = lean_apply_1(v___x_175__overap_220_, v_snd_212_);
lean_inc_n(v_toFun_217_, 2);
v___x_222_ = lean_apply_1(v_toFun_217_, v___x_221_);
v___x_177__overap_223_ = lp_tree_Formalism_LFunctionChainParameters_LHost_sgn2;
v___x_224_ = lean_apply_1(v___x_177__overap_223_, v_fst_211_);
v___x_225_ = lean_apply_1(v_toFun_217_, v___x_224_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_225_);
lean_ctor_set(v___x_214_, 0, v___x_222_);
v___x_227_ = v___x_214_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_233_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lp_tree_Formalism_HC_Frame_iotaInv___redArg(v_snd_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_228_);
lean_ctor_set(v___x_209_, 0, v___x_227_);
v___x_230_ = v___x_209_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
lean_inc(v_toFun_219_);
v___x_231_ = lean_apply_1(v_toFun_219_, v___x_230_);
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg(lean_object* v_H_236_){
_start:
{
lean_object* v___f_237_; 
v___f_237_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0), 2, 1);
lean_closure_set(v___f_237_, 0, v_H_236_);
return v___f_237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec(lean_object* v_00_u03c6_238_, lean_object* v_H_239_){
_start:
{
lean_object* v___f_240_; 
v___f_240_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___redArg___lam__0), 2, 1);
lean_closure_set(v___f_240_, 0, v_H_239_);
return v___f_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec___boxed(lean_object* v_00_u03c6_241_, lean_object* v_H_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hostRec(v_00_u03c6_241_, v_H_242_);
lean_dec_ref(v_00_u03c6_241_);
return v_res_243_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_to_int(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ(lean_object* v_N_246_, lean_object* v_t_247_){
_start:
{
lean_object* v_R_248_; lean_object* v_TT_249_; lean_object* v_toFrame_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_R_248_ = lean_ctor_get(v_N_246_, 0);
v_TT_249_ = lean_ctor_get(v_N_246_, 4);
v_toFrame_250_ = lean_ctor_get(v_R_248_, 0);
lean_inc_ref(v_toFrame_250_);
v___x_251_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_251_, 0, v_toFrame_250_);
lean_inc(v_TT_249_);
lean_inc(v_t_247_);
v___x_252_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_251_, v_t_247_, v_TT_249_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_t_247_);
lean_dec_ref(v_N_246_);
v___x_253_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lp_tree_Formalism_L2_DIV_NumDatum_aT(v_N_246_, v_t_247_);
v___x_255_ = l_Rat_floor(v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_bZ(lean_object* v_N_256_, lean_object* v_t_257_){
_start:
{
lean_object* v_R_258_; lean_object* v_TT_259_; lean_object* v_toFrame_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_R_258_ = lean_ctor_get(v_N_256_, 0);
v_TT_259_ = lean_ctor_get(v_N_256_, 4);
v_toFrame_260_ = lean_ctor_get(v_R_258_, 0);
lean_inc_ref(v_toFrame_260_);
v___x_261_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_261_, 0, v_toFrame_260_);
lean_inc(v_TT_259_);
lean_inc(v_t_257_);
v___x_262_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_261_, v_t_257_, v_TT_259_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v_t_257_);
lean_dec_ref(v_N_256_);
v___x_263_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ___closed__0);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lp_tree_Formalism_L2_DIV_NumDatum_bT(v_N_256_, v_t_257_);
v___x_265_ = l_Rat_floor(v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_off(lean_object* v_N_266_, lean_object* v_j_267_, lean_object* v_z_268_){
_start:
{
lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_271_; lean_object* v___y_273_; uint8_t v___x_278_; 
v_fst_269_ = lean_ctor_get(v_z_268_, 0);
lean_inc(v_fst_269_);
v_snd_270_ = lean_ctor_get(v_z_268_, 1);
lean_inc(v_snd_270_);
lean_inc_ref(v_N_266_);
v___x_271_ = lp_tree_Formalism_L2_DIV_NumDatum_w(v_N_266_, v_j_267_, v_z_268_);
v___x_278_ = lean_unbox(v_fst_269_);
lean_dec(v_fst_269_);
if (v___x_278_ == 0)
{
lean_object* v_R_279_; lean_object* v_TT_280_; lean_object* v_toFrame_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_R_279_ = lean_ctor_get(v_N_266_, 0);
v_TT_280_ = lean_ctor_get(v_N_266_, 4);
v_toFrame_281_ = lean_ctor_get(v_R_279_, 0);
lean_inc_ref(v_toFrame_281_);
v___x_282_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_282_, 0, v_toFrame_281_);
lean_inc(v_TT_280_);
lean_inc(v_snd_270_);
v___x_283_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_282_, v_snd_270_, v_TT_280_);
if (v___x_283_ == 0)
{
lean_dec(v_snd_270_);
lean_dec_ref(v_N_266_);
goto v___jp_276_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_bZ(v_N_266_, v_snd_270_);
v___x_285_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_284_);
v___y_273_ = v___x_285_;
goto v___jp_272_;
}
}
else
{
lean_dec(v_snd_270_);
lean_dec_ref(v_N_266_);
goto v___jp_276_;
}
v___jp_272_:
{
lean_object* v___f_274_; lean_object* v___f_275_; 
v___f_274_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_274_, 0, v___y_273_);
v___f_275_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_275_, 0, v___x_271_);
lean_closure_set(v___f_275_, 1, v___f_274_);
return v___f_275_;
}
v___jp_276_:
{
lean_object* v___x_277_; 
v___x_277_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_273_ = v___x_277_;
goto v___jp_272_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_off___boxed(lean_object* v_N_286_, lean_object* v_j_287_, lean_object* v_z_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_off(v_N_286_, v_j_287_, v_z_288_);
lean_dec(v_j_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_DGamM(lean_object* v_N_290_){
_start:
{
lean_object* v_R_291_; lean_object* v_m_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_R_291_ = lean_ctor_get(v_N_290_, 0);
v_m_292_ = lean_ctor_get(v_R_291_, 2);
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_291_);
v___x_295_ = lean_nat_mul(v___x_293_, v___x_294_);
lean_dec(v___x_294_);
v___x_296_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_291_, v_m_292_);
v___x_297_ = lean_nat_mul(v___x_295_, v___x_296_);
lean_dec(v___x_296_);
lean_dec(v___x_295_);
v___x_298_ = lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_DGamM___boxed(lean_object* v_N_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_DGamM(v_N_299_);
lean_dec_ref(v_N_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_lamQ(lean_object* v_N_301_, lean_object* v_00_u03b4_302_, lean_object* v_z_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_R_305_; lean_object* v_k_306_; lean_object* v_t_307_; uint8_t v___x_308_; 
v_R_305_ = lean_ctor_get(v_N_301_, 0);
v_k_306_ = lean_ctor_get(v_R_305_, 1);
v_t_307_ = lean_ctor_get(v_R_305_, 3);
v___x_308_ = lean_nat_dec_lt(v_a_304_, v_k_306_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_inc_ref(v_R_305_);
lean_dec_ref(v_00_u03b4_302_);
v___x_309_ = lean_nat_sub(v_a_304_, v_k_306_);
lean_dec(v_a_304_);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_t_307_, v___x_310_);
v___x_312_ = lean_nat_div(v___x_309_, v___x_311_);
lean_dec(v___x_311_);
lean_dec(v___x_309_);
v___x_313_ = lean_nat_add(v___x_312_, v___x_310_);
lean_dec(v___x_312_);
v___x_314_ = lp_tree_Formalism_L2_DIV_NumDatum_eQ(v_N_301_, v___x_313_, v_z_303_);
v___x_315_ = lp_tree_Formalism_BasicNotions_wG(v_R_305_, v___x_314_, v___x_313_);
v___x_316_ = l_Rat_neg(v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc(v_k_306_);
lean_inc(v_a_304_);
v___x_317_ = lp_tree_Formalism_L2_DIV_NumDatum_uW(v_N_301_, v_00_u03b4_302_, v_z_303_, v_a_304_);
v___x_318_ = lp_tree_Formalism_BasicNotions_rhoVec(v_k_306_, v_a_304_);
v___x_319_ = l_Rat_sub(v___x_317_, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___lam__0(lean_object* v_x1_320_, lean_object* v_x2_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_le(v_x1_320_, v_x2_321_);
if (v___x_322_ == 0)
{
lean_inc(v_x1_320_);
return v_x1_320_;
}
else
{
lean_inc(v_x2_321_);
return v_x2_321_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___lam__0___boxed(lean_object* v_x1_323_, lean_object* v_x2_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___lam__0(v_x1_323_, v_x2_324_);
lean_dec(v_x2_324_);
lean_dec(v_x1_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg(lean_object* v_s_327_, lean_object* v_f_328_){
_start:
{
lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___f_329_ = ((lean_object*)(lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg___closed__0));
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lp_mathlib_Finset_fold___redArg(v___f_329_, v___x_330_, v_f_328_, v_s_327_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0(lean_object* v_00_u03b2_332_, lean_object* v_s_333_, lean_object* v_f_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg(v_s_333_, v_f_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__0(lean_object* v_N_336_, lean_object* v_00_u03b4_337_, lean_object* v_z_338_, lean_object* v_t_339_, lean_object* v___x_340_, lean_object* v_i_341_, lean_object* v_toFrame_342_, lean_object* v_TT_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_nat_dec_eq(v_a_344_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec(v_TT_343_);
lean_dec_ref(v_toFrame_342_);
goto v___jp_345_;
}
else
{
lean_object* v_fst_356_; uint8_t v___x_357_; 
v_fst_356_ = lean_ctor_get(v_z_338_, 0);
v___x_357_ = lean_unbox(v_fst_356_);
if (v___x_357_ == 0)
{
lean_object* v_snd_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_snd_358_ = lean_ctor_get(v_z_338_, 1);
v___x_359_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_359_, 0, v_toFrame_342_);
lean_inc(v_snd_358_);
v___x_360_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_359_, v_snd_358_, v_TT_343_);
if (v___x_360_ == 0)
{
goto v___jp_345_;
}
else
{
lean_dec(v_a_344_);
lean_dec_ref(v_z_338_);
lean_dec_ref(v_00_u03b4_337_);
lean_dec_ref(v_N_336_);
return v___x_354_;
}
}
else
{
lean_dec(v_TT_343_);
lean_dec_ref(v_toFrame_342_);
goto v___jp_345_;
}
}
v___jp_345_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_346_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_lamQ(v_N_336_, v_00_u03b4_337_, v_z_338_, v_a_344_);
v___x_347_ = l_Rat_floor(v___x_346_);
v___x_348_ = lean_nat_add(v_t_339_, v___x_340_);
v___x_349_ = lean_nat_mul(v_i_341_, v___x_348_);
lean_dec(v___x_348_);
v___x_350_ = lean_nat_shiftr(v___x_349_, v___x_340_);
lean_dec(v___x_349_);
v___x_351_ = lean_nat_to_int(v___x_350_);
v___x_352_ = lean_int_sub(v___x_347_, v___x_351_);
lean_dec(v___x_351_);
lean_dec(v___x_347_);
v___x_353_ = lean_nat_abs(v___x_352_);
lean_dec(v___x_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__0___boxed(lean_object* v_N_361_, lean_object* v_00_u03b4_362_, lean_object* v_z_363_, lean_object* v_t_364_, lean_object* v___x_365_, lean_object* v_i_366_, lean_object* v_toFrame_367_, lean_object* v_TT_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__0(v_N_361_, v_00_u03b4_362_, v_z_363_, v_t_364_, v___x_365_, v_i_366_, v_toFrame_367_, v_TT_368_, v_a_369_);
lean_dec(v_i_366_);
lean_dec(v___x_365_);
lean_dec(v_t_364_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__1(lean_object* v_N_371_, lean_object* v_00_u03b4_372_, lean_object* v_z_373_, lean_object* v_t_374_, lean_object* v___x_375_, lean_object* v_toFrame_376_, lean_object* v_TT_377_, lean_object* v_R_378_, lean_object* v_i_379_){
_start:
{
lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc(v_i_379_);
v___f_380_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__0___boxed), 9, 8);
lean_closure_set(v___f_380_, 0, v_N_371_);
lean_closure_set(v___f_380_, 1, v_00_u03b4_372_);
lean_closure_set(v___f_380_, 2, v_z_373_);
lean_closure_set(v___f_380_, 3, v_t_374_);
lean_closure_set(v___f_380_, 4, v___x_375_);
lean_closure_set(v___f_380_, 5, v_i_379_);
lean_closure_set(v___f_380_, 6, v_toFrame_376_);
lean_closure_set(v___f_380_, 7, v_TT_377_);
v___x_381_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_378_, v_i_379_);
lean_dec(v_i_379_);
v___x_382_ = l_List_finRange(v___x_381_);
v___x_383_ = lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg(v___x_382_, v___f_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__1___boxed(lean_object* v_N_384_, lean_object* v_00_u03b4_385_, lean_object* v_z_386_, lean_object* v_t_387_, lean_object* v___x_388_, lean_object* v_toFrame_389_, lean_object* v_TT_390_, lean_object* v_R_391_, lean_object* v_i_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__1(v_N_384_, v_00_u03b4_385_, v_z_386_, v_t_387_, v___x_388_, v_toFrame_389_, v_TT_390_, v_R_391_, v_i_392_);
lean_dec_ref(v_R_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt(lean_object* v_N_394_, lean_object* v_00_u03b4_395_, lean_object* v_z_396_){
_start:
{
lean_object* v_R_397_; lean_object* v_TT_398_; lean_object* v_toFrame_399_; lean_object* v_m_400_; lean_object* v_t_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_R_397_ = lean_ctor_get(v_N_394_, 0);
lean_inc_ref(v_R_397_);
v_TT_398_ = lean_ctor_get(v_N_394_, 4);
lean_inc(v_TT_398_);
v_toFrame_399_ = lean_ctor_get(v_R_397_, 0);
lean_inc_ref(v_toFrame_399_);
v_m_400_ = lean_ctor_get(v_R_397_, 2);
lean_inc(v_m_400_);
v_t_401_ = lean_ctor_get(v_R_397_, 3);
lean_inc(v_t_401_);
v___x_402_ = lean_unsigned_to_nat(1u);
v___f_403_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_Wt___lam__1___boxed), 9, 8);
lean_closure_set(v___f_403_, 0, v_N_394_);
lean_closure_set(v___f_403_, 1, v_00_u03b4_395_);
lean_closure_set(v___f_403_, 2, v_z_396_);
lean_closure_set(v___f_403_, 3, v_t_401_);
lean_closure_set(v___f_403_, 4, v___x_402_);
lean_closure_set(v___f_403_, 5, v_toFrame_399_);
lean_closure_set(v___f_403_, 6, v_TT_398_);
lean_closure_set(v___f_403_, 7, v_R_397_);
v___x_404_ = lean_nat_add(v_m_400_, v___x_402_);
lean_dec(v_m_400_);
v___x_405_ = l_List_range(v___x_404_);
v___x_406_ = lp_tree_Finset_sup___at___00Formalism_L2_GlobalTheoryTheory_Arith_Wt_spec__0___redArg(v___x_405_, v___f_403_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_elt___redArg(lean_object* v_inst_407_, lean_object* v_sd_408_, lean_object* v_00_u03c0_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_toDiv_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_toSemiring_415_; lean_object* v___x_416_; lean_object* v_toMul_417_; lean_object* v_toAdd_418_; lean_object* v_toRing_419_; lean_object* v___x_420_; lean_object* v_toAddMonoidWithOne_421_; lean_object* v_toIntCast_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v_toNatCast_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc_ref(v_inst_407_);
v___x_410_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_407_);
v___x_411_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_410_);
v_toDiv_412_ = lean_ctor_get(v___x_411_, 2);
lean_inc(v_toDiv_412_);
lean_dec_ref(v___x_411_);
v___x_413_ = lp_mathlib_Field_toSemifield___redArg(v_inst_407_);
lean_dec_ref(v_inst_407_);
v___x_414_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_413_);
v_toSemiring_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_toSemiring_415_);
lean_dec_ref(v___x_414_);
v___x_416_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_415_);
v_toMul_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_toMul_417_);
v_toAdd_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_toAdd_418_);
lean_dec_ref(v___x_416_);
v_toRing_419_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_toRing_419_);
lean_dec_ref(v___x_410_);
v___x_420_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_419_);
v_toAddMonoidWithOne_421_ = lean_ctor_get(v___x_420_, 1);
lean_inc_ref(v_toAddMonoidWithOne_421_);
v_toIntCast_422_ = lean_ctor_get(v___x_420_, 0);
lean_inc_n(v_toIntCast_422_, 2);
lean_dec_ref(v___x_420_);
v_fst_423_ = lean_ctor_get(v_00_u03c0_409_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v_00_u03c0_409_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v_00_u03c0_409_);
v_toNatCast_425_ = lean_ctor_get(v_toAddMonoidWithOne_421_, 0);
lean_inc(v_toNatCast_425_);
lean_dec_ref(v_toAddMonoidWithOne_421_);
v___x_426_ = lean_apply_1(v_toIntCast_422_, v_fst_423_);
v___x_427_ = lean_apply_1(v_toIntCast_422_, v_snd_424_);
v___x_428_ = lean_apply_2(v_toMul_417_, v___x_427_, v_sd_408_);
v___x_429_ = lean_apply_2(v_toAdd_418_, v___x_426_, v___x_428_);
v___x_430_ = lean_unsigned_to_nat(2u);
v___x_431_ = lean_apply_1(v_toNatCast_425_, v___x_430_);
v___x_432_ = lean_apply_2(v_toDiv_412_, v___x_429_, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_elt(lean_object* v_K_433_, lean_object* v_inst_434_, lean_object* v_sd_435_, lean_object* v_00_u03c0_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_elt___redArg(v_inst_434_, v_sd_435_, v_00_u03c0_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_eltBar___redArg(lean_object* v_inst_438_, lean_object* v_sd_439_, lean_object* v_00_u03c0_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_toDiv_443_; lean_object* v_toRing_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_toSub_447_; lean_object* v_toIntCast_448_; lean_object* v_toAddMonoidWithOne_449_; lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_toSemiring_454_; lean_object* v___x_455_; lean_object* v_toMul_456_; lean_object* v_toNatCast_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_inc_ref(v_inst_438_);
v___x_441_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_438_);
v___x_442_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_441_);
v_toDiv_443_ = lean_ctor_get(v___x_442_, 2);
lean_inc(v_toDiv_443_);
lean_dec_ref(v___x_442_);
v_toRing_444_ = lean_ctor_get(v___x_441_, 0);
lean_inc_ref(v_toRing_444_);
lean_dec_ref(v___x_441_);
v___x_445_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_444_);
v___x_446_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_445_);
v_toSub_447_ = lean_ctor_get(v___x_446_, 2);
lean_inc(v_toSub_447_);
lean_dec_ref(v___x_446_);
v_toIntCast_448_ = lean_ctor_get(v___x_445_, 0);
lean_inc_n(v_toIntCast_448_, 2);
v_toAddMonoidWithOne_449_ = lean_ctor_get(v___x_445_, 1);
lean_inc_ref(v_toAddMonoidWithOne_449_);
lean_dec_ref(v___x_445_);
v_fst_450_ = lean_ctor_get(v_00_u03c0_440_, 0);
lean_inc(v_fst_450_);
v_snd_451_ = lean_ctor_get(v_00_u03c0_440_, 1);
lean_inc(v_snd_451_);
lean_dec_ref(v_00_u03c0_440_);
v___x_452_ = lp_mathlib_Field_toSemifield___redArg(v_inst_438_);
lean_dec_ref(v_inst_438_);
v___x_453_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_452_);
v_toSemiring_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc_ref(v_toSemiring_454_);
lean_dec_ref(v___x_453_);
v___x_455_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_454_);
v_toMul_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_toMul_456_);
lean_dec_ref(v___x_455_);
v_toNatCast_457_ = lean_ctor_get(v_toAddMonoidWithOne_449_, 0);
lean_inc(v_toNatCast_457_);
lean_dec_ref(v_toAddMonoidWithOne_449_);
v___x_458_ = lean_apply_1(v_toIntCast_448_, v_fst_450_);
v___x_459_ = lean_apply_1(v_toIntCast_448_, v_snd_451_);
v___x_460_ = lean_apply_2(v_toMul_456_, v___x_459_, v_sd_439_);
v___x_461_ = lean_apply_2(v_toSub_447_, v___x_458_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(2u);
v___x_463_ = lean_apply_1(v_toNatCast_457_, v___x_462_);
v___x_464_ = lean_apply_2(v_toDiv_443_, v___x_461_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_eltBar(lean_object* v_K_465_, lean_object* v_inst_466_, lean_object* v_sd_467_, lean_object* v_00_u03c0_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_eltBar___redArg(v_inst_466_, v_sd_467_, v_00_u03c0_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs___redArg(lean_object* v_w_470_){
_start:
{
return v_w_470_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs(lean_object* v_K_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_w_474_){
_start:
{
return v_w_474_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs___boxed(lean_object* v_K_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_w_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_hs(v_K_475_, v_inst_476_, v_inst_477_, v_w_478_);
lean_dec_ref(v_inst_476_);
return v_res_479_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = lp_mathlib_ZMod_instField___redArg(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0);
v___x_483_ = lp_mathlib_Field_toSemifield___redArg(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__2(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__1, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__1_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__1);
v___x_485_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__0);
v___x_487_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg(lean_object* v_z_488_){
_start:
{
lean_object* v___x_489_; lean_object* v_toSemiring_490_; lean_object* v___x_491_; lean_object* v_toZero_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_516_; 
v___x_489_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__2, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__2_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__2);
v_toSemiring_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_ref(v_toSemiring_490_);
v___x_491_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_490_);
v_toZero_492_ = lean_ctor_get(v___x_491_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_491_, 0);
lean_dec(v_unused_517_);
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_516_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_toZero_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_516_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_515_; 
v_fst_496_ = lean_ctor_get(v_z_488_, 0);
v_snd_497_ = lean_ctor_get(v_z_488_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_z_488_);
if (v_isSharedCheck_515_ == 0)
{
v___x_499_ = v_z_488_;
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_inc(v_fst_496_);
lean_dec(v_z_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___y_502_; uint8_t v___x_509_; 
v___x_509_ = lean_unbox(v_fst_496_);
lean_dec(v_fst_496_);
if (v___x_509_ == 0)
{
lean_inc(v_toZero_492_);
v___y_502_ = v_toZero_492_;
goto v___jp_501_;
}
else
{
lean_object* v___x_510_; lean_object* v_toRing_511_; lean_object* v___x_512_; lean_object* v_toAddMonoidWithOne_513_; lean_object* v_toOne_514_; 
v___x_510_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3);
v_toRing_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc_ref(v_toRing_511_);
v___x_512_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_511_);
v_toAddMonoidWithOne_513_ = lean_ctor_get(v___x_512_, 1);
lean_inc_ref(v_toAddMonoidWithOne_513_);
lean_dec_ref(v___x_512_);
v_toOne_514_ = lean_ctor_get(v_toAddMonoidWithOne_513_, 2);
lean_inc(v_toOne_514_);
lean_dec_ref(v_toAddMonoidWithOne_513_);
v___y_502_ = v_toOne_514_;
goto v___jp_501_;
}
v___jp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___y_502_);
lean_ctor_set(v___x_499_, 0, v_toZero_492_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_toZero_492_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___y_502_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v_snd_497_);
lean_ctor_set(v___x_494_, 0, v___x_504_);
v___x_506_ = v___x_494_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_snd_497_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost(lean_object* v_N_518_, lean_object* v_z_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg(v_z_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___boxed(lean_object* v_N_521_, lean_object* v_z_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost(v_N_521_, v_z_522_);
lean_dec_ref(v_N_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf___redArg(lean_object* v_00_u03c1_524_){
_start:
{
lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v_snd_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_542_; 
v_fst_525_ = lean_ctor_get(v_00_u03c1_524_, 0);
lean_inc(v_fst_525_);
v_snd_526_ = lean_ctor_get(v_00_u03c1_524_, 1);
lean_inc(v_snd_526_);
lean_dec_ref(v_00_u03c1_524_);
v_snd_527_ = lean_ctor_get(v_fst_525_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_fst_525_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_fst_525_, 0);
lean_dec(v_unused_543_);
v___x_529_ = v_fst_525_;
v_isShared_530_ = v_isSharedCheck_542_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snd_527_);
lean_dec(v_fst_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_542_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_toRing_533_; lean_object* v___x_534_; lean_object* v_toAddMonoidWithOne_535_; lean_object* v_toOne_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_531_ = lean_unsigned_to_nat(2u);
v___x_532_ = lean_obj_once(&lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3, &lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3_once, _init_lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_plHost___redArg___closed__3);
v_toRing_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_ref(v_toRing_533_);
v___x_534_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_533_);
v_toAddMonoidWithOne_535_ = lean_ctor_get(v___x_534_, 1);
lean_inc_ref(v_toAddMonoidWithOne_535_);
lean_dec_ref(v___x_534_);
v_toOne_536_ = lean_ctor_get(v_toAddMonoidWithOne_535_, 2);
lean_inc(v_toOne_536_);
lean_dec_ref(v_toAddMonoidWithOne_535_);
v___x_537_ = lp_mathlib_ZMod_decidableEq(v___x_531_, v_snd_527_, v_toOne_536_);
lean_dec(v_toOne_536_);
lean_dec(v_snd_527_);
v___x_538_ = lean_box(v___x_537_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_snd_526_);
lean_ctor_set(v___x_529_, 0, v___x_538_);
v___x_540_ = v___x_529_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_snd_526_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf(lean_object* v_N_544_, lean_object* v_00_u03c1_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf___redArg(v_00_u03c1_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf___boxed(lean_object* v_N_547_, lean_object* v_00_u03c1_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf(v_N_547_, v_00_u03c1_548_);
lean_dec_ref(v_N_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_wHost(lean_object* v_N_550_, lean_object* v_j_551_, lean_object* v_00_u03c1_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_j_551_, v___x_553_);
v___x_555_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_rplOf___redArg(v_00_u03c1_552_);
v___x_556_ = lp_tree_Formalism_L2_DIV_NumDatum_w(v_N_550_, v___x_554_, v___x_555_);
lean_dec(v___x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_wHost___boxed(lean_object* v_N_557_, lean_object* v_j_558_, lean_object* v_00_u03c1_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_wHost(v_N_557_, v_j_558_, v_00_u03c1_559_);
lean_dec(v_j_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_ttHost(lean_object* v_N_561_){
_start:
{
lean_object* v_TT_562_; 
v_TT_562_ = lean_ctor_get(v_N_561_, 4);
lean_inc(v_TT_562_);
return v_TT_562_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_ttHost___boxed(lean_object* v_N_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_ttHost(v_N_563_);
lean_dec_ref(v_N_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aHost(lean_object* v_N_565_, lean_object* v_t_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lp_tree_Formalism_L2_GlobalTheoryTheory_Arith_aZ(v_N_565_, v_t_566_);
v___x_568_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_567_);
return v___x_568_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Numbers(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataErr(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataMink(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DefsInst(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_GaloisToProductIsIso(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Numbers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataMink(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DefsInst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_GaloisToProductIsIso(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
