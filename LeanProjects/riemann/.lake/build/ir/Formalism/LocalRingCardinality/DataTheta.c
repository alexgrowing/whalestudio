// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataTheta
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SatakeDualWeyl.Statement public import Formalism.FormalDegreeBessel.StatementG
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
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_UG_Jpq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_QuantumDeterminants_herm___at___00Formalism_QuantumDeterminants_Tz_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* lp_mathlib_Equiv_sumComm(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_prodSumDistrib(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_abs___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__2(lean_object*);
lean_object* lp_mathlib_Equiv_sumProdDistrib(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_instDecidableEqRat___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_bind___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lp_mathlib_Nat_instDecidablePredEven(lean_object*);
lean_object* lp_mathlib_Equiv_sumSumSumComm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_sumCongr___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_finProdFinEquiv___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_finSumFinEquiv(lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
uint8_t lp_mathlib_Nat_instDecidablePredOdd(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_Jm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_Jm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_Eab___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_Eab___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_Eab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___lam__0(lean_object*);
static const lean_closure_object lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_conjR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_wtSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_wtSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_hwSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_hwSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_linePos___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_linePos___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_linePos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_linePos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__0;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__2;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__3;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__4;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__5;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_homog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_homog___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_blattner(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoSq(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_normSq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_normSq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_shiftNu___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_shiftNu(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_shiftNu___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_degW___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_degW(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_cPair(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00List_mapTR_loop___at___00Formalism_BasicNotions_TH_pad_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_TH_pad_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_TH_pad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_TH_pad___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_pad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_BasicNotions_TH_block_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_TH_block_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_tree_Formalism_BasicNotions_TH_block___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_tree_Formalism_BasicNotions_TH_block___closed__0 = (const lean_object*)&lp_tree_Formalism_BasicNotions_TH_block___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_block(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lamA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lamA_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lamM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_GrpData_covU___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_GrpData_covU(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_GrpData_covU___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_block___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_block(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__3(lean_object*);
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___closed__0 = (const lean_object*)&lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___closed__0_value;
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__5(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___closed__0 = (const lean_object*)&lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___closed__0_value;
LEAN_EXPORT uint8_t lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___closed__0 = (const lean_object*)&lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Xpar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Xpar___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Xpar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_sphOff(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_sphOff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_cuspD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_cuspD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_typeX(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_parOf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_parOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_petY(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_dnY___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_dnY(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_Jm(lean_object* v_p_1_, lean_object* v_q_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lp_tree_Formalism_UG_Jpq(v_p_1_, v_q_2_, v_a_3_, v_a_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_Jm___boxed(lean_object* v_p_6_, lean_object* v_q_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_BasicNotions_TH_Jm(v_p_6_, v_q_7_, v_a_8_, v_a_9_);
lean_dec(v_q_7_);
lean_dec(v_p_6_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter___redArg(lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_, lean_object* v_h__3_15_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_dec(v_h__2_14_);
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v_val_16_; lean_object* v_val_17_; lean_object* v___x_18_; 
lean_dec(v_h__3_15_);
v_val_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_16_);
lean_dec_ref_known(v_x_11_, 1);
v_val_17_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_x_12_, 1);
v___x_18_ = lean_apply_2(v_h__1_13_, v_val_16_, v_val_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; 
lean_dec(v_h__1_13_);
v___x_19_ = lean_apply_4(v_h__3_15_, v_x_11_, v_x_12_, lean_box(0), lean_box(0));
return v___x_19_;
}
}
else
{
lean_dec(v_h__1_13_);
if (lean_obj_tag(v_x_12_) == 1)
{
lean_object* v_val_20_; lean_object* v_val_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_15_);
v_val_20_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v_x_11_, 1);
v_val_21_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_x_12_, 1);
v___x_22_ = lean_apply_2(v_h__2_14_, v_val_20_, v_val_21_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; 
lean_dec(v_h__2_14_);
v___x_23_ = lean_apply_4(v_h__3_15_, v_x_11_, v_x_12_, lean_box(0), lean_box(0));
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter(lean_object* v_p_24_, lean_object* v_q_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_dec(v_h__2_30_);
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v_val_32_; lean_object* v_val_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_31_);
v_val_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_val_32_);
lean_dec_ref_known(v_x_27_, 1);
v_val_33_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_val_33_);
lean_dec_ref_known(v_x_28_, 1);
v___x_34_ = lean_apply_2(v_h__1_29_, v_val_32_, v_val_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
lean_dec(v_h__1_29_);
v___x_35_ = lean_apply_4(v_h__3_31_, v_x_27_, v_x_28_, lean_box(0), lean_box(0));
return v___x_35_;
}
}
else
{
lean_dec(v_h__1_29_);
if (lean_obj_tag(v_x_28_) == 1)
{
lean_object* v_val_36_; lean_object* v_val_37_; lean_object* v___x_38_; 
lean_dec(v_h__3_31_);
v_val_36_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v_x_27_, 1);
v_val_37_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v_x_28_, 1);
v___x_38_ = lean_apply_2(v_h__2_30_, v_val_36_, v_val_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
lean_dec(v_h__2_30_);
v___x_39_ = lean_apply_4(v_h__3_31_, v_x_27_, v_x_28_, lean_box(0), lean_box(0));
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter___boxed(lean_object* v_p_40_, lean_object* v_q_41_, lean_object* v_motive_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_sameBlock_match__1_splitter(v_p_40_, v_q_41_, v_motive_42_, v_x_43_, v_x_44_, v_h__1_45_, v_h__2_46_, v_h__3_47_);
lean_dec(v_q_41_);
lean_dec(v_p_40_);
return v_res_48_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(lean_object* v_a_49_, lean_object* v_b_50_){
_start:
{
uint8_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = 1;
v___x_52_ = 0;
if (lean_obj_tag(v_a_49_) == 0)
{
if (lean_obj_tag(v_b_50_) == 0)
{
return v___x_51_;
}
else
{
return v___x_52_;
}
}
else
{
if (lean_obj_tag(v_b_50_) == 0)
{
return v___x_52_;
}
else
{
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg___boxed(lean_object* v_a_53_, lean_object* v_b_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(v_a_53_, v_b_54_);
lean_dec_ref(v_b_54_);
lean_dec_ref(v_a_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock(lean_object* v_p_57_, lean_object* v_q_58_, lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(v_a_59_, v_b_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___boxed(lean_object* v_p_62_, lean_object* v_q_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock(v_p_62_, v_q_63_, v_a_64_, v_b_65_);
lean_dec_ref(v_b_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_q_63_);
lean_dec(v_p_62_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__0(lean_object* v_p_68_, lean_object* v_q_69_, lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_72_, 0, v_p_68_);
v___x_73_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_73_, 0, v_q_69_);
v___x_74_ = l_instDecidableEqSum_decEq___redArg(v___x_72_, v___x_73_, v_a_70_, v_b_71_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__0___boxed(lean_object* v_p_75_, lean_object* v_q_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__0(v_p_75_, v_q_76_, v_a_77_, v_b_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
static lean_object* _init_lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_82_ = lp_mathlib_Complex_ofReal(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1(lean_object* v___f_83_, lean_object* v_j_84_, lean_object* v_i_85_, lean_object* v_a_86_, lean_object* v_i_x27_87_, lean_object* v_j_x27_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
lean_inc_ref(v___f_83_);
v___x_89_ = lean_apply_2(v___f_83_, v_j_84_, v_j_x27_88_);
v___x_90_ = lean_apply_2(v___f_83_, v_i_85_, v_i_x27_87_);
v___x_91_ = lean_unbox(v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0, &lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0_once, _init_lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0);
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = lean_unbox(v___x_89_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0, &lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0_once, _init_lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___closed__0);
return v___x_94_;
}
else
{
lean_inc_ref(v_a_86_);
return v_a_86_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___boxed(lean_object* v___f_95_, lean_object* v_j_96_, lean_object* v_i_97_, lean_object* v_a_98_, lean_object* v_i_x27_99_, lean_object* v_j_x27_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1(v___f_95_, v_j_96_, v_i_97_, v_a_98_, v_i_x27_99_, v_j_x27_100_);
lean_dec_ref(v_a_98_);
return v_res_101_;
}
}
static lean_object* _init_lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___closed__0(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0(lean_object* v_p_103_, lean_object* v_q_104_, lean_object* v_i_105_, lean_object* v_j_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; lean_object* v_toFun_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; 
v___x_110_ = lean_obj_once(&lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___closed__0, &lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___closed__0_once, _init_lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___closed__0);
v_toFun_111_ = lean_ctor_get(v___x_110_, 0);
v___f_112_ = lean_alloc_closure((void*)(lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__0___boxed), 4, 2);
lean_closure_set(v___f_112_, 0, v_p_103_);
lean_closure_set(v___f_112_, 1, v_q_104_);
v___f_113_ = lean_alloc_closure((void*)(lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_113_, 0, v___f_112_);
lean_closure_set(v___f_113_, 1, v_j_106_);
lean_closure_set(v___f_113_, 2, v_i_105_);
lean_closure_set(v___f_113_, 3, v_a_107_);
lean_inc(v_toFun_111_);
v___x_114_ = lean_apply_3(v_toFun_111_, v___f_113_, v_a_108_, v_a_109_);
return v___x_114_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_Eab___closed__0(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_116_ = lp_mathlib_Complex_ofReal(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_Eab(lean_object* v_p_117_, lean_object* v_q_118_, lean_object* v_a_119_, lean_object* v_b_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_Eab___closed__0, &lp_tree_Formalism_BasicNotions_TH_Eab___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_Eab___closed__0);
v___x_124_ = lp_tree_Matrix_single___at___00Formalism_BasicNotions_TH_Eab_spec__0(v_p_117_, v_q_118_, v_a_119_, v_b_120_, v___x_123_, v_a_121_, v_a_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___lam__0(lean_object* v_z_125_){
_start:
{
lean_object* v_re_126_; lean_object* v_im_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_135_; 
v_re_126_ = lean_ctor_get(v_z_125_, 0);
v_im_127_ = lean_ctor_get(v_z_125_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_z_125_);
if (v_isSharedCheck_135_ == 0)
{
v___x_129_ = v_z_125_;
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_im_127_);
lean_inc(v_re_126_);
lean_dec(v_z_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___f_131_; lean_object* v___x_133_; 
v___f_131_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_131_, 0, v_im_127_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___f_131_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_re_126_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___f_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg(lean_object* v_M_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___f_140_ = ((lean_object*)(lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg___closed__0));
v___x_141_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_141_, 0, lean_box(0));
lean_closure_set(v___x_141_, 1, lean_box(0));
lean_closure_set(v___x_141_, 2, lean_box(0));
lean_closure_set(v___x_141_, 3, v_M_137_);
v___x_142_ = lp_mathlib_Matrix_map___redArg(v___x_141_, v___f_140_, v_a_138_, v_a_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0(lean_object* v_m_143_, lean_object* v_n_144_, lean_object* v_M_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg(v_M_145_, v_a_146_, v_a_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__0(lean_object* v_p_149_, lean_object* v_q_150_, lean_object* v_a_151_, lean_object* v_j_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lp_tree_Formalism_UG_Jpq(v_p_149_, v_q_150_, v_a_151_, v_j_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__0___boxed(lean_object* v_p_154_, lean_object* v_q_155_, lean_object* v_a_156_, lean_object* v_j_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lp_tree_Formalism_BasicNotions_TH_adjZ___lam__0(v_p_154_, v_q_155_, v_a_156_, v_j_157_);
lean_dec(v_q_155_);
lean_dec(v_p_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__1(lean_object* v_p_159_, lean_object* v_q_160_, lean_object* v_a_161_, lean_object* v_j_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lp_tree_Formalism_UG_Jpq(v_p_159_, v_q_160_, v_j_162_, v_a_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__1___boxed(lean_object* v_p_164_, lean_object* v_q_165_, lean_object* v_a_166_, lean_object* v_j_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_tree_Formalism_BasicNotions_TH_adjZ___lam__1(v_p_164_, v_q_165_, v_a_166_, v_j_167_);
lean_dec(v_q_165_);
lean_dec(v_p_164_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__2(lean_object* v_Z_169_, lean_object* v_j_170_, lean_object* v_j_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lp_tree_Matrix_conjTranspose___at___00Formalism_BasicNotions_TH_adjZ_spec__0___redArg(v_Z_169_, v_j_171_, v_j_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1___lam__0(lean_object* v_v_173_, lean_object* v_w_174_, lean_object* v_i_175_){
_start:
{
lean_object* v___x_176_; lean_object* v_re_177_; lean_object* v_im_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_inc_ref(v_i_175_);
v___x_176_ = lean_apply_1(v_v_173_, v_i_175_);
v_re_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_re_177_);
v_im_178_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_im_178_);
lean_dec_ref(v___x_176_);
v___x_179_ = lean_apply_1(v_w_174_, v_i_175_);
v___x_180_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_177_, v_im_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1(lean_object* v_p_181_, lean_object* v_q_182_, lean_object* v_v_183_, lean_object* v_w_184_){
_start:
{
lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___f_185_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_185_, 0, v_v_183_);
lean_closure_set(v___f_185_, 1, v_w_184_);
v___x_186_ = l_List_finRange(v_p_181_);
v___x_187_ = l_List_finRange(v_q_182_);
v___x_188_ = lp_mathlib_Multiset_disjSum___redArg(v___x_186_, v___x_187_);
v___x_189_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_QuantumDeterminants_herm___at___00Formalism_QuantumDeterminants_Tz_spec__0_spec__1_spec__3___redArg(v___x_188_, v___f_185_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ___lam__3(lean_object* v_Z_190_, lean_object* v_p_191_, lean_object* v_q_192_, lean_object* v___f_193_, lean_object* v_j_194_){
_start:
{
lean_object* v___f_195_; lean_object* v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_adjZ___lam__2), 3, 2);
lean_closure_set(v___f_195_, 0, v_Z_190_);
lean_closure_set(v___f_195_, 1, v_j_194_);
v___x_196_ = lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1(v_p_191_, v_q_192_, v___f_193_, v___f_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_adjZ(lean_object* v_p_197_, lean_object* v_q_198_, lean_object* v_Z_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; 
lean_inc_n(v_q_198_, 3);
lean_inc_n(v_p_197_, 3);
v___f_202_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_adjZ___lam__0___boxed), 4, 3);
lean_closure_set(v___f_202_, 0, v_p_197_);
lean_closure_set(v___f_202_, 1, v_q_198_);
lean_closure_set(v___f_202_, 2, v_a_200_);
v___f_203_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_adjZ___lam__1___boxed), 4, 3);
lean_closure_set(v___f_203_, 0, v_p_197_);
lean_closure_set(v___f_203_, 1, v_q_198_);
lean_closure_set(v___f_203_, 2, v_a_201_);
v___f_204_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_adjZ___lam__3), 5, 4);
lean_closure_set(v___f_204_, 0, v_Z_199_);
lean_closure_set(v___f_204_, 1, v_p_197_);
lean_closure_set(v___f_204_, 2, v_q_198_);
lean_closure_set(v___f_204_, 3, v___f_202_);
v___x_205_ = lp_tree_dotProduct___at___00Formalism_BasicNotions_TH_adjZ_spec__1(v_p_197_, v_q_198_, v___f_204_, v___f_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_conjR(lean_object* v_p_206_, lean_object* v_q_207_, lean_object* v_Z_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; lean_object* v_re_212_; lean_object* v_im_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_222_; 
v___x_211_ = lp_tree_Formalism_BasicNotions_TH_adjZ(v_p_206_, v_q_207_, v_Z_208_, v_a_209_, v_a_210_);
v_re_212_ = lean_ctor_get(v___x_211_, 0);
v_im_213_ = lean_ctor_get(v___x_211_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_222_ == 0)
{
v___x_215_ = v___x_211_;
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_im_213_);
lean_inc(v_re_212_);
lean_dec(v___x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_220_; 
v___f_217_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_217_, 0, v_re_212_);
v___f_218_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_218_, 0, v_im_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___f_218_);
lean_ctor_set(v___x_215_, 0, v___f_217_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___f_217_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___f_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_wtSub(lean_object* v_p_223_, lean_object* v_q_224_, lean_object* v_V_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_act_228_, lean_object* v_00_u03bc_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_wtSub___boxed(lean_object* v_p_231_, lean_object* v_q_232_, lean_object* v_V_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_act_236_, lean_object* v_00_u03bc_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = lp_tree_Formalism_BasicNotions_TH_wtSub(v_p_231_, v_q_232_, v_V_233_, v_inst_234_, v_inst_235_, v_act_236_, v_00_u03bc_237_);
lean_dec_ref(v_00_u03bc_237_);
lean_dec(v_act_236_);
lean_dec(v_inst_235_);
lean_dec_ref(v_inst_234_);
lean_dec(v_q_232_);
lean_dec(v_p_231_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_hwSub(lean_object* v_p_239_, lean_object* v_q_240_, lean_object* v_V_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_act_244_, lean_object* v_00_u03bc_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(0);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_hwSub___boxed(lean_object* v_p_247_, lean_object* v_q_248_, lean_object* v_V_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_act_252_, lean_object* v_00_u03bc_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = lp_tree_Formalism_BasicNotions_TH_hwSub(v_p_247_, v_q_248_, v_V_249_, v_inst_250_, v_inst_251_, v_act_252_, v_00_u03bc_253_);
lean_dec_ref(v_00_u03bc_253_);
lean_dec(v_act_252_);
lean_dec(v_inst_251_);
lean_dec_ref(v_inst_250_);
lean_dec(v_q_248_);
lean_dec(v_p_247_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__0(lean_object* v_p_255_, lean_object* v_q_256_, lean_object* v_a_257_, lean_object* v_act_258_, lean_object* v_b_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_inc_ref(v_b_259_);
lean_inc_ref(v_a_257_);
lean_inc(v_q_256_);
lean_inc(v_p_255_);
v___x_261_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_Eab), 6, 4);
lean_closure_set(v___x_261_, 0, v_p_255_);
lean_closure_set(v___x_261_, 1, v_q_256_);
lean_closure_set(v___x_261_, 2, v_a_257_);
lean_closure_set(v___x_261_, 3, v_b_259_);
lean_inc(v_act_258_);
v___x_262_ = lean_apply_1(v_act_258_, v___x_261_);
v___x_263_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_Eab), 6, 4);
lean_closure_set(v___x_263_, 0, v_p_255_);
lean_closure_set(v___x_263_, 1, v_q_256_);
lean_closure_set(v___x_263_, 2, v_b_259_);
lean_closure_set(v___x_263_, 3, v_a_257_);
v___x_264_ = lean_apply_1(v_act_258_, v___x_263_);
v___x_265_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___x_264_, v___x_262_, v___y_260_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__1(lean_object* v_p_266_, lean_object* v_q_267_, lean_object* v_act_268_, lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v_a_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___f_273_; lean_object* v___x_92__overap_274_; lean_object* v___x_275_; 
v___f_273_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__0), 6, 4);
lean_closure_set(v___f_273_, 0, v_p_266_);
lean_closure_set(v___f_273_, 1, v_q_267_);
lean_closure_set(v___f_273_, 2, v_a_271_);
lean_closure_set(v___f_273_, 3, v_act_268_);
v___x_92__overap_274_ = lp_mathlib_Finset_sum___redArg(v___x_269_, v___x_270_, v___f_273_);
v___x_275_ = lean_apply_1(v___x_92__overap_274_, v___y_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__1___boxed(lean_object* v_p_276_, lean_object* v_q_277_, lean_object* v_act_278_, lean_object* v___x_279_, lean_object* v___x_280_, lean_object* v_a_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__1(v_p_276_, v_q_277_, v_act_278_, v___x_279_, v___x_280_, v_a_281_, v___y_282_);
lean_dec_ref(v___x_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___redArg(lean_object* v_p_284_, lean_object* v_q_285_, lean_object* v_inst_286_, lean_object* v_act_287_){
_start:
{
lean_object* v_toAddMonoid_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___f_293_; lean_object* v___x_294_; 
v_toAddMonoid_288_ = lean_ctor_get(v_inst_286_, 0);
lean_inc_ref(v_toAddMonoid_288_);
lean_dec_ref(v_inst_286_);
v___x_289_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_288_);
lean_inc(v_p_284_);
v___x_290_ = l_List_finRange(v_p_284_);
lean_inc(v_q_285_);
v___x_291_ = l_List_finRange(v_q_285_);
v___x_292_ = lp_mathlib_Multiset_disjSum___redArg(v___x_290_, v___x_291_);
lean_inc(v___x_292_);
lean_inc_ref(v___x_289_);
v___f_293_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_casimir___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_293_, 0, v_p_284_);
lean_closure_set(v___f_293_, 1, v_q_285_);
lean_closure_set(v___f_293_, 2, v_act_287_);
lean_closure_set(v___f_293_, 3, v___x_289_);
lean_closure_set(v___f_293_, 4, v___x_292_);
v___x_294_ = lp_mathlib_Finset_sum___redArg(v___x_289_, v___x_292_, v___f_293_);
lean_dec_ref(v___x_289_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir(lean_object* v_p_295_, lean_object* v_q_296_, lean_object* v_V_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_act_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lp_tree_Formalism_BasicNotions_TH_casimir___redArg(v_p_295_, v_q_296_, v_inst_298_, v_act_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_casimir___boxed(lean_object* v_p_302_, lean_object* v_q_303_, lean_object* v_V_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_act_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_tree_Formalism_BasicNotions_TH_casimir(v_p_302_, v_q_303_, v_V_304_, v_inst_305_, v_inst_306_, v_act_307_);
lean_dec(v_inst_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign___redArg(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
if (lean_obj_tag(v_x_310_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_Eab___closed__0, &lp_tree_Formalism_BasicNotions_TH_Eab___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_Eab___closed__0);
return v___x_318_;
}
else
{
goto v___jp_311_;
}
}
else
{
if (lean_obj_tag(v_x_310_) == 1)
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_Eab___closed__0, &lp_tree_Formalism_BasicNotions_TH_Eab___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_Eab___closed__0);
return v___x_319_;
}
else
{
goto v___jp_311_;
}
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v_re_313_; lean_object* v_im_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___x_317_; 
v___x_312_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_Eab___closed__0, &lp_tree_Formalism_BasicNotions_TH_Eab___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_Eab___closed__0);
v_re_313_ = lean_ctor_get(v___x_312_, 0);
v_im_314_ = lean_ctor_get(v___x_312_, 1);
lean_inc(v_re_313_);
v___f_315_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_315_, 0, v_re_313_);
lean_inc(v_im_314_);
v___f_316_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_316_, 0, v_im_314_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___f_315_);
lean_ctor_set(v___x_317_, 1, v___f_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign___redArg___boxed(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = lp_tree_Formalism_BasicNotions_TH_lineSign___redArg(v_x_320_, v_x_321_);
lean_dec_ref(v_x_321_);
lean_dec_ref(v_x_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign(lean_object* v_p_323_, lean_object* v_q_324_, lean_object* v_r_325_, lean_object* v_s_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lp_tree_Formalism_BasicNotions_TH_lineSign___redArg(v_x_327_, v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineSign___boxed(lean_object* v_p_330_, lean_object* v_q_331_, lean_object* v_r_332_, lean_object* v_s_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = lp_tree_Formalism_BasicNotions_TH_lineSign(v_p_330_, v_q_331_, v_r_332_, v_s_333_, v_x_334_, v_x_335_);
lean_dec_ref(v_x_335_);
lean_dec_ref(v_x_334_);
lean_dec(v_s_333_);
lean_dec(v_r_332_);
lean_dec(v_q_331_);
lean_dec(v_p_330_);
return v_res_336_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_linePos___redArg(lean_object* v_x_337_){
_start:
{
lean_object* v_fst_338_; 
v_fst_338_ = lean_ctor_get(v_x_337_, 0);
if (lean_obj_tag(v_fst_338_) == 0)
{
lean_object* v_snd_339_; 
v_snd_339_ = lean_ctor_get(v_x_337_, 1);
if (lean_obj_tag(v_snd_339_) == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 1;
return v___x_340_;
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
else
{
lean_object* v_snd_342_; 
v_snd_342_ = lean_ctor_get(v_x_337_, 1);
if (lean_obj_tag(v_snd_342_) == 1)
{
uint8_t v___x_343_; 
v___x_343_ = 1;
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = 0;
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_linePos___redArg___boxed(lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = lp_tree_Formalism_BasicNotions_TH_linePos___redArg(v_x_345_);
lean_dec_ref(v_x_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_linePos(lean_object* v_p_348_, lean_object* v_q_349_, lean_object* v_r_350_, lean_object* v_s_351_, lean_object* v_x_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = lp_tree_Formalism_BasicNotions_TH_linePos___redArg(v_x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_linePos___boxed(lean_object* v_p_354_, lean_object* v_q_355_, lean_object* v_r_356_, lean_object* v_s_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = lp_tree_Formalism_BasicNotions_TH_linePos(v_p_354_, v_q_355_, v_r_356_, v_s_357_, v_x_358_);
lean_dec_ref(v_x_358_);
lean_dec(v_s_357_);
lean_dec(v_r_356_);
lean_dec(v_q_355_);
lean_dec(v_p_354_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__0(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lp_mathlib_Equiv_sumProdDistrib(lean_box(0), lean_box(0), lean_box(0));
return v___x_361_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lp_mathlib_Equiv_prodSumDistrib(lean_box(0), lean_box(0), lean_box(0));
return v___x_362_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__2(void){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lp_mathlib_Equiv_sumComm(lean_box(0), lean_box(0));
return v___x_363_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__3(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__2, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__2_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__2);
v___x_365_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1);
v___x_366_ = lp_mathlib_Equiv_trans___redArg(v___x_365_, v___x_364_);
return v___x_366_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__4(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__3, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__3_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__3);
v___x_368_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__1);
v___x_369_ = lp_mathlib_Equiv_sumCongr___redArg(v___x_368_, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__5(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lp_mathlib_Equiv_sumSumSumComm(lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_370_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv(lean_object* v_p_371_, lean_object* v_q_372_, lean_object* v_r_373_, lean_object* v_s_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_375_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__0, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__0);
v___x_376_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__4, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__4_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__4);
v___x_377_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__5, &lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__5_once, _init_lp_tree_Formalism_BasicNotions_TH_lineEquiv___closed__5);
lean_inc(v_r_373_);
v___x_378_ = lp_mathlib_finProdFinEquiv___redArg(v_r_373_);
lean_inc(v_s_374_);
v___x_379_ = lp_mathlib_finProdFinEquiv___redArg(v_s_374_);
lean_inc_ref(v___x_379_);
lean_inc_ref(v___x_378_);
v___x_380_ = lp_mathlib_Equiv_sumCongr___redArg(v___x_378_, v___x_379_);
v___x_381_ = lean_nat_mul(v_p_371_, v_r_373_);
v___x_382_ = lean_nat_mul(v_q_372_, v_s_374_);
v___x_383_ = lp_mathlib_finSumFinEquiv(v___x_381_, v___x_382_);
v___x_384_ = lp_mathlib_Equiv_trans___redArg(v___x_380_, v___x_383_);
v___x_385_ = lp_mathlib_Equiv_sumCongr___redArg(v___x_379_, v___x_378_);
v___x_386_ = lean_nat_mul(v_p_371_, v_s_374_);
lean_dec(v_s_374_);
v___x_387_ = lean_nat_mul(v_q_372_, v_r_373_);
lean_dec(v_r_373_);
v___x_388_ = lp_mathlib_finSumFinEquiv(v___x_386_, v___x_387_);
v___x_389_ = lp_mathlib_Equiv_trans___redArg(v___x_385_, v___x_388_);
v___x_390_ = lp_mathlib_Equiv_sumCongr___redArg(v___x_384_, v___x_389_);
v___x_391_ = lp_mathlib_Equiv_trans___redArg(v___x_377_, v___x_390_);
v___x_392_ = lp_mathlib_Equiv_trans___redArg(v___x_376_, v___x_391_);
v___x_393_ = lp_mathlib_Equiv_trans___redArg(v___x_375_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lineEquiv___boxed(lean_object* v_p_394_, lean_object* v_q_395_, lean_object* v_r_396_, lean_object* v_s_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = lp_tree_Formalism_BasicNotions_TH_lineEquiv(v_p_394_, v_q_395_, v_r_396_, v_s_397_);
lean_dec(v_q_395_);
lean_dec(v_p_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter___redArg(lean_object* v_x_399_, lean_object* v_h__1_400_, lean_object* v_h__2_401_, lean_object* v_h__3_402_){
_start:
{
lean_object* v_fst_403_; 
v_fst_403_ = lean_ctor_get(v_x_399_, 0);
if (lean_obj_tag(v_fst_403_) == 0)
{
lean_object* v_snd_404_; 
lean_dec(v_h__2_401_);
v_snd_404_ = lean_ctor_get(v_x_399_, 1);
if (lean_obj_tag(v_snd_404_) == 0)
{
lean_object* v_val_405_; lean_object* v_val_406_; lean_object* v___x_407_; 
lean_inc_ref(v_snd_404_);
lean_inc_ref(v_fst_403_);
lean_dec(v_h__3_402_);
lean_dec_ref(v_x_399_);
v_val_405_ = lean_ctor_get(v_fst_403_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v_fst_403_, 1);
v_val_406_ = lean_ctor_get(v_snd_404_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_snd_404_, 1);
v___x_407_ = lean_apply_2(v_h__1_400_, v_val_405_, v_val_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
lean_dec(v_h__1_400_);
v___x_408_ = lean_apply_3(v_h__3_402_, v_x_399_, lean_box(0), lean_box(0));
return v___x_408_;
}
}
else
{
lean_object* v_snd_409_; 
lean_dec(v_h__1_400_);
v_snd_409_ = lean_ctor_get(v_x_399_, 1);
if (lean_obj_tag(v_snd_409_) == 1)
{
lean_object* v_val_410_; lean_object* v_val_411_; lean_object* v___x_412_; 
lean_inc_ref(v_snd_409_);
lean_inc_ref(v_fst_403_);
lean_dec(v_h__3_402_);
lean_dec_ref(v_x_399_);
v_val_410_ = lean_ctor_get(v_fst_403_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_fst_403_, 1);
v_val_411_ = lean_ctor_get(v_snd_409_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v_snd_409_, 1);
v___x_412_ = lean_apply_2(v_h__2_401_, v_val_410_, v_val_411_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
lean_dec(v_h__2_401_);
v___x_413_ = lean_apply_3(v_h__3_402_, v_x_399_, lean_box(0), lean_box(0));
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter(lean_object* v_p_414_, lean_object* v_q_415_, lean_object* v_r_416_, lean_object* v_s_417_, lean_object* v_motive_418_, lean_object* v_x_419_, lean_object* v_h__1_420_, lean_object* v_h__2_421_, lean_object* v_h__3_422_){
_start:
{
lean_object* v_fst_423_; 
v_fst_423_ = lean_ctor_get(v_x_419_, 0);
if (lean_obj_tag(v_fst_423_) == 0)
{
lean_object* v_snd_424_; 
lean_dec(v_h__2_421_);
v_snd_424_ = lean_ctor_get(v_x_419_, 1);
if (lean_obj_tag(v_snd_424_) == 0)
{
lean_object* v_val_425_; lean_object* v_val_426_; lean_object* v___x_427_; 
lean_inc_ref(v_snd_424_);
lean_inc_ref(v_fst_423_);
lean_dec(v_h__3_422_);
lean_dec_ref(v_x_419_);
v_val_425_ = lean_ctor_get(v_fst_423_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_fst_423_, 1);
v_val_426_ = lean_ctor_get(v_snd_424_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_snd_424_, 1);
v___x_427_ = lean_apply_2(v_h__1_420_, v_val_425_, v_val_426_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; 
lean_dec(v_h__1_420_);
v___x_428_ = lean_apply_3(v_h__3_422_, v_x_419_, lean_box(0), lean_box(0));
return v___x_428_;
}
}
else
{
lean_object* v_snd_429_; 
lean_dec(v_h__1_420_);
v_snd_429_ = lean_ctor_get(v_x_419_, 1);
if (lean_obj_tag(v_snd_429_) == 1)
{
lean_object* v_val_430_; lean_object* v_val_431_; lean_object* v___x_432_; 
lean_inc_ref(v_snd_429_);
lean_inc_ref(v_fst_423_);
lean_dec(v_h__3_422_);
lean_dec_ref(v_x_419_);
v_val_430_ = lean_ctor_get(v_fst_423_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_fst_423_, 1);
v_val_431_ = lean_ctor_get(v_snd_429_, 0);
lean_inc(v_val_431_);
lean_dec_ref_known(v_snd_429_, 1);
v___x_432_ = lean_apply_2(v_h__2_421_, v_val_430_, v_val_431_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
lean_dec(v_h__2_421_);
v___x_433_ = lean_apply_3(v_h__3_422_, v_x_419_, lean_box(0), lean_box(0));
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter___boxed(lean_object* v_p_434_, lean_object* v_q_435_, lean_object* v_r_436_, lean_object* v_s_437_, lean_object* v_motive_438_, lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_linePos_match__1_splitter(v_p_434_, v_q_435_, v_r_436_, v_s_437_, v_motive_438_, v_x_439_, v_h__1_440_, v_h__2_441_, v_h__3_442_);
lean_dec(v_s_437_);
lean_dec(v_r_436_);
lean_dec(v_q_435_);
lean_dec(v_p_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter___redArg(lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_, lean_object* v_h__3_448_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_dec(v_h__2_447_);
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_val_449_; lean_object* v_val_450_; lean_object* v___x_451_; 
lean_dec(v_h__3_448_);
v_val_449_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v_x_444_, 1);
v_val_450_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v_x_445_, 1);
v___x_451_ = lean_apply_2(v_h__1_446_, v_val_449_, v_val_450_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; 
lean_dec(v_h__1_446_);
v___x_452_ = lean_apply_4(v_h__3_448_, v_x_444_, v_x_445_, lean_box(0), lean_box(0));
return v___x_452_;
}
}
else
{
lean_dec(v_h__1_446_);
if (lean_obj_tag(v_x_445_) == 1)
{
lean_object* v_val_453_; lean_object* v_val_454_; lean_object* v___x_455_; 
lean_dec(v_h__3_448_);
v_val_453_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v_x_444_, 1);
v_val_454_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_val_454_);
lean_dec_ref_known(v_x_445_, 1);
v___x_455_ = lean_apply_2(v_h__2_447_, v_val_453_, v_val_454_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; 
lean_dec(v_h__2_447_);
v___x_456_ = lean_apply_4(v_h__3_448_, v_x_444_, v_x_445_, lean_box(0), lean_box(0));
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter(lean_object* v_p_457_, lean_object* v_q_458_, lean_object* v_r_459_, lean_object* v_s_460_, lean_object* v_motive_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_h__1_464_, lean_object* v_h__2_465_, lean_object* v_h__3_466_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_dec(v_h__2_465_);
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v_val_467_; lean_object* v_val_468_; lean_object* v___x_469_; 
lean_dec(v_h__3_466_);
v_val_467_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_x_462_, 1);
v_val_468_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v_x_463_, 1);
v___x_469_ = lean_apply_2(v_h__1_464_, v_val_467_, v_val_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_h__1_464_);
v___x_470_ = lean_apply_4(v_h__3_466_, v_x_462_, v_x_463_, lean_box(0), lean_box(0));
return v___x_470_;
}
}
else
{
lean_dec(v_h__1_464_);
if (lean_obj_tag(v_x_463_) == 1)
{
lean_object* v_val_471_; lean_object* v_val_472_; lean_object* v___x_473_; 
lean_dec(v_h__3_466_);
v_val_471_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v_x_462_, 1);
v_val_472_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v_x_463_, 1);
v___x_473_ = lean_apply_2(v_h__2_465_, v_val_471_, v_val_472_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; 
lean_dec(v_h__2_465_);
v___x_474_ = lean_apply_4(v_h__3_466_, v_x_462_, v_x_463_, lean_box(0), lean_box(0));
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter___boxed(lean_object* v_p_475_, lean_object* v_q_476_, lean_object* v_r_477_, lean_object* v_s_478_, lean_object* v_motive_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_h__1_482_, lean_object* v_h__2_483_, lean_object* v_h__3_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = lp_tree___private_Formalism_LocalRingCardinality_DataTheta_0__Formalism_BasicNotions_TH_lineSign_match__1_splitter(v_p_475_, v_q_476_, v_r_477_, v_s_478_, v_motive_479_, v_x_480_, v_x_481_, v_h__1_482_, v_h__2_483_, v_h__3_484_);
lean_dec(v_s_478_);
lean_dec(v_r_477_);
lean_dec(v_q_476_);
lean_dec(v_p_475_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_homog(lean_object* v_00_u03c3_486_, lean_object* v_d_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_homog___boxed(lean_object* v_00_u03c3_489_, lean_object* v_d_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = lp_tree_Formalism_BasicNotions_TH_homog(v_00_u03c3_489_, v_d_490_);
lean_dec(v_d_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0___redArg(lean_object* v_F_492_){
_start:
{
lean_object* v_Om_493_; lean_object* v_emb_494_; lean_object* v___f_495_; 
v_Om_493_ = lean_ctor_get(v_F_492_, 2);
lean_inc(v_Om_493_);
v_emb_494_ = lean_ctor_get(v_F_492_, 4);
lean_inc(v_emb_494_);
lean_dec_ref(v_F_492_);
v___f_495_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_495_, 0, v_emb_494_);
lean_closure_set(v___f_495_, 1, v_Om_493_);
return v___f_495_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0(lean_object* v_p_496_, lean_object* v_q_497_, lean_object* v_r_498_, lean_object* v_s_499_, lean_object* v_T0_500_, lean_object* v_T1_501_, lean_object* v_T2_502_, lean_object* v_F_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0___redArg(v_F_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0___boxed(lean_object* v_p_505_, lean_object* v_q_506_, lean_object* v_r_507_, lean_object* v_s_508_, lean_object* v_T0_509_, lean_object* v_T1_510_, lean_object* v_T2_511_, lean_object* v_F_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = lp_tree_Formalism_BasicNotions_TH_FockData_00_u03c0(v_p_505_, v_q_506_, v_r_507_, v_s_508_, v_T0_509_, v_T1_510_, v_T2_511_, v_F_512_);
lean_dec_ref(v_T2_511_);
lean_dec_ref(v_T1_510_);
lean_dec_ref(v_T0_509_);
lean_dec(v_s_508_);
lean_dec(v_r_507_);
lean_dec(v_q_506_);
lean_dec(v_p_505_);
return v_res_513_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__0(lean_object* v_a_514_, lean_object* v_lam_515_, lean_object* v_a_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(v_a_514_, v_a_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
lean_inc_ref(v_lam_515_);
v___x_518_ = lean_apply_1(v_lam_515_, v_a_516_);
v___x_519_ = lean_apply_1(v_lam_515_, v_a_514_);
v___x_520_ = l_Rat_blt(v___x_518_, v___x_519_);
return v___x_520_;
}
else
{
uint8_t v___x_521_; 
lean_dec_ref(v_a_516_);
lean_dec_ref(v_lam_515_);
lean_dec_ref(v_a_514_);
v___x_521_ = 0;
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__0___boxed(lean_object* v_a_522_, lean_object* v_lam_523_, lean_object* v_a_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__0(v_a_522_, v_lam_523_, v_a_524_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__1(lean_object* v_a_527_, lean_object* v_lam_528_, lean_object* v_a_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(v_a_527_, v_a_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
lean_inc_ref(v_lam_528_);
v___x_531_ = lean_apply_1(v_lam_528_, v_a_527_);
v___x_532_ = lean_apply_1(v_lam_528_, v_a_529_);
v___x_533_ = l_Rat_blt(v___x_531_, v___x_532_);
return v___x_533_;
}
else
{
uint8_t v___x_534_; 
lean_dec_ref(v_a_529_);
lean_dec_ref(v_lam_528_);
lean_dec_ref(v_a_527_);
v___x_534_ = 0;
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__1___boxed(lean_object* v_a_535_, lean_object* v_lam_536_, lean_object* v_a_537_){
_start:
{
uint8_t v_res_538_; lean_object* v_r_539_; 
v_res_538_ = lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__1(v_a_535_, v_lam_536_, v_a_537_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__2(lean_object* v_a_540_, lean_object* v_lam_541_, lean_object* v_a_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(v_a_540_, v_a_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_a_542_);
lean_dec_ref(v_lam_541_);
lean_dec_ref(v_a_540_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
lean_inc_ref(v_lam_541_);
v___x_544_ = lean_apply_1(v_lam_541_, v_a_542_);
v___x_545_ = lean_apply_1(v_lam_541_, v_a_540_);
v___x_546_ = l_Rat_blt(v___x_544_, v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__2___boxed(lean_object* v_a_547_, lean_object* v_lam_548_, lean_object* v_a_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__2(v_a_547_, v_lam_548_, v_a_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__3(lean_object* v_a_552_, lean_object* v_lam_553_, lean_object* v_a_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lp_tree_Formalism_BasicNotions_TH_instDecidableSameBlock___redArg(v_a_552_, v_a_554_);
if (v___x_555_ == 0)
{
lean_dec_ref(v_a_554_);
lean_dec_ref(v_lam_553_);
lean_dec_ref(v_a_552_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
lean_inc_ref(v_lam_553_);
v___x_556_ = lean_apply_1(v_lam_553_, v_a_552_);
v___x_557_ = lean_apply_1(v_lam_553_, v_a_554_);
v___x_558_ = l_Rat_blt(v___x_556_, v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__3___boxed(lean_object* v_a_559_, lean_object* v_lam_560_, lean_object* v_a_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__3(v_a_559_, v_lam_560_, v_a_561_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(2u);
v___x_565_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoNC(lean_object* v_p_566_, lean_object* v_q_567_, lean_object* v_lam_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___f_570_; lean_object* v___f_571_; lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_inc_ref_n(v_lam_568_, 3);
lean_inc_ref_n(v_a_569_, 3);
v___f_570_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_570_, 0, v_a_569_);
lean_closure_set(v___f_570_, 1, v_lam_568_);
v___f_571_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__1___boxed), 3, 2);
lean_closure_set(v___f_571_, 0, v_a_569_);
lean_closure_set(v___f_571_, 1, v_lam_568_);
v___f_572_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__2___boxed), 3, 2);
lean_closure_set(v___f_572_, 0, v_a_569_);
lean_closure_set(v___f_572_, 1, v_lam_568_);
v___f_573_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_rhoNC___lam__3___boxed), 3, 2);
lean_closure_set(v___f_573_, 0, v_a_569_);
lean_closure_set(v___f_573_, 1, v_lam_568_);
v___x_574_ = l_List_finRange(v_p_566_);
v___x_575_ = l_List_finRange(v_q_567_);
v___x_576_ = lp_mathlib_Multiset_disjSum___redArg(v___x_574_, v___x_575_);
lean_inc_n(v___x_576_, 3);
v___x_577_ = lp_mathlib_Multiset_filter___redArg(v___f_570_, v___x_576_);
v___x_578_ = l_List_lengthTR___redArg(v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_578_);
v___x_580_ = lp_mathlib_Multiset_filter___redArg(v___f_571_, v___x_576_);
v___x_581_ = l_List_lengthTR___redArg(v___x_580_);
lean_dec(v___x_580_);
v___x_582_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_581_);
v___x_583_ = l_Rat_sub(v___x_579_, v___x_582_);
v___x_584_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0);
v___x_585_ = l_Rat_div(v___x_583_, v___x_584_);
lean_dec_ref(v___x_583_);
v___x_586_ = lp_mathlib_Multiset_filter___redArg(v___f_572_, v___x_576_);
v___x_587_ = l_List_lengthTR___redArg(v___x_586_);
lean_dec(v___x_586_);
v___x_588_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_587_);
v___x_589_ = lp_mathlib_Multiset_filter___redArg(v___f_573_, v___x_576_);
v___x_590_ = l_List_lengthTR___redArg(v___x_589_);
lean_dec(v___x_589_);
v___x_591_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_590_);
v___x_592_ = l_Rat_sub(v___x_588_, v___x_591_);
v___x_593_ = l_Rat_div(v___x_592_, v___x_584_);
lean_dec_ref(v___x_592_);
v___x_594_ = l_Rat_sub(v___x_585_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_blattner(lean_object* v_p_595_, lean_object* v_q_596_, lean_object* v_lam_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_inc_ref(v_lam_597_);
lean_inc_ref(v_a_598_);
v___x_599_ = lean_apply_1(v_lam_597_, v_a_598_);
v___x_600_ = lp_tree_Formalism_BasicNotions_TH_rhoNC(v_p_595_, v_q_596_, v_lam_597_, v_a_598_);
v___x_601_ = l_Rat_add(v___x_599_, v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0(lean_object* v_n_604_, lean_object* v_i_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_606_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_n_604_);
v___x_607_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0);
v___x_608_ = l_Rat_sub(v___x_606_, v___x_607_);
v___x_609_ = lean_unsigned_to_nat(2u);
v___x_610_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0);
v___x_611_ = l_Rat_div(v___x_608_, v___x_610_);
lean_dec_ref(v___x_608_);
v___x_612_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_605_);
v___x_613_ = l_Rat_sub(v___x_611_, v___x_612_);
v___x_614_ = l_Rat_pow(v___x_613_, v___x_609_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_rhoSq(lean_object* v_n_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc(v_n_615_);
v___f_616_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0), 2, 1);
lean_closure_set(v___f_616_, 0, v_n_615_);
v___x_617_ = l_List_range(v_n_615_);
v___x_618_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_617_, v___f_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_normSq___lam__0(lean_object* v_lam_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_apply_1(v_lam_619_, v_a_620_);
v___x_622_ = lean_unsigned_to_nat(2u);
v___x_623_ = l_Rat_pow(v___x_621_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_normSq(lean_object* v_p_624_, lean_object* v_q_625_, lean_object* v_lam_626_){
_start:
{
lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___f_627_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_normSq___lam__0), 2, 1);
lean_closure_set(v___f_627_, 0, v_lam_626_);
v___x_628_ = l_List_finRange(v_p_624_);
v___x_629_ = l_List_finRange(v_q_625_);
v___x_630_ = lp_mathlib_Multiset_disjSum___redArg(v___x_628_, v___x_629_);
v___x_631_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_630_, v___f_627_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_shiftNu___redArg(lean_object* v_c_632_, lean_object* v_00_u03bc_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_apply_1(v_00_u03bc_633_, v_x_634_);
v___x_636_ = l_Rat_sub(v___x_635_, v_c_632_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_apply_1(v_00_u03bc_633_, v_x_634_);
v___x_638_ = l_Rat_add(v___x_637_, v_c_632_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_shiftNu(lean_object* v_p_639_, lean_object* v_q_640_, lean_object* v_c_641_, lean_object* v_00_u03bc_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lp_tree_Formalism_BasicNotions_TH_shiftNu___redArg(v_c_641_, v_00_u03bc_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_shiftNu___boxed(lean_object* v_p_645_, lean_object* v_q_646_, lean_object* v_c_647_, lean_object* v_00_u03bc_648_, lean_object* v_x_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = lp_tree_Formalism_BasicNotions_TH_shiftNu(v_p_645_, v_q_646_, v_c_647_, v_00_u03bc_648_, v_x_649_);
lean_dec(v_q_646_);
lean_dec(v_p_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_degW___lam__0(lean_object* v_c_651_, lean_object* v_00_u03bc_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lp_tree_Formalism_BasicNotions_TH_shiftNu___redArg(v_c_651_, v_00_u03bc_652_, v_a_653_);
v___x_655_ = lp_mathlib_abs___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__2(v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_degW(lean_object* v_p_656_, lean_object* v_q_657_, lean_object* v_c_658_, lean_object* v_00_u03bc_659_){
_start:
{
lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___f_660_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_degW___lam__0), 3, 2);
lean_closure_set(v___f_660_, 0, v_c_658_);
lean_closure_set(v___f_660_, 1, v_00_u03bc_659_);
v___x_661_ = l_List_finRange(v_p_656_);
v___x_662_ = l_List_finRange(v_q_657_);
v___x_663_ = lp_mathlib_Multiset_disjSum___redArg(v___x_661_, v___x_662_);
v___x_664_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_663_, v___f_660_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_cPair(lean_object* v_r_665_, lean_object* v_s_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_r_665_);
v___x_668_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_s_666_);
v___x_669_ = l_Rat_sub(v___x_667_, v___x_668_);
v___x_670_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0);
v___x_671_ = l_Rat_div(v___x_669_, v___x_670_);
lean_dec_ref(v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(lean_object* v_l_u2081_674_, lean_object* v_l_u2082_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v_val_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_val_677_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_x_676_, 1);
v___x_678_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0, &lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0);
v___x_679_ = l_List_getD___redArg(v_l_u2081_674_, v_val_677_, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v_val_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_val_680_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v_x_676_, 1);
v___x_681_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0, &lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0);
v___x_682_ = l_List_getD___redArg(v_l_u2082_675_, v_val_680_, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___boxed(lean_object* v_l_u2081_683_, lean_object* v_l_u2082_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(v_l_u2081_683_, v_l_u2082_684_, v_x_685_);
lean_dec(v_l_u2082_684_);
lean_dec(v_l_u2081_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks(lean_object* v_p_687_, lean_object* v_q_688_, lean_object* v_l_u2081_689_, lean_object* v_l_u2082_690_, lean_object* v_x_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(v_l_u2081_689_, v_l_u2082_690_, v_x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_ofBlocks___boxed(lean_object* v_p_693_, lean_object* v_q_694_, lean_object* v_l_u2081_695_, lean_object* v_l_u2082_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = lp_tree_Formalism_BasicNotions_TH_ofBlocks(v_p_693_, v_q_694_, v_l_u2081_695_, v_l_u2082_696_, v_x_697_);
lean_dec(v_l_u2082_696_);
lean_dec(v_l_u2081_695_);
lean_dec(v_q_694_);
lean_dec(v_p_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00List_mapTR_loop___at___00Formalism_BasicNotions_TH_pad_spec__0_spec__0(lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
if (lean_obj_tag(v_a_699_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = l_List_reverse___redArg(v_a_700_);
return v___x_701_;
}
else
{
lean_object* v_head_702_; lean_object* v_tail_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v_head_702_ = lean_ctor_get(v_a_699_, 0);
v_tail_703_ = lean_ctor_get(v_a_699_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_705_ = v_a_699_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_tail_703_);
lean_inc(v_head_702_);
lean_dec(v_a_699_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Rat_ofInt(v_head_702_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v_a_700_);
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_a_700_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v_a_699_ = v_tail_703_;
v_a_700_ = v___x_709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_TH_pad_spec__0(lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
if (lean_obj_tag(v_a_713_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l_List_reverse___redArg(v_a_714_);
return v___x_715_;
}
else
{
lean_object* v_head_716_; lean_object* v_tail_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_head_716_ = lean_ctor_get(v_a_713_, 0);
v_tail_717_ = lean_ctor_get(v_a_713_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v_a_713_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_tail_717_);
lean_inc(v_head_716_);
lean_dec(v_a_713_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = l_Rat_ofInt(v_head_716_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_a_714_);
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_714_);
v___x_723_ = v_reuseFailAlloc_725_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; 
v___x_724_ = lp_tree_List_mapTR_loop___at___00List_mapTR_loop___at___00Formalism_BasicNotions_TH_pad_spec__0_spec__0(v_tail_717_, v___x_723_);
return v___x_724_;
}
}
}
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_TH_pad___closed__0(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_nat_to_int(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_pad(lean_object* v_x_729_, lean_object* v_k_730_, lean_object* v_y_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_pad___closed__0, &lp_tree_Formalism_BasicNotions_TH_pad___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_pad___closed__0);
v___x_733_ = l_List_replicateTR___redArg(v_k_730_, v___x_732_);
v___x_734_ = l_List_appendTR___redArg(v_x_729_, v___x_733_);
v___x_735_ = l_List_appendTR___redArg(v___x_734_, v_y_731_);
v___x_736_ = lean_box(0);
v___x_737_ = lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_TH_pad_spec__0(v___x_735_, v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_BasicNotions_TH_block_spec__0(lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
if (lean_obj_tag(v_a_738_) == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_array_to_list(v_a_739_);
return v___x_740_;
}
else
{
lean_object* v_head_741_; lean_object* v_tail_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_753_; 
v_head_741_ = lean_ctor_get(v_a_738_, 0);
v_tail_742_ = lean_ctor_get(v_a_738_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_753_ == 0)
{
v___x_744_ = v_a_738_;
v_isShared_745_ = v_isSharedCheck_753_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_tail_742_);
lean_inc(v_head_741_);
lean_dec(v_a_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_753_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_head_741_);
v___x_747_ = lean_box(0);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_747_);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_752_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_739_, v___x_749_);
v_a_738_ = v_tail_742_;
v_a_739_ = v___x_750_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_TH_block_spec__1(lean_object* v_t_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
if (lean_obj_tag(v_a_755_) == 0)
{
lean_object* v___x_757_; 
lean_dec(v_t_754_);
v___x_757_ = l_List_reverse___redArg(v_a_756_);
return v___x_757_;
}
else
{
lean_object* v_head_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_773_; 
v_head_758_ = lean_ctor_get(v_a_755_, 0);
v_tail_759_ = lean_ctor_get(v_a_755_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_773_ == 0)
{
v___x_761_ = v_a_755_;
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_inc(v_head_758_);
lean_dec(v_a_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
lean_inc(v_t_754_);
v___x_763_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_754_);
v___x_764_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0);
v___x_765_ = l_Rat_sub(v___x_763_, v___x_764_);
v___x_766_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0);
v___x_767_ = l_Rat_div(v___x_765_, v___x_766_);
lean_dec_ref(v___x_765_);
v___x_768_ = l_Rat_sub(v___x_767_, v_head_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_a_756_);
lean_ctor_set(v___x_761_, 0, v___x_768_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_756_);
v___x_770_ = v_reuseFailAlloc_772_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v_a_755_ = v_tail_759_;
v_a_756_ = v___x_770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_block(lean_object* v_t_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_inc(v_t_776_);
v___x_777_ = l_List_range(v_t_776_);
v___x_778_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_TH_block___closed__0));
v___x_779_ = lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_BasicNotions_TH_block_spec__0(v___x_777_, v___x_778_);
v___x_780_ = lean_box(0);
v___x_781_ = lp_tree_List_mapTR_loop___at___00Formalism_BasicNotions_TH_block_spec__1(v_t_776_, v___x_779_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lamA(lean_object* v_al_782_, lean_object* v_be_783_, lean_object* v_ga_784_, lean_object* v_de_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = l_List_appendTR___redArg(v_al_782_, v_be_783_);
v___x_788_ = l_List_appendTR___redArg(v_ga_784_, v_de_785_);
v___x_789_ = lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(v___x_787_, v___x_788_, v_a_786_);
lean_dec(v___x_788_);
lean_dec(v___x_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lamA_x27(lean_object* v_t_790_, lean_object* v_al_791_, lean_object* v_be_792_, lean_object* v_ga_793_, lean_object* v_de_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_796_ = lp_tree_Formalism_BasicNotions_TH_block(v_t_790_);
v___x_797_ = l_List_appendTR___redArg(v_al_791_, v___x_796_);
v___x_798_ = l_List_appendTR___redArg(v___x_797_, v_de_794_);
v___x_799_ = l_List_appendTR___redArg(v_ga_793_, v_be_792_);
v___x_800_ = lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(v___x_798_, v___x_799_, v_a_795_);
lean_dec(v___x_799_);
lean_dec(v___x_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_lamM_x27(lean_object* v_t_801_, lean_object* v_al_802_, lean_object* v_be_803_, lean_object* v_ga_804_, lean_object* v_de_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_807_ = l_List_appendTR___redArg(v_al_802_, v_de_805_);
v___x_808_ = lp_tree_Formalism_BasicNotions_TH_block(v_t_801_);
v___x_809_ = l_List_appendTR___redArg(v_ga_804_, v___x_808_);
v___x_810_ = l_List_appendTR___redArg(v___x_809_, v_be_803_);
v___x_811_ = lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg(v___x_807_, v___x_810_, v_a_806_);
lean_dec(v___x_810_);
lean_dec(v___x_807_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_GrpData_covU___redArg(lean_object* v_T_812_, lean_object* v_x_813_){
_start:
{
lean_object* v_cov_814_; lean_object* v___x_815_; 
v_cov_814_ = lean_ctor_get(v_T_812_, 4);
lean_inc_ref(v_cov_814_);
lean_dec_ref(v_T_812_);
v___x_815_ = lean_apply_1(v_cov_814_, v_x_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_GrpData_covU(lean_object* v_p_816_, lean_object* v_q_817_, lean_object* v_T_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = lp_tree_Formalism_BasicNotions_TH_GrpData_covU___redArg(v_T_818_, v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_GrpData_covU___boxed(lean_object* v_p_821_, lean_object* v_q_822_, lean_object* v_T_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = lp_tree_Formalism_BasicNotions_TH_GrpData_covU(v_p_821_, v_q_822_, v_T_823_, v_x_824_);
lean_dec(v_q_822_);
lean_dec(v_p_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__0(lean_object* v_hcW_826_, lean_object* v_w_827_, lean_object* v_00_u03c4_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_830_; lean_object* v_u_831_; lean_object* v___x_832_; 
v___x_830_ = lean_apply_2(v_hcW_826_, v_w_827_, v_00_u03c4_828_);
v_u_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_u_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = lean_apply_1(v_u_831_, v___y_829_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__1(lean_object* v_hcW_833_, lean_object* v_w_834_, lean_object* v_00_u03c4_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_837_; lean_object* v_v_838_; lean_object* v___x_839_; 
v___x_837_ = lean_apply_2(v_hcW_833_, v_w_834_, v_00_u03c4_835_);
v_v_838_ = lean_ctor_get(v___x_837_, 1);
lean_inc_ref(v_v_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_apply_1(v_v_838_, v___y_836_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__2(lean_object* v_hcW_840_, lean_object* v_w_841_, lean_object* v_00_u03c4_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_844_; lean_object* v_b_845_; lean_object* v___x_846_; 
v___x_844_ = lean_apply_2(v_hcW_840_, v_w_841_, v_00_u03c4_842_);
v_b_845_ = lean_ctor_get(v___x_844_, 2);
lean_inc_ref(v_b_845_);
lean_dec_ref(v___x_844_);
v___x_846_ = lean_apply_1(v_b_845_, v___y_843_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__3(lean_object* v_hcW_847_, lean_object* v_w_848_, lean_object* v_00_u03c4_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_851_; lean_object* v_e_852_; lean_object* v___x_853_; 
v___x_851_ = lean_apply_2(v_hcW_847_, v_w_848_, v_00_u03c4_849_);
v_e_852_ = lean_ctor_get(v___x_851_, 3);
lean_inc_ref(v_e_852_);
lean_dec_ref(v___x_851_);
v___x_853_ = lean_apply_1(v_e_852_, v___y_850_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg(lean_object* v_D_854_, lean_object* v_w_855_, lean_object* v_eta_856_){
_start:
{
lean_object* v_R_857_; lean_object* v_hcW_858_; lean_object* v_t_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; 
v_R_857_ = lean_ctor_get(v_D_854_, 0);
lean_inc_ref(v_R_857_);
v_hcW_858_ = lean_ctor_get(v_D_854_, 9);
lean_inc_ref_n(v_hcW_858_, 4);
lean_dec_ref(v_D_854_);
v_t_859_ = lean_ctor_get(v_R_857_, 3);
lean_inc(v_t_859_);
lean_dec_ref(v_R_857_);
lean_inc_n(v_w_855_, 3);
v___f_860_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__0), 4, 2);
lean_closure_set(v___f_860_, 0, v_hcW_858_);
lean_closure_set(v___f_860_, 1, v_w_855_);
v___f_861_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__1), 4, 2);
lean_closure_set(v___f_861_, 0, v_hcW_858_);
lean_closure_set(v___f_861_, 1, v_w_855_);
v___f_862_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__2), 4, 2);
lean_closure_set(v___f_862_, 0, v_hcW_858_);
lean_closure_set(v___f_862_, 1, v_w_855_);
v___f_863_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg___lam__3), 4, 2);
lean_closure_set(v___f_863_, 0, v_hcW_858_);
lean_closure_set(v___f_863_, 1, v_w_855_);
v___x_864_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_864_, 0, v_t_859_);
lean_ctor_set(v___x_864_, 1, v___f_860_);
lean_ctor_set(v___x_864_, 2, v___f_861_);
lean_ctor_set(v___x_864_, 3, v___f_862_);
lean_ctor_set(v___x_864_, 4, v___f_863_);
lean_ctor_set(v___x_864_, 5, v_eta_856_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_ofWord(lean_object* v_D_865_, lean_object* v_w_866_, lean_object* v_eta_867_, lean_object* v_h_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg(v_D_865_, v_w_866_, v_eta_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_block___lam__0(lean_object* v_len_870_, lean_object* v_c_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_873_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_len_870_);
v___x_874_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoSq___lam__0___closed__0);
v___x_875_ = l_Rat_sub(v___x_873_, v___x_874_);
v___x_876_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0, &lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_rhoNC___closed__0);
v___x_877_ = l_Rat_div(v___x_875_, v___x_876_);
lean_dec_ref(v___x_875_);
v___x_878_ = l_Rat_add(v_c_871_, v___x_877_);
v___x_879_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_a_872_);
v___x_880_ = l_Rat_sub(v___x_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object* v___x_881_, uint8_t v___x_882_, lean_object* v___y_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = l_instDecidableEqRat_decEq(v___x_881_, v___y_883_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
v___x_885_ = 1;
return v___x_885_;
}
else
{
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_363__boxed_889_; uint8_t v_res_890_; lean_object* v_r_891_; 
v___x_363__boxed_889_ = lean_unbox(v___x_887_);
v_res_890_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(v___x_886_, v___x_363__boxed_889_, v___y_888_);
lean_dec_ref(v___y_888_);
lean_dec_ref(v___x_886_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_as_892_, size_t v_i_893_, size_t v_stop_894_, lean_object* v_b_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_eq(v_i_893_, v_stop_894_);
if (v___x_896_ == 0)
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___f_901_; uint8_t v___x_902_; 
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v_i_893_, v___x_897_);
v___x_899_ = lean_array_uget_borrowed(v_as_892_, v___x_898_);
v___x_900_ = lean_box(v___x_896_);
lean_inc(v___x_899_);
v___f_901_ = lean_alloc_closure((void*)(lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_901_, 0, v___x_899_);
lean_closure_set(v___f_901_, 1, v___x_900_);
lean_inc(v_b_895_);
v___x_902_ = l_List_decidableBAll___redArg(v___f_901_, v_b_895_);
if (v___x_902_ == 0)
{
v_i_893_ = v___x_898_;
goto _start;
}
else
{
lean_object* v___x_904_; 
lean_inc(v___x_899_);
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_899_);
lean_ctor_set(v___x_904_, 1, v_b_895_);
v_i_893_ = v___x_898_;
v_b_895_ = v___x_904_;
goto _start;
}
}
else
{
return v_b_895_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_as_906_, lean_object* v_i_907_, lean_object* v_stop_908_, lean_object* v_b_909_){
_start:
{
size_t v_i_boxed_910_; size_t v_stop_boxed_911_; lean_object* v_res_912_; 
v_i_boxed_910_ = lean_unbox_usize(v_i_907_);
lean_dec(v_i_907_);
v_stop_boxed_911_ = lean_unbox_usize(v_stop_908_);
lean_dec(v_stop_908_);
v_res_912_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_as_906_, v_i_boxed_910_, v_stop_boxed_911_, v_b_909_);
lean_dec_ref(v_as_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_init_913_, lean_object* v_l_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_915_ = lean_array_mk(v_l_914_);
v___x_916_ = lean_array_get_size(v___x_915_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_nat_dec_lt(v___x_917_, v___x_916_);
if (v___x_918_ == 0)
{
lean_dec_ref(v___x_915_);
return v_init_913_;
}
else
{
size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_usize_of_nat(v___x_916_);
v___x_920_ = ((size_t)0ULL);
v___x_921_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v___x_915_, v___x_919_, v___x_920_, v_init_913_);
lean_dec_ref(v___x_915_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_l_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_box(0);
v___x_924_ = lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v___x_923_, v_l_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1(lean_object* v_s_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0(lean_object* v_s_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0___redArg(lean_object* v_f_929_, lean_object* v_s_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lp_mathlib_Multiset_map___redArg(v_f_929_, v_s_930_);
v___x_932_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_block(lean_object* v_c_933_, lean_object* v_len_934_){
_start:
{
lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc(v_len_934_);
v___f_935_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_block___lam__0), 3, 2);
lean_closure_set(v___f_935_, 0, v_len_934_);
lean_closure_set(v___f_935_, 1, v_c_933_);
v___x_936_ = l_List_range(v_len_934_);
v___x_937_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0___redArg(v___f_935_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0(lean_object* v_00_u03b1_938_, lean_object* v_f_939_, lean_object* v_s_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0___redArg(v_f_939_, v_s_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2(lean_object* v_l_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_R_944_, lean_object* v_l_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_block_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__0(lean_object* v_P_947_, lean_object* v_00_u03c4_948_, lean_object* v_i_949_){
_start:
{
lean_object* v_v_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_v_950_ = lean_ctor_get(v_P_947_, 2);
lean_inc_ref(v_v_950_);
lean_dec_ref(v_P_947_);
v___x_951_ = lean_apply_2(v_v_950_, v_00_u03c4_948_, v_i_949_);
v___x_952_ = 1;
v___x_953_ = lean_box(v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_951_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__1(lean_object* v_P_955_, lean_object* v_00_u03c4_956_, lean_object* v_j_957_, lean_object* v_i_958_){
_start:
{
lean_object* v_b_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_b_959_ = lean_ctor_get(v_P_955_, 3);
lean_inc_ref(v_b_959_);
lean_dec_ref(v_P_955_);
lean_inc(v_i_958_);
v___x_960_ = lean_apply_2(v_b_959_, v_00_u03c4_956_, v_i_958_);
v___x_961_ = l_Rat_neg(v___x_960_);
v___x_962_ = lean_nat_dec_le(v_i_958_, v_j_957_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_963_ = lean_nat_sub(v_i_958_, v_j_957_);
lean_dec(v_i_958_);
v___x_964_ = lp_mathlib_Nat_instDecidablePredEven(v___x_963_);
lean_dec(v___x_963_);
v___x_965_ = lean_box(v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_i_958_);
v___x_967_ = lean_box(v___x_962_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_961_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__1___boxed(lean_object* v_P_969_, lean_object* v_00_u03c4_970_, lean_object* v_j_971_, lean_object* v_i_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__1(v_P_969_, v_00_u03c4_970_, v_j_971_, v_i_972_);
lean_dec(v_j_971_);
return v_res_973_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2(lean_object* v_j_974_, lean_object* v_a_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_nat_dec_lt(v_a_975_, v_j_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2___boxed(lean_object* v_j_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2(v_j_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec(v_j_977_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__3(lean_object* v_x_981_){
_start:
{
uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = 1;
v___x_983_ = lean_box(v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_x_981_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__0(uint8_t v___y_985_, uint8_t v___y_986_){
_start:
{
if (v___y_985_ == 0)
{
if (v___y_986_ == 0)
{
uint8_t v___x_987_; 
v___x_987_ = 1;
return v___x_987_;
}
else
{
return v___y_985_;
}
}
else
{
return v___y_986_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__0___boxed(lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v___y_886__boxed_990_; uint8_t v___y_887__boxed_991_; uint8_t v_res_992_; lean_object* v_r_993_; 
v___y_886__boxed_990_ = lean_unbox(v___y_988_);
v___y_887__boxed_991_ = lean_unbox(v___y_989_);
v_res_992_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__0(v___y_886__boxed_990_, v___y_887__boxed_991_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__1(lean_object* v___f_994_, lean_object* v___x_995_, uint8_t v___x_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_alloc_closure((void*)(l_instDecidableEqRat___boxed), 2, 0);
v___x_999_ = l_instDecidableEqProd___redArg(v___x_998_, v___f_994_, v___x_995_, v___y_997_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; 
v___x_1000_ = 1;
return v___x_1000_;
}
else
{
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__1___boxed(lean_object* v___f_1001_, lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_896__boxed_1005_; uint8_t v_res_1006_; lean_object* v_r_1007_; 
v___x_896__boxed_1005_ = lean_unbox(v___x_1003_);
v_res_1006_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__1(v___f_1001_, v___x_1002_, v___x_896__boxed_1005_, v___y_1004_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10(lean_object* v_as_1009_, size_t v_i_1010_, size_t v_stop_1011_, lean_object* v_b_1012_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_eq(v_i_1010_, v_stop_1011_);
if (v___x_1013_ == 0)
{
lean_object* v___f_1014_; size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; uint8_t v___x_1020_; 
v___f_1014_ = ((lean_object*)(lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___closed__0));
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_sub(v_i_1010_, v___x_1015_);
v___x_1017_ = lean_array_uget_borrowed(v_as_1009_, v___x_1016_);
v___x_1018_ = lean_box(v___x_1013_);
lean_inc(v___x_1017_);
v___f_1019_ = lean_alloc_closure((void*)(lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1019_, 0, v___f_1014_);
lean_closure_set(v___f_1019_, 1, v___x_1017_);
lean_closure_set(v___f_1019_, 2, v___x_1018_);
lean_inc(v_b_1012_);
v___x_1020_ = l_List_decidableBAll___redArg(v___f_1019_, v_b_1012_);
if (v___x_1020_ == 0)
{
v_i_1010_ = v___x_1016_;
goto _start;
}
else
{
lean_object* v___x_1022_; 
lean_inc(v___x_1017_);
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1017_);
lean_ctor_set(v___x_1022_, 1, v_b_1012_);
v_i_1010_ = v___x_1016_;
v_b_1012_ = v___x_1022_;
goto _start;
}
}
else
{
return v_b_1012_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10___boxed(lean_object* v_as_1024_, lean_object* v_i_1025_, lean_object* v_stop_1026_, lean_object* v_b_1027_){
_start:
{
size_t v_i_boxed_1028_; size_t v_stop_boxed_1029_; lean_object* v_res_1030_; 
v_i_boxed_1028_ = lean_unbox_usize(v_i_1025_);
lean_dec(v_i_1025_);
v_stop_boxed_1029_ = lean_unbox_usize(v_stop_1026_);
lean_dec(v_stop_1026_);
v_res_1030_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10(v_as_1024_, v_i_boxed_1028_, v_stop_boxed_1029_, v_b_1027_);
lean_dec_ref(v_as_1024_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object* v_init_1031_, lean_object* v_l_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1033_ = lean_array_mk(v_l_1032_);
v___x_1034_ = lean_array_get_size(v___x_1033_);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_nat_dec_lt(v___x_1035_, v___x_1034_);
if (v___x_1036_ == 0)
{
lean_dec_ref(v___x_1033_);
return v_init_1031_;
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_usize_of_nat(v___x_1034_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__10(v___x_1033_, v___x_1037_, v___x_1038_, v_init_1031_);
lean_dec_ref(v___x_1033_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_l_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(v___x_1041_, v_l_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1(lean_object* v_s_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_s_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0(lean_object* v_s_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_s_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(lean_object* v_f_1047_, lean_object* v_s_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lp_mathlib_Multiset_map___redArg(v_f_1047_, v_s_1048_);
v___x_1050_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__4(lean_object* v_P_1051_, lean_object* v_00_u03c4_1052_, lean_object* v___f_1053_, lean_object* v_i_1054_){
_start:
{
lean_object* v_t_1055_; lean_object* v_e_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_t_1055_ = lean_ctor_get(v_P_1051_, 0);
lean_inc(v_t_1055_);
v_e_1056_ = lean_ctor_get(v_P_1051_, 4);
lean_inc_ref(v_e_1056_);
lean_dec_ref(v_P_1051_);
v___x_1057_ = lean_apply_2(v_e_1056_, v_00_u03c4_1052_, v_i_1054_);
v___x_1058_ = l_Rat_neg(v___x_1057_);
v___x_1059_ = lp_tree_Formalism_BasicNotions_TH_TPar_block(v___x_1058_, v_t_1055_);
v___x_1060_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_1053_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__5(uint8_t v___x_1061_, lean_object* v_P_1062_, lean_object* v_00_u03c4_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1079_; 
v_fst_1065_ = lean_ctor_get(v_x_1064_, 0);
v_snd_1066_ = lean_ctor_get(v_x_1064_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1068_ = v_x_1064_;
v_isShared_1069_ = v_isSharedCheck_1079_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_x_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1079_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___y_1071_; 
if (v___x_1061_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_00_u03c4_1063_);
lean_dec_ref(v_P_1062_);
v___x_1076_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0, &lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0_once, _init_lp_tree_Formalism_BasicNotions_TH_ofBlocks___redArg___closed__0);
v___y_1071_ = v___x_1076_;
goto v___jp_1070_;
}
else
{
lean_object* v_eta_1077_; lean_object* v___x_1078_; 
v_eta_1077_ = lean_ctor_get(v_P_1062_, 5);
lean_inc_ref(v_eta_1077_);
lean_dec_ref(v_P_1062_);
v___x_1078_ = lean_apply_1(v_eta_1077_, v_00_u03c4_1063_);
v___y_1071_ = v___x_1078_;
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = l_Rat_add(v_fst_1065_, v___y_1071_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_snd_1066_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__5___boxed(lean_object* v___x_1080_, lean_object* v_P_1081_, lean_object* v_00_u03c4_1082_, lean_object* v_x_1083_){
_start:
{
uint8_t v___x_977__boxed_1084_; lean_object* v_res_1085_; 
v___x_977__boxed_1084_ = lean_unbox(v___x_1080_);
v_res_1085_ = lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__5(v___x_977__boxed_1084_, v_P_1081_, v_00_u03c4_1082_, v_x_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg___lam__0(lean_object* v_t_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_apply_1(v_t_1086_, v_a_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg(lean_object* v_s_1089_, lean_object* v_t_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___f_1091_ = lean_alloc_closure((void*)(lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1091_, 0, v_t_1090_);
v___x_1092_ = lp_mathlib_Multiset_bind___redArg(v_s_1089_, v___f_1091_);
v___x_1093_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT uint8_t lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___lam__0(uint8_t v___y_1094_, uint8_t v___y_1095_){
_start:
{
if (v___y_1094_ == 0)
{
if (v___y_1095_ == 0)
{
uint8_t v___x_1096_; 
v___x_1096_ = 1;
return v___x_1096_;
}
else
{
return v___y_1094_;
}
}
else
{
return v___y_1095_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___lam__0___boxed(lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v___y_1014__boxed_1099_; uint8_t v___y_1015__boxed_1100_; uint8_t v_res_1101_; lean_object* v_r_1102_; 
v___y_1014__boxed_1099_ = lean_unbox(v___y_1097_);
v___y_1015__boxed_1100_ = lean_unbox(v___y_1098_);
v_res_1101_ = lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___lam__0(v___y_1014__boxed_1099_, v___y_1015__boxed_1100_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
LEAN_EXPORT uint8_t lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2(lean_object* v_a_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
uint8_t v___x_1106_; 
lean_dec_ref(v_a_1104_);
v___x_1106_ = 0;
return v___x_1106_;
}
else
{
lean_object* v_head_1107_; lean_object* v_tail_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_head_1107_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_head_1107_);
v_tail_1108_ = lean_ctor_get(v_x_1105_, 1);
lean_inc(v_tail_1108_);
lean_dec_ref_known(v_x_1105_, 2);
v___f_1109_ = ((lean_object*)(lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___closed__0));
v___x_1110_ = lean_alloc_closure((void*)(l_instDecidableEqRat___boxed), 2, 0);
lean_inc_ref(v_a_1104_);
v___x_1111_ = l_instDecidableEqProd___redArg(v___x_1110_, v___f_1109_, v_a_1104_, v_head_1107_);
if (v___x_1111_ == 0)
{
v_x_1105_ = v_tail_1108_;
goto _start;
}
else
{
lean_dec(v_tail_1108_);
lean_dec_ref(v_a_1104_);
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2___boxed(lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2(v_a_1113_, v_x_1114_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3_spec__5(lean_object* v_as_1117_, size_t v_i_1118_, size_t v_stop_1119_, lean_object* v_b_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_eq(v_i_1118_, v_stop_1119_);
if (v___x_1121_ == 0)
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1122_ = ((size_t)1ULL);
v___x_1123_ = lean_usize_sub(v_i_1118_, v___x_1122_);
v___x_1124_ = lean_array_uget_borrowed(v_as_1117_, v___x_1123_);
lean_inc(v_b_1120_);
lean_inc(v___x_1124_);
v___x_1125_ = lp_tree_List_elem___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__2(v___x_1124_, v_b_1120_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_inc(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v_b_1120_);
v_i_1118_ = v___x_1123_;
v_b_1120_ = v___x_1126_;
goto _start;
}
else
{
v_i_1118_ = v___x_1123_;
goto _start;
}
}
else
{
return v_b_1120_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3_spec__5___boxed(lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_stop_1131_, lean_object* v_b_1132_){
_start:
{
size_t v_i_boxed_1133_; size_t v_stop_boxed_1134_; lean_object* v_res_1135_; 
v_i_boxed_1133_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_stop_boxed_1134_ = lean_unbox_usize(v_stop_1131_);
lean_dec(v_stop_1131_);
v_res_1135_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3_spec__5(v_as_1129_, v_i_boxed_1133_, v_stop_boxed_1134_, v_b_1132_);
lean_dec_ref(v_as_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3(lean_object* v_init_1136_, lean_object* v_l_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1138_ = lean_array_mk(v_l_1137_);
v___x_1139_ = lean_array_get_size(v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_nat_dec_lt(v___x_1140_, v___x_1139_);
if (v___x_1141_ == 0)
{
lean_dec_ref(v___x_1138_);
return v_init_1136_;
}
else
{
size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_usize_of_nat(v___x_1139_);
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3_spec__5(v___x_1138_, v___x_1142_, v___x_1143_, v_init_1136_);
lean_dec_ref(v___x_1138_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1(lean_object* v_s_1145_, lean_object* v_t_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3(v_t_1146_, v_s_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Dpar(lean_object* v_D_1149_, lean_object* v_P_1150_, lean_object* v_j_1151_, lean_object* v_00_u03c4_1152_){
_start:
{
lean_object* v_R_1153_; lean_object* v_k_1154_; lean_object* v_m_1155_; lean_object* v___f_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_R_1153_ = lean_ctor_get(v_D_1149_, 0);
lean_inc_ref(v_R_1153_);
lean_dec_ref(v_D_1149_);
v_k_1154_ = lean_ctor_get(v_R_1153_, 1);
lean_inc(v_k_1154_);
v_m_1155_ = lean_ctor_get(v_R_1153_, 2);
lean_inc(v_m_1155_);
lean_dec_ref(v_R_1153_);
lean_inc_n(v_00_u03c4_1152_, 3);
lean_inc_ref_n(v_P_1150_, 3);
v___f_1156_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__0), 3, 2);
lean_closure_set(v___f_1156_, 0, v_P_1150_);
lean_closure_set(v___f_1156_, 1, v_00_u03c4_1152_);
lean_inc_n(v_j_1151_, 2);
v___f_1157_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1157_, 0, v_P_1150_);
lean_closure_set(v___f_1157_, 1, v_00_u03c4_1152_);
lean_closure_set(v___f_1157_, 2, v_j_1151_);
v___f_1158_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1158_, 0, v_j_1151_);
v___f_1159_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___closed__0));
v___f_1160_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__4), 4, 3);
lean_closure_set(v___f_1160_, 0, v_P_1150_);
lean_closure_set(v___f_1160_, 1, v_00_u03c4_1152_);
lean_closure_set(v___f_1160_, 2, v___f_1159_);
v___x_1161_ = lp_mathlib_Nat_instDecidablePredOdd(v_j_1151_);
lean_dec(v_j_1151_);
v___x_1162_ = lean_box(v___x_1161_);
v___f_1163_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1163_, 0, v___x_1162_);
lean_closure_set(v___f_1163_, 1, v_P_1150_);
lean_closure_set(v___f_1163_, 2, v_00_u03c4_1152_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v_k_1154_, v___x_1164_);
lean_dec(v_k_1154_);
v___x_1166_ = l_List_finRange(v___x_1165_);
v___x_1167_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_1156_, v___x_1166_);
v___x_1168_ = l_List_finRange(v_m_1155_);
lean_inc(v___x_1168_);
v___x_1169_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_1157_, v___x_1168_);
v___x_1170_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3(v___x_1169_, v___x_1167_);
v___x_1171_ = lp_mathlib_Multiset_filter___redArg(v___f_1158_, v___x_1168_);
v___x_1172_ = lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg(v___x_1171_, v___f_1160_);
v___x_1173_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3(v___x_1172_, v___x_1170_);
v___x_1174_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_1163_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0(lean_object* v_00_u03b1_1175_, lean_object* v_f_1176_, lean_object* v_s_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v_f_1176_, v_s_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2(lean_object* v_00_u03b1_1179_, lean_object* v_s_1180_, lean_object* v_t_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg(v_s_1180_, v_t_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4(lean_object* v_l_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_l_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_R_1185_, lean_object* v_l_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_l_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Xpar___lam__0(lean_object* v_P_1188_, lean_object* v_00_u03c4_1189_, lean_object* v_i_1190_){
_start:
{
lean_object* v_u_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_u_1191_ = lean_ctor_get(v_P_1188_, 1);
lean_inc_ref(v_u_1191_);
lean_dec_ref(v_P_1188_);
v___x_1192_ = lean_apply_2(v_u_1191_, v_00_u03c4_1189_, v_i_1190_);
v___x_1193_ = 1;
v___x_1194_ = lean_box(v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1192_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Xpar___lam__3(lean_object* v_P_1196_, lean_object* v_00_u03c4_1197_, lean_object* v___f_1198_, lean_object* v_i_1199_){
_start:
{
lean_object* v_t_1200_; lean_object* v_e_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_t_1200_ = lean_ctor_get(v_P_1196_, 0);
lean_inc(v_t_1200_);
v_e_1201_ = lean_ctor_get(v_P_1196_, 4);
lean_inc_ref(v_e_1201_);
lean_dec_ref(v_P_1196_);
v___x_1202_ = lean_apply_2(v_e_1201_, v_00_u03c4_1197_, v_i_1199_);
v___x_1203_ = l_Rat_neg(v___x_1202_);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_add(v_t_1200_, v___x_1204_);
lean_dec(v_t_1200_);
v___x_1206_ = lp_tree_Formalism_BasicNotions_TH_TPar_block(v___x_1203_, v___x_1205_);
v___x_1207_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_1198_, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_TH_TPar_Xpar(lean_object* v_D_1208_, lean_object* v_P_1209_, lean_object* v_j_1210_, lean_object* v_00_u03c4_1211_){
_start:
{
lean_object* v_R_1212_; lean_object* v_k_1213_; lean_object* v_m_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_R_1212_ = lean_ctor_get(v_D_1208_, 0);
lean_inc_ref(v_R_1212_);
lean_dec_ref(v_D_1208_);
v_k_1213_ = lean_ctor_get(v_R_1212_, 1);
lean_inc(v_k_1213_);
v_m_1214_ = lean_ctor_get(v_R_1212_, 2);
lean_inc(v_m_1214_);
lean_dec_ref(v_R_1212_);
lean_inc(v_00_u03c4_1211_);
lean_inc_ref(v_P_1209_);
v___f_1215_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Xpar___lam__0), 3, 2);
lean_closure_set(v___f_1215_, 0, v_P_1209_);
lean_closure_set(v___f_1215_, 1, v_00_u03c4_1211_);
v___f_1216_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1216_, 0, v_j_1210_);
v___f_1217_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_TH_TPar_Dpar___closed__0));
v___f_1218_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Xpar___lam__3), 4, 3);
lean_closure_set(v___f_1218_, 0, v_P_1209_);
lean_closure_set(v___f_1218_, 1, v_00_u03c4_1211_);
lean_closure_set(v___f_1218_, 2, v___f_1217_);
v___x_1219_ = l_List_finRange(v_k_1213_);
v___x_1220_ = lp_tree_Finset_image___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__0___redArg(v___f_1215_, v___x_1219_);
v___x_1221_ = l_List_finRange(v_m_1214_);
v___x_1222_ = lp_mathlib_Multiset_filter___redArg(v___f_1216_, v___x_1221_);
v___x_1223_ = lp_tree_Finset_biUnion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__2___redArg(v___x_1222_, v___f_1218_);
v___x_1224_ = lp_tree_List_foldrTR___at___00Multiset_ndunion___at___00Formalism_BasicNotions_TH_TPar_Dpar_spec__1_spec__3(v___x_1223_, v___x_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_sphOff(lean_object* v_D_1225_, lean_object* v_X_1226_, lean_object* v_V_1227_, lean_object* v_S_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_box(0);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_sphOff___boxed(lean_object* v_D_1230_, lean_object* v_X_1231_, lean_object* v_V_1232_, lean_object* v_S_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = lp_tree_Formalism_BasicNotions_ThetaX_sphOff(v_D_1230_, v_X_1231_, v_V_1232_, v_S_1233_);
lean_dec(v_S_1233_);
lean_dec_ref(v_V_1232_);
lean_dec_ref(v_X_1231_);
lean_dec_ref(v_D_1230_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_cuspD(lean_object* v_D_1235_, lean_object* v_X_1236_, lean_object* v_P_1237_, lean_object* v_j_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_box(0);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_cuspD___boxed(lean_object* v_D_1240_, lean_object* v_X_1241_, lean_object* v_P_1242_, lean_object* v_j_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = lp_tree_Formalism_BasicNotions_ThetaX_cuspD(v_D_1240_, v_X_1241_, v_P_1242_, v_j_1243_);
lean_dec(v_j_1243_);
lean_dec_ref(v_P_1242_);
lean_dec_ref(v_X_1241_);
lean_dec_ref(v_D_1240_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_typeX(lean_object* v_D_1245_, lean_object* v_X_1246_, lean_object* v_P_1247_, lean_object* v_j_1248_){
_start:
{
lean_object* v_typ_1249_; lean_object* v_Xs_1250_; lean_object* v_t_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_typ_1249_ = lean_ctor_get(v_X_1246_, 8);
lean_inc_ref(v_typ_1249_);
v_Xs_1250_ = lean_ctor_get(v_X_1246_, 17);
lean_inc_ref(v_Xs_1250_);
lean_dec_ref(v_X_1246_);
v_t_1251_ = lean_ctor_get(v_P_1247_, 0);
lean_inc(v_j_1248_);
lean_inc(v_t_1251_);
v___x_1252_ = lean_apply_2(v_Xs_1250_, v_t_1251_, v_j_1248_);
v___x_1253_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_TH_TPar_Xpar), 4, 3);
lean_closure_set(v___x_1253_, 0, v_D_1245_);
lean_closure_set(v___x_1253_, 1, v_P_1247_);
lean_closure_set(v___x_1253_, 2, v_j_1248_);
v___x_1254_ = lean_apply_2(v_typ_1249_, v___x_1252_, v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bj___redArg(lean_object* v_X_1255_, lean_object* v_t_1256_, lean_object* v_j_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_Xs_1262_; lean_object* v_Ys_1263_; lean_object* v_iXYs_1264_; lean_object* v_Bper_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_Xs_1262_ = lean_ctor_get(v_X_1255_, 17);
lean_inc_ref(v_Xs_1262_);
v_Ys_1263_ = lean_ctor_get(v_X_1255_, 18);
lean_inc_ref(v_Ys_1263_);
v_iXYs_1264_ = lean_ctor_get(v_X_1255_, 19);
lean_inc(v_iXYs_1264_);
v_Bper_1265_ = lean_ctor_get(v_X_1255_, 25);
lean_inc_ref(v_Bper_1265_);
lean_dec_ref(v_X_1255_);
lean_inc_n(v_j_1257_, 2);
lean_inc_n(v_t_1256_, 2);
v___x_1266_ = lean_apply_2(v_Xs_1262_, v_t_1256_, v_j_1257_);
v___x_1267_ = lean_apply_2(v_Ys_1263_, v_t_1256_, v_j_1257_);
v___x_1268_ = lean_apply_2(v_iXYs_1264_, v_t_1256_, v_j_1257_);
v___x_1269_ = lean_apply_7(v_Bper_1265_, v___x_1266_, v___x_1267_, v___x_1268_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bj(lean_object* v_D_1270_, lean_object* v_X_1271_, lean_object* v_t_1272_, lean_object* v_j_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = lp_tree_Formalism_BasicNotions_ThetaX_Bj___redArg(v_X_1271_, v_t_1272_, v_j_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bj___boxed(lean_object* v_D_1279_, lean_object* v_X_1280_, lean_object* v_t_1281_, lean_object* v_j_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = lp_tree_Formalism_BasicNotions_ThetaX_Bj(v_D_1279_, v_X_1280_, v_t_1281_, v_j_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec_ref(v_D_1279_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_Bm(lean_object* v_D_1288_, lean_object* v_X_1289_, lean_object* v_t_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_R_1293_; lean_object* v_Xs_1294_; lean_object* v_Ys_1295_; lean_object* v_iYXm_1296_; lean_object* v_Btop_1297_; lean_object* v_m_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_R_1293_ = lean_ctor_get(v_D_1288_, 0);
lean_inc_ref(v_R_1293_);
lean_dec_ref(v_D_1288_);
v_Xs_1294_ = lean_ctor_get(v_X_1289_, 17);
lean_inc_ref(v_Xs_1294_);
v_Ys_1295_ = lean_ctor_get(v_X_1289_, 18);
lean_inc_ref(v_Ys_1295_);
v_iYXm_1296_ = lean_ctor_get(v_X_1289_, 20);
lean_inc(v_iYXm_1296_);
v_Btop_1297_ = lean_ctor_get(v_X_1289_, 26);
lean_inc_ref(v_Btop_1297_);
lean_dec_ref(v_X_1289_);
v_m_1298_ = lean_ctor_get(v_R_1293_, 2);
lean_inc_n(v_m_1298_, 2);
lean_dec_ref(v_R_1293_);
lean_inc_n(v_t_1290_, 2);
v___x_1299_ = lean_apply_2(v_Xs_1294_, v_t_1290_, v_m_1298_);
v___x_1300_ = lean_apply_2(v_Ys_1295_, v_t_1290_, v_m_1298_);
v___x_1301_ = lean_apply_1(v_iYXm_1296_, v_t_1290_);
v___x_1302_ = lean_apply_5(v_Btop_1297_, v___x_1299_, v___x_1300_, v___x_1301_, v_a_1291_, v_a_1292_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_parOf___lam__0(lean_object* v_X_1303_, lean_object* v_00_u03c4_1304_){
_start:
{
lean_object* v_infTy_1305_; lean_object* v_etaT_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_infTy_1305_ = lean_ctor_get(v_X_1303_, 10);
lean_inc_ref(v_infTy_1305_);
v_etaT_1306_ = lean_ctor_get(v_X_1303_, 12);
lean_inc(v_etaT_1306_);
lean_dec_ref(v_X_1303_);
v___x_1307_ = lean_apply_2(v_infTy_1305_, v_etaT_1306_, v_00_u03c4_1304_);
v___x_1308_ = l_Rat_neg(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_parOf(lean_object* v_D_1309_, lean_object* v_X_1310_, lean_object* v_w_1311_){
_start:
{
lean_object* v___f_1312_; lean_object* v___x_1313_; 
v___f_1312_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_ThetaX_parOf___lam__0), 2, 1);
lean_closure_set(v___f_1312_, 0, v_X_1310_);
v___x_1313_ = lp_tree_Formalism_BasicNotions_TH_TPar_ofWord___redArg(v_D_1309_, v_w_1311_, v___f_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg(lean_object* v_X_1314_, lean_object* v_00_u03bc_1315_, lean_object* v_s_1316_, lean_object* v_i_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lp_mathlib_Nat_instDecidablePredEven(v_i_1317_);
if (v___x_1318_ == 0)
{
lean_object* v_chrOf_1319_; lean_object* v___x_1320_; 
v_chrOf_1319_ = lean_ctor_get(v_X_1314_, 11);
lean_inc(v_chrOf_1319_);
lean_dec_ref(v_X_1314_);
v___x_1320_ = lean_apply_2(v_chrOf_1319_, v_00_u03bc_1315_, v_s_1316_);
return v___x_1320_;
}
else
{
lean_object* v_chrGrp_1321_; lean_object* v_chrOf_1322_; lean_object* v_etaT_1323_; lean_object* v_toMonoid_1324_; lean_object* v___x_1325_; lean_object* v_toMul_1326_; lean_object* v___x_1327_; lean_object* v_toInv_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_chrGrp_1321_ = lean_ctor_get(v_X_1314_, 9);
lean_inc_ref(v_chrGrp_1321_);
v_chrOf_1322_ = lean_ctor_get(v_X_1314_, 11);
lean_inc(v_chrOf_1322_);
v_etaT_1323_ = lean_ctor_get(v_X_1314_, 12);
lean_inc(v_etaT_1323_);
lean_dec_ref(v_X_1314_);
v_toMonoid_1324_ = lean_ctor_get(v_chrGrp_1321_, 0);
v___x_1325_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_1324_);
v_toMul_1326_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_toMul_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_chrGrp_1321_);
lean_dec_ref(v_chrGrp_1321_);
v_toInv_1328_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_toInv_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = lean_apply_2(v_chrOf_1322_, v_00_u03bc_1315_, v_s_1316_);
v___x_1330_ = lean_apply_1(v_toInv_1328_, v_etaT_1323_);
v___x_1331_ = lean_apply_2(v_toMul_1326_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg___boxed(lean_object* v_X_1332_, lean_object* v_00_u03bc_1333_, lean_object* v_s_1334_, lean_object* v_i_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg(v_X_1332_, v_00_u03bc_1333_, v_s_1334_, v_i_1335_);
lean_dec(v_i_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY(lean_object* v_D_1337_, lean_object* v_X_1338_, lean_object* v_00_u03bc_1339_, lean_object* v_s_1340_, lean_object* v_i_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg(v_X_1338_, v_00_u03bc_1339_, v_s_1340_, v_i_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_carY___boxed(lean_object* v_D_1343_, lean_object* v_X_1344_, lean_object* v_00_u03bc_1345_, lean_object* v_s_1346_, lean_object* v_i_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = lp_tree_Formalism_BasicNotions_ThetaX_carY(v_D_1343_, v_X_1344_, v_00_u03bc_1345_, v_s_1346_, v_i_1347_);
lean_dec(v_i_1347_);
lean_dec_ref(v_D_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_petY(lean_object* v_D_1349_, lean_object* v_X_1350_, lean_object* v_00_u03bc_1351_, lean_object* v_j_1352_, lean_object* v_F_1353_, lean_object* v_G_1354_){
_start:
{
lean_object* v_sp_1355_; lean_object* v_pet_1356_; lean_object* v_mY_1357_; lean_object* v_Y_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_re_1361_; lean_object* v_im_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_sp_1355_ = lean_ctor_get(v_D_1349_, 2);
lean_inc_ref(v_sp_1355_);
lean_dec_ref(v_D_1349_);
v_pet_1356_ = lean_ctor_get(v_X_1350_, 3);
lean_inc_ref(v_pet_1356_);
v_mY_1357_ = lean_ctor_get(v_X_1350_, 33);
lean_inc(v_mY_1357_);
lean_dec_ref(v_X_1350_);
v_Y_1358_ = lean_ctor_get(v_sp_1355_, 5);
lean_inc_ref(v_Y_1358_);
lean_dec_ref(v_sp_1355_);
lean_inc(v_j_1352_);
v___x_1359_ = lean_apply_2(v_mY_1357_, v_00_u03bc_1351_, v_j_1352_);
v___x_1360_ = lp_mathlib_Complex_ofReal(v___x_1359_);
v_re_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_re_1361_);
v_im_1362_ = lean_ctor_get(v___x_1360_, 1);
lean_inc(v_im_1362_);
lean_dec_ref(v___x_1360_);
v___x_1363_ = lean_apply_1(v_Y_1358_, v_j_1352_);
v___x_1364_ = lean_apply_3(v_pet_1356_, v___x_1363_, v_F_1353_, v_G_1354_);
v___x_1365_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_1361_, v_im_1362_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_dnY___lam__0(lean_object* v_th_1366_, lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v___x_1369_, lean_object* v___x_1370_, lean_object* v___x_1371_, lean_object* v_afMod_1372_, lean_object* v___x_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc_ref(v___x_1368_);
v___x_1375_ = lean_apply_6(v_th_1366_, v___x_1367_, v___x_1368_, v___x_1369_, v___x_1370_, v___x_1371_, v___y_1374_);
v___x_1376_ = lean_apply_3(v_afMod_1372_, v___x_1368_, v___x_1373_, v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ThetaX_dnY(lean_object* v_D_1377_, lean_object* v_X_1378_, lean_object* v_00_u03bc_1379_, lean_object* v_j_1380_){
_start:
{
lean_object* v_sp_1381_; lean_object* v_Y_1382_; lean_object* v_afMod_1383_; lean_object* v_th_1384_; lean_object* v_PhiY_1385_; lean_object* v_mY_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; 
v_sp_1381_ = lean_ctor_get(v_D_1377_, 2);
lean_inc_ref(v_sp_1381_);
lean_dec_ref(v_D_1377_);
v_Y_1382_ = lean_ctor_get(v_sp_1381_, 5);
lean_inc_ref_n(v_Y_1382_, 2);
lean_dec_ref(v_sp_1381_);
v_afMod_1383_ = lean_ctor_get(v_X_1378_, 1);
lean_inc(v_afMod_1383_);
v_th_1384_ = lean_ctor_get(v_X_1378_, 16);
lean_inc(v_th_1384_);
v_PhiY_1385_ = lean_ctor_get(v_X_1378_, 31);
lean_inc(v_PhiY_1385_);
v_mY_1386_ = lean_ctor_get(v_X_1378_, 33);
v___x_1387_ = lean_unsigned_to_nat(1u);
v___x_1388_ = lean_nat_add(v_j_1380_, v___x_1387_);
lean_inc_n(v___x_1388_, 3);
v___x_1389_ = lean_apply_1(v_Y_1382_, v___x_1388_);
lean_inc(v_j_1380_);
v___x_1390_ = lean_apply_1(v_Y_1382_, v_j_1380_);
lean_inc(v_mY_1386_);
lean_inc_n(v_00_u03bc_1379_, 3);
v___x_1391_ = lean_apply_2(v_mY_1386_, v_00_u03bc_1379_, v___x_1388_);
v___x_1392_ = lp_mathlib_Complex_ofReal(v___x_1391_);
lean_inc_ref(v_X_1378_);
v___x_1393_ = lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg(v_X_1378_, v_00_u03bc_1379_, v___x_1388_, v___x_1388_);
v___x_1394_ = lp_tree_Formalism_BasicNotions_ThetaX_carY___redArg(v_X_1378_, v_00_u03bc_1379_, v___x_1388_, v_j_1380_);
v___x_1395_ = lean_apply_2(v_PhiY_1385_, v_00_u03bc_1379_, v_j_1380_);
v___f_1396_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_ThetaX_dnY___lam__0), 9, 8);
lean_closure_set(v___f_1396_, 0, v_th_1384_);
lean_closure_set(v___f_1396_, 1, v___x_1389_);
lean_closure_set(v___f_1396_, 2, v___x_1390_);
lean_closure_set(v___f_1396_, 3, v___x_1393_);
lean_closure_set(v___f_1396_, 4, v___x_1394_);
lean_closure_set(v___f_1396_, 5, v___x_1395_);
lean_closure_set(v___f_1396_, 6, v_afMod_1383_);
lean_closure_set(v___f_1396_, 7, v___x_1392_);
return v___f_1396_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_FormalDegreeBessel_StatementG(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataTheta(uint8_t builtin) {
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
res = initialize_tree_Formalism_SatakeDualWeyl_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FormalDegreeBessel_StatementG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
