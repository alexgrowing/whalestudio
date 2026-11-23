// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.LocalRingCardinality.DataCoeff public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower public import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta public import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace public import Formalism.LocalToGlobal.Divisibility.Tuples public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_lamOf(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_wG(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_floor(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_rhoVec(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Fintype_card___at___00Formalism_L2_Col_Fields_f_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Fintype_card___at___00Formalism_L2_Col_Fields_f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_f(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_f___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_starRingEnd___at___00Formalism_L2_Col_Fields_sig_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_starRingEnd___at___00Formalism_L2_Col_Fields_sig_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_sig(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_sig___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___closed__0 = (const lean_object*)&lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___closed__0 = (const lean_object*)&lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_conjO(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_embBar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_Kq(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_Kq___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_embC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_ofQ___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_ofQ___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_ofQ___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__2___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__3(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_ofQ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_Col_ofQ___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_ofQ___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_ofQ___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_bAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_bAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_eAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_eAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_vb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_vb___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sgHC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sgQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sgTrue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_pOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_pOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_qOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_qOf___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_dV___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_dV___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_dV(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_dV___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aPlus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aPlus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aMinusRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aMinusRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamVQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamVQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamV(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_nuW___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_nuW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_nuW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgW___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgTrue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamV___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_aTop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_aTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_aTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_bTop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_bTop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_bTop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Fintype_card___at___00Formalism_L2_Col_Fields_f_spec__0(lean_object* v_X_1_){
_start:
{
lean_object* v_ftTau_2_; lean_object* v___x_3_; 
v_ftTau_2_ = lean_ctor_get(v_X_1_, 6);
v___x_3_ = l_List_lengthTR___redArg(v_ftTau_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Fintype_card___at___00Formalism_L2_Col_Fields_f_spec__0___boxed(lean_object* v_X_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Fintype_card___at___00Formalism_L2_Col_Fields_f_spec__0(v_X_4_);
lean_dec_ref(v_X_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_f(lean_object* v_X_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_tree_Fintype_card___at___00Formalism_L2_Col_Fields_f_spec__0(v_X_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_f___boxed(lean_object* v_X_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_L2_Col_Fields_f(v_X_8_);
lean_dec_ref(v_X_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_starRingEnd___at___00Formalism_L2_Col_Fields_sig_spec__0(lean_object* v_X_10_){
_start:
{
lean_object* v_starE_11_; 
v_starE_11_ = lean_ctor_get(v_X_10_, 4);
lean_inc(v_starE_11_);
return v_starE_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_starRingEnd___at___00Formalism_L2_Col_Fields_sig_spec__0___boxed(lean_object* v_X_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_starRingEnd___at___00Formalism_L2_Col_Fields_sig_spec__0(v_X_12_);
lean_dec_ref(v_X_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_sig(lean_object* v_X_14_){
_start:
{
lean_object* v_starE_15_; 
v_starE_15_ = lean_ctor_get(v_X_14_, 4);
lean_inc(v_starE_15_);
return v_starE_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_sig___boxed(lean_object* v_X_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_L2_Col_Fields_sig(v_X_16_);
lean_dec_ref(v_X_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__0(lean_object* v_X_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_integralClosure___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__0___boxed(lean_object* v_X_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_integralClosure___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__0(v_X_20_);
lean_dec_ref(v_X_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___lam__0(lean_object* v_self_22_){
_start:
{
lean_inc(v_self_22_);
return v_self_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___lam__0___boxed(lean_object* v_self_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___lam__0(v_self_23_);
lean_dec(v_self_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2(lean_object* v_X_26_, lean_object* v_s_27_){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = ((lean_object*)(lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___closed__0));
return v___f_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___boxed(lean_object* v_X_29_, lean_object* v_s_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2(v_X_29_, v_s_30_);
lean_dec_ref(v_X_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__1(lean_object* v_X_32_, lean_object* v_inst_33_, lean_object* v_s_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subsemiring_ofClass___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__1___boxed(lean_object* v_X_36_, lean_object* v_inst_37_, lean_object* v_s_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Subsemiring_ofClass___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__1(v_X_36_, v_inst_37_, v_s_38_);
lean_dec_ref(v_X_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0(lean_object* v_X_41_, lean_object* v_f_42_, lean_object* v_k_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_44_ = ((lean_object*)(lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___closed__0));
v___f_45_ = ((lean_object*)(lp_tree_Subsemiring_subtype___at___00NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0_spec__2___closed__0));
v___x_46_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_45_, v___f_44_, v_k_43_);
v___x_47_ = lean_apply_1(v_f_42_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___boxed(lean_object* v_X_48_, lean_object* v_f_49_, lean_object* v_k_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0(v_X_48_, v_f_49_, v_k_50_);
lean_dec_ref(v_X_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0(lean_object* v_X_52_, lean_object* v_f_53_){
_start:
{
lean_object* v___f_54_; 
v___f_54_ = lean_alloc_closure((void*)(lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_54_, 0, v_X_52_);
lean_closure_set(v___f_54_, 1, v_f_53_);
return v___f_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_conjO(lean_object* v_X_55_){
_start:
{
lean_object* v_starE_56_; lean_object* v___f_57_; 
v_starE_56_ = lean_ctor_get(v_X_55_, 4);
lean_inc(v_starE_56_);
v___f_57_ = lean_alloc_closure((void*)(lp_tree_NumberField_RingOfIntegers_mapRingHom___at___00Formalism_L2_Col_Fields_conjO_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_57_, 0, v_X_55_);
lean_closure_set(v___f_57_, 1, v_starE_56_);
return v___f_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_embBar(lean_object* v_X_58_, lean_object* v_00_u03c4_59_){
_start:
{
lean_object* v_starE_60_; lean_object* v_emb_61_; lean_object* v___x_62_; lean_object* v___f_63_; 
v_starE_60_ = lean_ctor_get(v_X_58_, 4);
lean_inc(v_starE_60_);
v_emb_61_ = lean_ctor_get(v_X_58_, 8);
lean_inc(v_emb_61_);
lean_dec_ref(v_X_58_);
v___x_62_ = lean_apply_1(v_emb_61_, v_00_u03c4_59_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_63_, 0, v_starE_60_);
lean_closure_set(v___f_63_, 1, v___x_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_Kq(lean_object* v_X_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_Kq___boxed(lean_object* v_X_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_Formalism_L2_Col_Fields_Kq(v_X_66_);
lean_dec_ref(v_X_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_embC(lean_object* v_X_68_, lean_object* v_00_u03c3_u2080_69_, lean_object* v_00_u03c4_70_){
_start:
{
lean_object* v_emb_71_; lean_object* v___x_72_; lean_object* v___f_73_; 
v_emb_71_ = lean_ctor_get(v_X_68_, 8);
lean_inc(v_emb_71_);
lean_dec_ref(v_X_68_);
v___x_72_ = lean_apply_1(v_emb_71_, v_00_u03c4_70_);
v___f_73_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_73_, 0, v___x_72_);
lean_closure_set(v___f_73_, 1, v_00_u03c3_u2080_69_);
return v___f_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty___lam__0(lean_object* v_toMonoid_74_, lean_object* v_x_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v_toOne_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v___x_77_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_74_);
v_toOne_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v___x_77_, 1);
lean_dec(v_unused_86_);
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_toOne_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
lean_inc(v_toOne_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v_toOne_78_);
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_toOne_78_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_toOne_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty___lam__0___boxed(lean_object* v_toMonoid_87_, lean_object* v_x_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_tree_Formalism_L2_Col_QDat_empty___lam__0(v_toMonoid_87_, v_x_88_, v___y_89_);
lean_dec_ref(v___y_89_);
lean_dec_ref(v_toMonoid_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty(lean_object* v_X_91_){
_start:
{
lean_object* v_fieldK_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_toSemiring_95_; lean_object* v_toMonoid_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___x_99_; 
v_fieldK_92_ = lean_ctor_get(v_X_91_, 2);
v___x_93_ = lp_mathlib_Field_toSemifield___redArg(v_fieldK_92_);
v___x_94_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_93_);
v_toSemiring_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_toSemiring_95_);
lean_dec_ref(v___x_94_);
v_toMonoid_96_ = lean_ctor_get(v_toSemiring_95_, 1);
lean_inc_ref(v_toMonoid_96_);
lean_dec_ref(v_toSemiring_95_);
v___x_97_ = lean_box(0);
v___f_98_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_QDat_empty___lam__0___boxed), 3, 1);
lean_closure_set(v___f_98_, 0, v_toMonoid_96_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___f_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_QDat_empty___boxed(lean_object* v_X_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Formalism_L2_Col_QDat_empty(v_X_100_);
lean_dec_ref(v_X_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0(lean_object* v_lam_102_, lean_object* v_c_103_, lean_object* v_i_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_apply_1(v_lam_102_, v_i_104_);
v___x_106_ = lean_int_add(v___x_105_, v_c_103_);
lean_dec(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed(lean_object* v_lam_107_, lean_object* v_c_108_, lean_object* v_i_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0(v_lam_107_, v_c_108_, v_i_109_);
lean_dec(v_c_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___redArg(lean_object* v_lam_111_, lean_object* v_c_112_){
_start:
{
lean_object* v___f_113_; 
v___f_113_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_113_, 0, v_lam_111_);
lean_closure_set(v___f_113_, 1, v_c_112_);
return v___f_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW(lean_object* v_N_114_, lean_object* v_lam_115_, lean_object* v_c_116_){
_start:
{
lean_object* v___f_117_; 
v___f_117_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_117_, 0, v_lam_115_);
lean_closure_set(v___f_117_, 1, v_c_116_);
return v___f_117_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_shiftW___boxed(lean_object* v_N_118_, lean_object* v_lam_119_, lean_object* v_c_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_Formalism_L2_Col_shiftW(v_N_118_, v_lam_119_, v_c_120_);
lean_dec(v_N_118_);
return v_res_121_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_ofQ___lam__0(lean_object* v_a_122_, lean_object* v_x_123_, lean_object* v_a_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_le(v_a_122_, v_a_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
lean_dec(v_a_124_);
lean_dec_ref(v_x_123_);
lean_dec(v_a_122_);
v___x_126_ = 1;
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
lean_inc_ref(v_x_123_);
v___x_127_ = lean_apply_1(v_x_123_, v_a_124_);
v___x_128_ = lean_apply_1(v_x_123_, v_a_122_);
v___x_129_ = l_Rat_instDecidableLe(v___x_127_, v___x_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__0___boxed(lean_object* v_a_130_, lean_object* v_x_131_, lean_object* v_a_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = lp_tree_Formalism_L2_Col_ofQ___lam__0(v_a_130_, v_x_131_, v_a_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_L2_Col_ofQ___lam__1(lean_object* v_x_135_, lean_object* v_N_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___f_138_; uint8_t v___x_139_; 
v___f_138_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_ofQ___lam__0___boxed), 3, 2);
lean_closure_set(v___f_138_, 0, v_a_137_);
lean_closure_set(v___f_138_, 1, v_x_135_);
v___x_139_ = l_Nat_decidableForallFin___redArg(v_N_136_, v___f_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__1___boxed(lean_object* v_x_140_, lean_object* v_N_141_, lean_object* v_a_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = lp_tree_Formalism_L2_Col_ofQ___lam__1(v_x_140_, v_N_141_, v_a_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_ofQ___lam__2___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__2(lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&lp_tree_Formalism_L2_Col_ofQ___lam__2___closed__0, &lp_tree_Formalism_L2_Col_ofQ___lam__2___closed__0_once, _init_lp_tree_Formalism_L2_Col_ofQ___lam__2___closed__0);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__2___boxed(lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = lp_tree_Formalism_L2_Col_ofQ___lam__2(v_x_149_);
lean_dec(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ___lam__3(lean_object* v_x_151_, lean_object* v_i_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_apply_1(v_x_151_, v_i_152_);
v___x_154_ = l_Rat_floor(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ofQ(lean_object* v_N_156_, lean_object* v_x_157_){
_start:
{
lean_object* v___f_158_; uint8_t v___x_159_; 
lean_inc(v_N_156_);
lean_inc_ref(v_x_157_);
v___f_158_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_ofQ___lam__1___boxed), 3, 2);
lean_closure_set(v___f_158_, 0, v_x_157_);
lean_closure_set(v___f_158_, 1, v_N_156_);
v___x_159_ = l_Nat_decidableForallFin___redArg(v_N_156_, v___f_158_);
if (v___x_159_ == 0)
{
lean_object* v___f_160_; 
lean_dec_ref(v_x_157_);
v___f_160_ = ((lean_object*)(lp_tree_Formalism_L2_Col_ofQ___closed__0));
return v___f_160_;
}
else
{
lean_object* v___f_161_; 
v___f_161_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_ofQ___lam__3), 2, 1);
lean_closure_set(v___f_161_, 0, v_x_157_);
return v___f_161_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of___redArg(lean_object* v_P_162_){
_start:
{
lean_object* v_v_163_; lean_object* v_b_164_; lean_object* v_e_165_; lean_object* v___x_166_; 
v_v_163_ = lean_ctor_get(v_P_162_, 1);
v_b_164_ = lean_ctor_get(v_P_162_, 2);
v_e_165_ = lean_ctor_get(v_P_162_, 3);
lean_inc_ref(v_e_165_);
lean_inc_ref(v_b_164_);
lean_inc_ref(v_v_163_);
v___x_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_166_, 0, v_v_163_);
lean_ctor_set(v___x_166_, 1, v_b_164_);
lean_ctor_set(v___x_166_, 2, v_e_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of___redArg___boxed(lean_object* v_P_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_tree_Formalism_L2_Col_RowPar_of___redArg(v_P_167_);
lean_dec_ref(v_P_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of(lean_object* v_R_169_, lean_object* v_P_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lp_tree_Formalism_L2_Col_RowPar_of___redArg(v_P_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_of___boxed(lean_object* v_R_172_, lean_object* v_P_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_tree_Formalism_L2_Col_RowPar_of(v_R_172_, v_P_173_);
lean_dec_ref(v_P_173_);
lean_dec_ref(v_R_172_);
return v_res_174_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_bAt(lean_object* v_R_177_, lean_object* v_S_178_, lean_object* v_n_179_){
_start:
{
lean_object* v_m_180_; uint8_t v___x_181_; 
v_m_180_ = lean_ctor_get(v_R_177_, 2);
v___x_181_ = lean_nat_dec_lt(v_n_179_, v_m_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v_n_179_);
lean_dec_ref(v_S_178_);
v___x_182_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0, &lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0);
return v___x_182_;
}
else
{
lean_object* v_b_183_; lean_object* v___x_184_; 
v_b_183_ = lean_ctor_get(v_S_178_, 1);
lean_inc_ref(v_b_183_);
lean_dec_ref(v_S_178_);
v___x_184_ = lean_apply_1(v_b_183_, v_n_179_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_bAt___boxed(lean_object* v_R_185_, lean_object* v_S_186_, lean_object* v_n_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_tree_Formalism_L2_Col_RowPar_bAt(v_R_185_, v_S_186_, v_n_187_);
lean_dec_ref(v_R_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_eAt(lean_object* v_R_189_, lean_object* v_S_190_, lean_object* v_n_191_){
_start:
{
lean_object* v_m_192_; uint8_t v___x_193_; 
v_m_192_ = lean_ctor_get(v_R_189_, 2);
v___x_193_ = lean_nat_dec_lt(v_n_191_, v_m_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec(v_n_191_);
lean_dec_ref(v_S_190_);
v___x_194_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0, &lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0);
return v___x_194_;
}
else
{
lean_object* v_e_195_; lean_object* v___x_196_; 
v_e_195_ = lean_ctor_get(v_S_190_, 2);
lean_inc_ref(v_e_195_);
lean_dec_ref(v_S_190_);
v___x_196_ = lean_apply_1(v_e_195_, v_n_191_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_eAt___boxed(lean_object* v_R_197_, lean_object* v_S_198_, lean_object* v_n_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_197_, v_S_198_, v_n_199_);
lean_dec_ref(v_R_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_vb(lean_object* v_R_201_, lean_object* v_S_202_, lean_object* v_n_203_){
_start:
{
lean_object* v_k_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_k_204_ = lean_ctor_get(v_R_201_, 1);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_sub(v_k_204_, v___x_205_);
v___x_207_ = lean_nat_dec_lt(v_n_203_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_nat_sub(v_n_203_, v___x_206_);
lean_dec(v___x_206_);
lean_dec(v_n_203_);
v___x_209_ = lp_tree_Formalism_L2_Col_RowPar_bAt(v_R_201_, v_S_202_, v___x_208_);
v___x_210_ = l_Rat_neg(v___x_209_);
return v___x_210_;
}
else
{
lean_object* v_v_211_; lean_object* v___x_212_; 
lean_dec(v___x_206_);
v_v_211_ = lean_ctor_get(v_S_202_, 0);
lean_inc_ref(v_v_211_);
lean_dec_ref(v_S_202_);
v___x_212_ = lean_apply_1(v_v_211_, v_n_203_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_vb___boxed(lean_object* v_R_213_, lean_object* v_S_214_, lean_object* v_n_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_tree_Formalism_L2_Col_RowPar_vb(v_R_213_, v_S_214_, v_n_215_);
lean_dec_ref(v_R_213_);
return v_res_216_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sgHC(lean_object* v_R_221_, lean_object* v_S_222_, lean_object* v_n_223_){
_start:
{
lean_object* v_k_224_; lean_object* v_m_225_; lean_object* v_t_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_k_224_ = lean_ctor_get(v_R_221_, 1);
v_m_225_ = lean_ctor_get(v_R_221_, 2);
v_t_226_ = lean_ctor_get(v_R_221_, 3);
lean_inc(v_m_225_);
v___x_227_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_m_225_);
lean_inc(v_t_226_);
v___x_228_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_226_);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0);
lean_inc_ref(v___x_228_);
v___x_231_ = l_Rat_add(v___x_228_, v___x_230_);
v___x_232_ = l_Rat_mul(v___x_227_, v___x_231_);
lean_dec_ref(v___x_227_);
v___x_233_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1);
v___x_234_ = l_Rat_div(v___x_232_, v___x_233_);
lean_dec_ref(v___x_232_);
v___x_235_ = lean_nat_sub(v_k_224_, v___x_229_);
v___x_236_ = lean_nat_dec_lt(v_n_223_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_237_ = lean_nat_sub(v_n_223_, v___x_235_);
lean_dec(v___x_235_);
lean_dec(v_n_223_);
v___x_238_ = lean_nat_add(v_t_226_, v___x_229_);
v___x_239_ = lean_nat_mod(v___x_237_, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_242_ = lean_nat_div(v___x_237_, v___x_238_);
lean_dec(v___x_238_);
lean_dec(v___x_237_);
v___x_243_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_221_, v_S_222_, v___x_242_);
lean_dec_ref(v_R_221_);
v___x_244_ = l_Rat_neg(v___x_243_);
v___x_245_ = l_Rat_sub(v___x_228_, v___x_230_);
v___x_246_ = l_Rat_div(v___x_245_, v___x_233_);
lean_dec_ref(v___x_245_);
v___x_247_ = l_Rat_add(v___x_244_, v___x_246_);
v___x_248_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_239_);
v___x_249_ = l_Rat_sub(v___x_248_, v___x_230_);
v___x_250_ = l_Rat_sub(v___x_247_, v___x_249_);
v___x_251_ = l_Rat_add(v___x_234_, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_239_);
lean_dec_ref(v___x_228_);
v___x_252_ = lean_nat_div(v___x_237_, v___x_238_);
lean_dec(v___x_238_);
lean_dec(v___x_237_);
v___x_253_ = lp_tree_Formalism_L2_Col_RowPar_bAt(v_R_221_, v_S_222_, v___x_252_);
lean_dec_ref(v_R_221_);
v___x_254_ = l_Rat_neg(v___x_253_);
v___x_255_ = l_Rat_add(v___x_234_, v___x_254_);
return v___x_255_;
}
}
else
{
lean_object* v_v_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_235_);
lean_dec_ref(v___x_228_);
lean_dec_ref(v_R_221_);
v_v_256_ = lean_ctor_get(v_S_222_, 0);
lean_inc_ref(v_v_256_);
lean_dec_ref(v_S_222_);
v___x_257_ = lean_apply_1(v_v_256_, v_n_223_);
v___x_258_ = l_Rat_add(v___x_234_, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sgQ(lean_object* v_R_259_, lean_object* v_S_260_, lean_object* v_i_261_){
_start:
{
lean_object* v_m_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_m_262_ = lean_ctor_get(v_R_259_, 2);
lean_inc(v_m_262_);
lean_inc(v_i_261_);
lean_inc_ref(v_R_259_);
v___x_263_ = lp_tree_Formalism_L2_Col_RowPar_sgHC(v_R_259_, v_S_260_, v_i_261_);
v___x_264_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_259_, v_m_262_);
lean_dec(v_m_262_);
lean_dec_ref(v_R_259_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_sub(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
v___x_267_ = lp_tree_Formalism_BasicNotions_rhoVec(v___x_266_, v_i_261_);
v___x_268_ = l_Rat_sub(v___x_263_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sg(lean_object* v_R_269_, lean_object* v_S_270_){
_start:
{
lean_object* v_m_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_m_271_ = lean_ctor_get(v_R_269_, 2);
v___x_272_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_269_, v_m_271_);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_sub(v___x_272_, v___x_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_RowPar_sgQ), 3, 2);
lean_closure_set(v___x_275_, 0, v_R_269_);
lean_closure_set(v___x_275_, 1, v_S_270_);
v___x_276_ = lp_tree_Formalism_L2_Col_ofQ(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sgTrue(lean_object* v_R_277_, lean_object* v_S_278_){
_start:
{
lean_object* v_m_279_; lean_object* v_t_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___f_289_; 
v_m_279_ = lean_ctor_get(v_R_277_, 2);
lean_inc(v_m_279_);
v_t_280_ = lean_ctor_get(v_R_277_, 3);
lean_inc(v_t_280_);
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lp_tree_Formalism_L2_Col_RowPar_sg(v_R_277_, v_S_278_);
v___x_283_ = lean_nat_to_int(v_m_279_);
v___x_284_ = lean_nat_add(v_t_280_, v___x_281_);
lean_dec(v_t_280_);
v___x_285_ = lean_nat_shiftr(v___x_284_, v___x_281_);
lean_dec(v___x_284_);
v___x_286_ = lean_nat_to_int(v___x_285_);
v___x_287_ = lean_int_mul(v___x_283_, v___x_286_);
lean_dec(v___x_286_);
lean_dec(v___x_283_);
v___x_288_ = lean_int_neg(v___x_287_);
lean_dec(v___x_287_);
v___f_289_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_289_, 0, v___x_282_);
lean_closure_set(v___f_289_, 1, v___x_288_);
return v___f_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_pOf(lean_object* v_R_290_, lean_object* v_j_291_){
_start:
{
lean_object* v_k_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_k_292_ = lean_ctor_get(v_R_290_, 1);
v___x_293_ = lean_nat_add(v_k_292_, v_j_291_);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_sub(v___x_293_, v___x_294_);
lean_dec(v___x_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_pOf___boxed(lean_object* v_R_296_, lean_object* v_j_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = lp_tree_Formalism_L2_Col_RowPar_pOf(v_R_296_, v_j_297_);
lean_dec(v_j_297_);
lean_dec_ref(v_R_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_qOf(lean_object* v_R_299_, lean_object* v_j_300_){
_start:
{
lean_object* v_m_301_; lean_object* v___x_302_; 
v_m_301_ = lean_ctor_get(v_R_299_, 2);
v___x_302_ = lean_nat_sub(v_m_301_, v_j_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_qOf___boxed(lean_object* v_R_303_, lean_object* v_j_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = lp_tree_Formalism_L2_Col_RowPar_qOf(v_R_303_, v_j_304_);
lean_dec(v_j_304_);
lean_dec_ref(v_R_303_);
return v_res_305_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_dV___closed__0(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1);
v___x_307_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0);
v___x_308_ = l_Rat_div(v___x_307_, v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_dV(lean_object* v_R_309_, lean_object* v_S_310_, lean_object* v_j_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_312_ = lp_tree_Formalism_L2_Col_RowPar_pOf(v_R_309_, v_j_311_);
v___x_313_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_312_);
v___x_314_ = lp_tree_Formalism_L2_Col_RowPar_qOf(v_R_309_, v_j_311_);
v___x_315_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_314_);
v___x_316_ = l_Rat_sub(v___x_313_, v___x_315_);
v___x_317_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1);
v___x_318_ = l_Rat_div(v___x_316_, v___x_317_);
lean_dec_ref(v___x_316_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_sub(v_j_311_, v___x_319_);
v___x_321_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_309_, v_S_310_, v___x_320_);
v___x_322_ = l_Rat_sub(v___x_318_, v___x_321_);
v___x_323_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_dV___closed__0, &lp_tree_Formalism_L2_Col_RowPar_dV___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_dV___closed__0);
v___x_324_ = l_Rat_sub(v___x_322_, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_dV___boxed(lean_object* v_R_325_, lean_object* v_S_326_, lean_object* v_j_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = lp_tree_Formalism_L2_Col_RowPar_dV(v_R_325_, v_S_326_, v_j_327_);
lean_dec(v_j_327_);
lean_dec_ref(v_R_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aPlus(lean_object* v_R_329_, lean_object* v_S_330_, lean_object* v_j_331_, lean_object* v_i_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_sub(v_i_332_, v___x_333_);
lean_inc_ref(v_S_330_);
v___x_335_ = lp_tree_Formalism_L2_Col_RowPar_vb(v_R_329_, v_S_330_, v___x_334_);
v___x_336_ = lean_nat_sub(v_j_331_, v___x_333_);
v___x_337_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_329_, v_S_330_, v___x_336_);
v___x_338_ = l_Rat_add(v___x_335_, v___x_337_);
v___x_339_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_329_);
v___x_340_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_339_);
v___x_341_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0);
v___x_342_ = l_Rat_add(v___x_340_, v___x_341_);
v___x_343_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1);
v___x_344_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_332_);
v___x_345_ = l_Rat_mul(v___x_343_, v___x_344_);
v___x_346_ = l_Rat_sub(v___x_342_, v___x_345_);
v___x_347_ = l_Rat_div(v___x_346_, v___x_343_);
lean_dec_ref(v___x_346_);
v___x_348_ = l_Rat_sub(v___x_338_, v___x_347_);
v___x_349_ = lp_tree_Formalism_L2_Col_RowPar_pOf(v_R_329_, v_j_331_);
v___x_350_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_349_);
v___x_351_ = lp_tree_Formalism_L2_Col_RowPar_qOf(v_R_329_, v_j_331_);
v___x_352_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_351_);
v___x_353_ = l_Rat_sub(v___x_350_, v___x_352_);
v___x_354_ = l_Rat_div(v___x_353_, v___x_343_);
lean_dec_ref(v___x_353_);
v___x_355_ = l_Rat_sub(v___x_348_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aPlus___boxed(lean_object* v_R_356_, lean_object* v_S_357_, lean_object* v_j_358_, lean_object* v_i_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = lp_tree_Formalism_L2_Col_RowPar_aPlus(v_R_356_, v_S_357_, v_j_358_, v_i_359_);
lean_dec(v_j_358_);
lean_dec_ref(v_R_356_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aMinusRev(lean_object* v_R_361_, lean_object* v_S_362_, lean_object* v_j_363_, lean_object* v_c_364_){
_start:
{
lean_object* v_t_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_t_365_ = lean_ctor_get(v_R_361_, 3);
lean_inc(v_t_365_);
v___x_366_ = lean_nat_add(v_j_363_, v_c_364_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_sub(v___x_366_, v___x_367_);
lean_dec(v___x_366_);
lean_inc_ref(v_S_362_);
v___x_369_ = lp_tree_Formalism_L2_Col_RowPar_bAt(v_R_361_, v_S_362_, v___x_368_);
v___x_370_ = lean_nat_sub(v_j_363_, v___x_367_);
v___x_371_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_361_, v_S_362_, v___x_370_);
lean_dec_ref(v_R_361_);
v___x_372_ = l_Rat_sub(v___x_369_, v___x_371_);
v___x_373_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__0);
v___x_374_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_365_);
v___x_375_ = l_Rat_sub(v___x_373_, v___x_374_);
v___x_376_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sgHC___closed__1);
v___x_377_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_c_364_);
v___x_378_ = l_Rat_mul(v___x_376_, v___x_377_);
v___x_379_ = l_Rat_sub(v___x_375_, v___x_378_);
v___x_380_ = l_Rat_div(v___x_379_, v___x_376_);
lean_dec_ref(v___x_379_);
v___x_381_ = l_Rat_add(v___x_372_, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_aMinusRev___boxed(lean_object* v_R_382_, lean_object* v_S_383_, lean_object* v_j_384_, lean_object* v_c_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = lp_tree_Formalism_L2_Col_RowPar_aMinusRev(v_R_382_, v_S_383_, v_j_384_, v_c_385_);
lean_dec(v_j_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamVQ(lean_object* v_R_387_, lean_object* v_S_388_, lean_object* v_j_389_, lean_object* v_i_390_){
_start:
{
lean_object* v___y_392_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lp_tree_Formalism_L2_Col_RowPar_pOf(v_R_387_, v_j_389_);
v___x_396_ = lean_nat_dec_lt(v_i_390_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v_t_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_t_397_ = lean_ctor_get(v_R_387_, 3);
v___x_398_ = lean_nat_add(v___x_395_, v_t_397_);
lean_dec(v___x_395_);
v___x_399_ = lean_nat_dec_lt(v_i_390_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_400_ = lean_nat_sub(v_i_390_, v___x_398_);
lean_dec(v___x_398_);
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_nat_add(v___x_400_, v___x_401_);
lean_dec(v___x_400_);
lean_inc_ref(v_S_388_);
lean_inc_ref(v_R_387_);
v___x_403_ = lp_tree_Formalism_L2_Col_RowPar_aMinusRev(v_R_387_, v_S_388_, v_j_389_, v___x_402_);
v___x_404_ = l_Rat_neg(v___x_403_);
v___y_392_ = v___x_404_;
goto v___jp_391_;
}
else
{
lean_object* v___x_405_; 
lean_dec(v___x_398_);
v___x_405_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0, &lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_bAt___closed__0);
v___y_392_ = v___x_405_;
goto v___jp_391_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec(v___x_395_);
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_add(v_i_390_, v___x_406_);
lean_inc_ref(v_S_388_);
v___x_408_ = lp_tree_Formalism_L2_Col_RowPar_aPlus(v_R_387_, v_S_388_, v_j_389_, v___x_407_);
v___y_392_ = v___x_408_;
goto v___jp_391_;
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lp_tree_Formalism_L2_Col_RowPar_dV(v_R_387_, v_S_388_, v_j_389_);
lean_dec_ref(v_R_387_);
v___x_394_ = l_Rat_add(v___y_392_, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamVQ___boxed(lean_object* v_R_409_, lean_object* v_S_410_, lean_object* v_j_411_, lean_object* v_i_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = lp_tree_Formalism_L2_Col_RowPar_lamVQ(v_R_409_, v_S_410_, v_j_411_, v_i_412_);
lean_dec(v_i_412_);
lean_dec(v_j_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamV(lean_object* v_R_414_, lean_object* v_S_415_, lean_object* v_j_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_414_);
v___x_418_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_RowPar_lamVQ___boxed), 4, 3);
lean_closure_set(v___x_418_, 0, v_R_414_);
lean_closure_set(v___x_418_, 1, v_S_415_);
lean_closure_set(v___x_418_, 2, v_j_416_);
v___x_419_ = lp_tree_Formalism_L2_Col_ofQ(v___x_417_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN___redArg(lean_object* v_R_420_, lean_object* v_W_421_, lean_object* v_u_422_, lean_object* v_j_423_, lean_object* v_00_u03c4_424_){
_start:
{
lean_object* v_hc_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_hc_425_ = lean_ctor_get(v_W_421_, 1);
lean_inc_ref(v_hc_425_);
lean_dec_ref(v_W_421_);
v___x_426_ = lean_apply_2(v_hc_425_, v_u_422_, v_00_u03c4_424_);
v___x_427_ = lp_tree_Formalism_BasicNotions_Examples_u2082_lamOf(v_R_420_, v___x_426_, v_j_423_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN___redArg___boxed(lean_object* v_R_428_, lean_object* v_W_429_, lean_object* v_u_430_, lean_object* v_j_431_, lean_object* v_00_u03c4_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_428_, v_W_429_, v_u_430_, v_j_431_, v_00_u03c4_432_);
lean_dec(v_j_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN(lean_object* v_X_434_, lean_object* v_Word_435_, lean_object* v_R_436_, lean_object* v_W_437_, lean_object* v_u_438_, lean_object* v_j_439_, lean_object* v_00_u03c4_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_436_, v_W_437_, v_u_438_, v_j_439_, v_00_u03c4_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamN___boxed(lean_object* v_X_442_, lean_object* v_Word_443_, lean_object* v_R_444_, lean_object* v_W_445_, lean_object* v_u_446_, lean_object* v_j_447_, lean_object* v_00_u03c4_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = lp_tree_Formalism_L2_Col_Wts_lamN(v_X_442_, v_Word_443_, v_R_444_, v_W_445_, v_u_446_, v_j_447_, v_00_u03c4_448_);
lean_dec(v_j_447_);
lean_dec_ref(v_X_442_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamTrue___redArg(lean_object* v_R_450_, lean_object* v_W_451_, lean_object* v_u_452_, lean_object* v_j_453_, lean_object* v_00_u03c4_454_){
_start:
{
lean_object* v_t_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___f_464_; 
v_t_455_ = lean_ctor_get(v_R_450_, 3);
lean_inc(v_t_455_);
v___x_456_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_450_, v_W_451_, v_u_452_, v_j_453_, v_00_u03c4_454_);
v___x_457_ = lean_nat_to_int(v_j_453_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v_t_455_, v___x_458_);
lean_dec(v_t_455_);
v___x_460_ = lean_nat_shiftr(v___x_459_, v___x_458_);
lean_dec(v___x_459_);
v___x_461_ = lean_nat_to_int(v___x_460_);
v___x_462_ = lean_int_mul(v___x_457_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v___x_457_);
v___x_463_ = lean_int_neg(v___x_462_);
lean_dec(v___x_462_);
v___f_464_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_464_, 0, v___x_456_);
lean_closure_set(v___f_464_, 1, v___x_463_);
return v___f_464_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamTrue(lean_object* v_X_465_, lean_object* v_Word_466_, lean_object* v_R_467_, lean_object* v_W_468_, lean_object* v_u_469_, lean_object* v_j_470_, lean_object* v_00_u03c4_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lp_tree_Formalism_L2_Col_Wts_lamTrue___redArg(v_R_467_, v_W_468_, v_u_469_, v_j_470_, v_00_u03c4_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamTrue___boxed(lean_object* v_X_473_, lean_object* v_Word_474_, lean_object* v_R_475_, lean_object* v_W_476_, lean_object* v_u_477_, lean_object* v_j_478_, lean_object* v_00_u03c4_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = lp_tree_Formalism_L2_Col_Wts_lamTrue(v_X_473_, v_Word_474_, v_R_475_, v_W_476_, v_u_477_, v_j_478_, v_00_u03c4_479_);
lean_dec_ref(v_X_473_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_nuW___redArg(lean_object* v_R_481_, lean_object* v_W_482_, lean_object* v_u_483_, lean_object* v_j_484_, lean_object* v_00_u03c4_485_){
_start:
{
lean_object* v_hc_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___f_495_; 
v_hc_486_ = lean_ctor_get(v_W_482_, 1);
lean_inc_ref(v_hc_486_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_sub(v_j_484_, v___x_487_);
lean_inc(v_00_u03c4_485_);
lean_inc(v_u_483_);
lean_inc_ref(v_R_481_);
v___x_489_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_481_, v_W_482_, v_u_483_, v___x_488_, v_00_u03c4_485_);
v___x_490_ = lean_apply_2(v_hc_486_, v_u_483_, v_00_u03c4_485_);
v___x_491_ = lp_tree_Formalism_L2_Col_RowPar_of___redArg(v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_481_, v___x_491_, v___x_488_);
v___x_493_ = lp_tree_Formalism_BasicNotions_wG(v_R_481_, v___x_492_, v_j_484_);
v___x_494_ = l_Rat_floor(v___x_493_);
v___f_495_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_shiftW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_495_, 0, v___x_489_);
lean_closure_set(v___f_495_, 1, v___x_494_);
return v___f_495_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_nuW(lean_object* v_X_496_, lean_object* v_Word_497_, lean_object* v_R_498_, lean_object* v_W_499_, lean_object* v_u_500_, lean_object* v_j_501_, lean_object* v_00_u03c4_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lp_tree_Formalism_L2_Col_Wts_nuW___redArg(v_R_498_, v_W_499_, v_u_500_, v_j_501_, v_00_u03c4_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_nuW___boxed(lean_object* v_X_504_, lean_object* v_Word_505_, lean_object* v_R_506_, lean_object* v_W_507_, lean_object* v_u_508_, lean_object* v_j_509_, lean_object* v_00_u03c4_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = lp_tree_Formalism_L2_Col_Wts_nuW(v_X_504_, v_Word_505_, v_R_506_, v_W_507_, v_u_508_, v_j_509_, v_00_u03c4_510_);
lean_dec_ref(v_X_504_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgW___redArg(lean_object* v_R_512_, lean_object* v_W_513_, lean_object* v_00_u03c4_514_){
_start:
{
lean_object* v_row_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_row_515_ = lean_ctor_get(v_W_513_, 0);
lean_inc_ref(v_row_515_);
lean_dec_ref(v_W_513_);
v___x_516_ = lean_apply_1(v_row_515_, v_00_u03c4_514_);
v___x_517_ = lp_tree_Formalism_L2_Col_RowPar_sg(v_R_512_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgW(lean_object* v_X_518_, lean_object* v_Word_519_, lean_object* v_R_520_, lean_object* v_W_521_, lean_object* v_00_u03c4_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lp_tree_Formalism_L2_Col_Wts_sgW___redArg(v_R_520_, v_W_521_, v_00_u03c4_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgW___boxed(lean_object* v_X_524_, lean_object* v_Word_525_, lean_object* v_R_526_, lean_object* v_W_527_, lean_object* v_00_u03c4_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = lp_tree_Formalism_L2_Col_Wts_sgW(v_X_524_, v_Word_525_, v_R_526_, v_W_527_, v_00_u03c4_528_);
lean_dec_ref(v_X_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgTrue___redArg(lean_object* v_R_530_, lean_object* v_W_531_, lean_object* v_00_u03c4_532_){
_start:
{
lean_object* v_row_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_row_533_ = lean_ctor_get(v_W_531_, 0);
lean_inc_ref(v_row_533_);
lean_dec_ref(v_W_531_);
v___x_534_ = lean_apply_1(v_row_533_, v_00_u03c4_532_);
v___x_535_ = lp_tree_Formalism_L2_Col_RowPar_sgTrue(v_R_530_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgTrue(lean_object* v_X_536_, lean_object* v_Word_537_, lean_object* v_R_538_, lean_object* v_W_539_, lean_object* v_00_u03c4_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lp_tree_Formalism_L2_Col_Wts_sgTrue___redArg(v_R_538_, v_W_539_, v_00_u03c4_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_sgTrue___boxed(lean_object* v_X_542_, lean_object* v_Word_543_, lean_object* v_R_544_, lean_object* v_W_545_, lean_object* v_00_u03c4_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = lp_tree_Formalism_L2_Col_Wts_sgTrue(v_X_542_, v_Word_543_, v_R_544_, v_W_545_, v_00_u03c4_546_);
lean_dec_ref(v_X_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamV___redArg(lean_object* v_R_548_, lean_object* v_W_549_, lean_object* v_j_550_, lean_object* v_00_u03c4_551_){
_start:
{
lean_object* v_row_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_row_552_ = lean_ctor_get(v_W_549_, 0);
lean_inc_ref(v_row_552_);
lean_dec_ref(v_W_549_);
v___x_553_ = lean_apply_1(v_row_552_, v_00_u03c4_551_);
v___x_554_ = lp_tree_Formalism_L2_Col_RowPar_lamV(v_R_548_, v___x_553_, v_j_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamV(lean_object* v_X_555_, lean_object* v_Word_556_, lean_object* v_R_557_, lean_object* v_W_558_, lean_object* v_j_559_, lean_object* v_00_u03c4_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lp_tree_Formalism_L2_Col_Wts_lamV___redArg(v_R_557_, v_W_558_, v_j_559_, v_00_u03c4_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamV___boxed(lean_object* v_X_562_, lean_object* v_Word_563_, lean_object* v_R_564_, lean_object* v_W_565_, lean_object* v_j_566_, lean_object* v_00_u03c4_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = lp_tree_Formalism_L2_Col_Wts_lamV(v_X_562_, v_Word_563_, v_R_564_, v_W_565_, v_j_566_, v_00_u03c4_567_);
lean_dec_ref(v_X_562_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_aTop___redArg(lean_object* v_R_569_, lean_object* v_W_570_, lean_object* v_u_571_, lean_object* v_00_u03c4_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_11__overap_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_11__overap_574_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_569_, v_W_570_, v_u_571_, v___x_573_, v_00_u03c4_572_);
v___x_575_ = lean_apply_1(v___x_11__overap_574_, v___x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_aTop(lean_object* v_X_576_, lean_object* v_Word_577_, lean_object* v_R_578_, lean_object* v_W_579_, lean_object* v_u_580_, lean_object* v_00_u03c4_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lp_tree_Formalism_L2_Col_Wts_aTop___redArg(v_R_578_, v_W_579_, v_u_580_, v_00_u03c4_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_aTop___boxed(lean_object* v_X_583_, lean_object* v_Word_584_, lean_object* v_R_585_, lean_object* v_W_586_, lean_object* v_u_587_, lean_object* v_00_u03c4_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = lp_tree_Formalism_L2_Col_Wts_aTop(v_X_583_, v_Word_584_, v_R_585_, v_W_586_, v_u_587_, v_00_u03c4_588_);
lean_dec_ref(v_X_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_bTop___redArg(lean_object* v_R_590_, lean_object* v_W_591_, lean_object* v_u_592_, lean_object* v_00_u03c4_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_590_, v___x_594_);
v___x_596_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_590_, v_W_591_, v_u_592_, v___x_594_, v_00_u03c4_593_);
v___x_597_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v___x_595_, v___x_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_int_neg(v___x_597_);
lean_dec(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_bTop(lean_object* v_X_599_, lean_object* v_Word_600_, lean_object* v_R_601_, lean_object* v_W_602_, lean_object* v_u_603_, lean_object* v_00_u03c4_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lp_tree_Formalism_L2_Col_Wts_bTop___redArg(v_R_601_, v_W_602_, v_u_603_, v_00_u03c4_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_bTop___boxed(lean_object* v_X_606_, lean_object* v_Word_607_, lean_object* v_R_608_, lean_object* v_W_609_, lean_object* v_u_610_, lean_object* v_00_u03c4_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = lp_tree_Formalism_L2_Col_Wts_bTop(v_X_606_, v_Word_607_, v_R_608_, v_W_609_, v_u_610_, v_00_u03c4_611_);
lean_dec_ref(v_X_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__0(lean_object* v_R_613_, lean_object* v_W_614_, lean_object* v_00_u03c4_615_, lean_object* v_i_616_){
_start:
{
lean_object* v___x_58__overap_617_; lean_object* v___x_618_; 
v___x_58__overap_617_ = lp_tree_Formalism_L2_Col_Wts_sgW___redArg(v_R_613_, v_W_614_, v_00_u03c4_615_);
v___x_618_ = lean_apply_1(v___x_58__overap_617_, v_i_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__1(lean_object* v_R_619_, lean_object* v_W_620_, lean_object* v_u_621_, lean_object* v_m_622_, lean_object* v_00_u03c4_623_, lean_object* v_i_624_){
_start:
{
lean_object* v___x_59__overap_625_; lean_object* v___x_626_; 
v___x_59__overap_625_ = lp_tree_Formalism_L2_Col_Wts_lamN___redArg(v_R_619_, v_W_620_, v_u_621_, v_m_622_, v_00_u03c4_623_);
v___x_626_ = lean_apply_1(v___x_59__overap_625_, v_i_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__1___boxed(lean_object* v_R_627_, lean_object* v_W_628_, lean_object* v_u_629_, lean_object* v_m_630_, lean_object* v_00_u03c4_631_, lean_object* v_i_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__1(v_R_627_, v_W_628_, v_u_629_, v_m_630_, v_00_u03c4_631_, v_i_632_);
lean_dec(v_m_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___redArg(lean_object* v_R_634_, lean_object* v_W_635_, lean_object* v_u_636_, lean_object* v_00_u03c4_637_){
_start:
{
lean_object* v_m_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_m_638_ = lean_ctor_get(v_R_634_, 2);
lean_inc_n(v_m_638_, 2);
lean_inc(v_00_u03c4_637_);
lean_inc_ref(v_W_635_);
lean_inc_ref_n(v_R_634_, 2);
v___f_639_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__0), 4, 3);
lean_closure_set(v___f_639_, 0, v_R_634_);
lean_closure_set(v___f_639_, 1, v_W_635_);
lean_closure_set(v___f_639_, 2, v_00_u03c4_637_);
v___f_640_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Wts_deg___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_640_, 0, v_R_634_);
lean_closure_set(v___f_640_, 1, v_W_635_);
lean_closure_set(v___f_640_, 2, v_u_636_);
lean_closure_set(v___f_640_, 3, v_m_638_);
lean_closure_set(v___f_640_, 4, v_00_u03c4_637_);
v___x_641_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_634_, v_m_638_);
lean_dec(v_m_638_);
lean_dec_ref(v_R_634_);
lean_inc(v___x_641_);
v___x_642_ = l_List_finRange(v___x_641_);
v___x_643_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_642_, v___f_640_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_sub(v___x_641_, v___x_644_);
lean_dec(v___x_641_);
v___x_646_ = l_List_finRange(v___x_645_);
v___x_647_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_646_, v___f_639_);
v___x_648_ = lean_int_sub(v___x_643_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_643_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg(lean_object* v_X_649_, lean_object* v_Word_650_, lean_object* v_R_651_, lean_object* v_W_652_, lean_object* v_u_653_, lean_object* v_00_u03c4_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lp_tree_Formalism_L2_Col_Wts_deg___redArg(v_R_651_, v_W_652_, v_u_653_, v_00_u03c4_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_deg___boxed(lean_object* v_X_656_, lean_object* v_Word_657_, lean_object* v_R_658_, lean_object* v_W_659_, lean_object* v_u_660_, lean_object* v_00_u03c4_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = lp_tree_Formalism_L2_Col_Wts_deg(v_X_656_, v_Word_657_, v_R_658_, v_W_659_, v_u_660_, v_00_u03c4_661_);
lean_dec_ref(v_X_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___redArg___lam__0(lean_object* v_R_663_, lean_object* v_W_664_, lean_object* v_00_u03c4_665_, lean_object* v_i_666_){
_start:
{
lean_object* v___x_58__overap_667_; lean_object* v___x_668_; 
v___x_58__overap_667_ = lp_tree_Formalism_L2_Col_Wts_sgTrue___redArg(v_R_663_, v_W_664_, v_00_u03c4_665_);
v___x_668_ = lean_apply_1(v___x_58__overap_667_, v_i_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___redArg___lam__1(lean_object* v_R_669_, lean_object* v_W_670_, lean_object* v_u_671_, lean_object* v_m_672_, lean_object* v_00_u03c4_673_, lean_object* v_i_674_){
_start:
{
lean_object* v___x_59__overap_675_; lean_object* v___x_676_; 
v___x_59__overap_675_ = lp_tree_Formalism_L2_Col_Wts_lamTrue___redArg(v_R_669_, v_W_670_, v_u_671_, v_m_672_, v_00_u03c4_673_);
v___x_676_ = lean_apply_1(v___x_59__overap_675_, v_i_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___redArg(lean_object* v_R_677_, lean_object* v_W_678_, lean_object* v_u_679_, lean_object* v_00_u03c4_680_){
_start:
{
lean_object* v_m_681_; lean_object* v___f_682_; lean_object* v___f_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_m_681_ = lean_ctor_get(v_R_677_, 2);
lean_inc_n(v_m_681_, 2);
lean_inc(v_00_u03c4_680_);
lean_inc_ref(v_W_678_);
lean_inc_ref_n(v_R_677_, 2);
v___f_682_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Wts_degTrue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_682_, 0, v_R_677_);
lean_closure_set(v___f_682_, 1, v_W_678_);
lean_closure_set(v___f_682_, 2, v_00_u03c4_680_);
v___f_683_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_Wts_degTrue___redArg___lam__1), 6, 5);
lean_closure_set(v___f_683_, 0, v_R_677_);
lean_closure_set(v___f_683_, 1, v_W_678_);
lean_closure_set(v___f_683_, 2, v_u_679_);
lean_closure_set(v___f_683_, 3, v_m_681_);
lean_closure_set(v___f_683_, 4, v_00_u03c4_680_);
v___x_684_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_677_, v_m_681_);
lean_dec(v_m_681_);
lean_dec_ref(v_R_677_);
lean_inc(v___x_684_);
v___x_685_ = l_List_finRange(v___x_684_);
v___x_686_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_685_, v___f_683_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v___x_684_, v___x_687_);
lean_dec(v___x_684_);
v___x_689_ = l_List_finRange(v___x_688_);
v___x_690_ = lp_tree_Finset_sum___at___00Formalism_HadamardInequality_energy_spec__0___redArg(v___x_689_, v___f_682_);
v___x_691_ = lean_int_sub(v___x_686_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_686_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue(lean_object* v_X_692_, lean_object* v_Word_693_, lean_object* v_R_694_, lean_object* v_W_695_, lean_object* v_u_696_, lean_object* v_00_u03c4_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = lp_tree_Formalism_L2_Col_Wts_degTrue___redArg(v_R_694_, v_W_695_, v_u_696_, v_00_u03c4_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_degTrue___boxed(lean_object* v_X_699_, lean_object* v_Word_700_, lean_object* v_R_701_, lean_object* v_W_702_, lean_object* v_u_703_, lean_object* v_00_u03c4_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = lp_tree_Formalism_L2_Col_Wts_degTrue(v_X_699_, v_Word_700_, v_R_701_, v_W_702_, v_u_703_, v_00_u03c4_704_);
lean_dec_ref(v_X_699_);
return v_res_705_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataCoeff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_FmZeroHLatEmpty(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Tuples(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataCoeff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_FmZeroHLatEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Tuples(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
