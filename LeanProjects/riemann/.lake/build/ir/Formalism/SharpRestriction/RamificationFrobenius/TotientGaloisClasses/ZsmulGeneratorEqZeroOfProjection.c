// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.FrobeniusOrbits.Statement
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
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_tree_MonoidHom_fst___at___00Formalism_FrobeniusOrbits_chQ_spec__0___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_tree_MonoidHom_snd___at___00Formalism_TwoAdicCyclotomicDecomposition_D2_spec__0___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Additive_toMul(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lean_int_neg(lean_object*);
extern lean_object* lp_tree_Formalism_FrobeniusOrbits_c0;
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instFintypeIdx___aux__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instFintypeIdx(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instAddCommGroupA(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instAddCommGroupA___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instFintypeA___aux__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instFintypeA(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_h(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_h___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_a0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_a0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_zmultiples___at___00Formalism_HC_Frame_A0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_zmultiples___at___00Formalism_HC_Frame_A0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_dig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofNat___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_hH___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_hH___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_hH___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_hH(lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_iota___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_iota___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iota___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iota(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iota___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iotaInv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iotaInv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iotaInv___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_sg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_sg___closed__0;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_sg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_sg___closed__1;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_sg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_sg___closed__2;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_sg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_sg___closed__3;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_sg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_sg___closed__4;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_sg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_sg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_cc(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_cc___boxed(lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_iod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_iod___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iod(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iod___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___closed__0 = (const lean_object*)&lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_HC_Frame_chD___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_snd___at___00Formalism_TwoAdicCyclotomicDecomposition_D2_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HC_Frame_chD___closed__0 = (const lean_object*)&lp_tree_Formalism_HC_Frame_chD___closed__0_value;
static const lean_closure_object lp_tree_Formalism_HC_Frame_chD___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_OneHom_comp___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___closed__0_value),((lean_object*)&lp_tree_Formalism_HC_Frame_chD___closed__0_value)} };
static const lean_object* lp_tree_Formalism_HC_Frame_chD___closed__1 = (const lean_object*)&lp_tree_Formalism_HC_Frame_chD___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chD(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chD___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_HC_Frame_chQ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_MonoidHom_fst___at___00Formalism_FrobeniusOrbits_chQ_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HC_Frame_chQ___closed__0 = (const lean_object*)&lp_tree_Formalism_HC_Frame_chQ___closed__0_value;
static const lean_closure_object lp_tree_Formalism_HC_Frame_chQ___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_OneHom_comp___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___closed__0_value),((lean_object*)&lp_tree_Formalism_HC_Frame_chQ___closed__0_value)} };
static const lean_object* lp_tree_Formalism_HC_Frame_chQ___closed__1 = (const lean_object*)&lp_tree_Formalism_HC_Frame_chQ___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chQ(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chQ___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0(lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_chC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_chC___closed__0;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_chC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_chC___closed__1;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_chC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_chC___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chC___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_Psi(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_Psi___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_placeOf(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_tau1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_tau1___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instFintypeIdx___aux__1(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_List_finRange(v_n_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instFintypeIdx(lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_List_finRange(v_n_3_);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___redArg(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_eq(v_a_5_, v_b_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___redArg___boxed(lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___redArg(v_a_8_, v_b_9_);
lean_dec(v_b_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx___aux__1(lean_object* v_n_12_, lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lean_nat_dec_eq(v_a_13_, v_b_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___aux__1___boxed(lean_object* v_n_16_, lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = lp_tree_Formalism_HC_instDecidableEqIdx___aux__1(v_n_16_, v_a_17_, v_b_18_);
lean_dec(v_b_18_);
lean_dec(v_a_17_);
lean_dec(v_n_16_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx___redArg(lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_eq(v_a_21_, v_b_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___redArg___boxed(lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = lp_tree_Formalism_HC_instDecidableEqIdx___redArg(v_a_24_, v_b_25_);
lean_dec(v_b_25_);
lean_dec(v_a_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_instDecidableEqIdx(lean_object* v_n_28_, lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_instDecidableEqIdx___boxed(lean_object* v_n_32_, lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = lp_tree_Formalism_HC_instDecidableEqIdx(v_n_32_, v_a_33_, v_b_34_);
lean_dec(v_b_34_);
lean_dec(v_a_33_);
lean_dec(v_n_32_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instAddCommGroupA(lean_object* v_00_u03c6_37_){
_start:
{
lean_object* v_grp_38_; 
v_grp_38_ = lean_ctor_get(v_00_u03c6_37_, 2);
lean_inc_ref(v_grp_38_);
return v_grp_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instAddCommGroupA___boxed(lean_object* v_00_u03c6_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_HC_Frame_instAddCommGroupA(v_00_u03c6_39_);
lean_dec_ref(v_00_u03c6_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instFintypeA___aux__1(lean_object* v_00_u03c6_41_){
_start:
{
lean_object* v_ord_42_; lean_object* v___x_43_; 
v_ord_42_ = lean_ctor_get(v_00_u03c6_41_, 1);
lean_inc(v_ord_42_);
lean_dec_ref(v_00_u03c6_41_);
v___x_43_ = l_List_finRange(v_ord_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instFintypeA(lean_object* v_00_u03c6_44_){
_start:
{
lean_object* v_ord_45_; lean_object* v___x_46_; 
v_ord_45_ = lean_ctor_get(v_00_u03c6_44_, 1);
lean_inc(v_ord_45_);
lean_dec_ref(v_00_u03c6_44_);
v___x_46_ = l_List_finRange(v_ord_45_);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___redArg(lean_object* v_a_47_, lean_object* v_b_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_eq(v_a_47_, v_b_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___redArg___boxed(lean_object* v_a_50_, lean_object* v_b_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___redArg(v_a_50_, v_b_51_);
lean_dec(v_b_51_);
lean_dec(v_a_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1(lean_object* v_00_u03c6_54_, lean_object* v_a_55_, lean_object* v_b_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_eq(v_a_55_, v_b_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1___boxed(lean_object* v_00_u03c6_58_, lean_object* v_a_59_, lean_object* v_b_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = lp_tree_Formalism_HC_Frame_instDecidableEqA___aux__1(v_00_u03c6_58_, v_a_59_, v_b_60_);
lean_dec(v_b_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_00_u03c6_58_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA___redArg(lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_eq(v_a_63_, v_b_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___redArg___boxed(lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = lp_tree_Formalism_HC_Frame_instDecidableEqA___redArg(v_a_66_, v_b_67_);
lean_dec(v_b_67_);
lean_dec(v_a_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HC_Frame_instDecidableEqA(lean_object* v_00_u03c6_70_, lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_nat_dec_eq(v_a_71_, v_b_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed(lean_object* v_00_u03c6_74_, lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = lp_tree_Formalism_HC_Frame_instDecidableEqA(v_00_u03c6_74_, v_a_75_, v_b_76_);
lean_dec(v_b_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_00_u03c6_74_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val___redArg(lean_object* v_t_79_){
_start:
{
lean_inc(v_t_79_);
return v_t_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val___redArg___boxed(lean_object* v_t_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_Formalism_HC_Frame_A_val___redArg(v_t_80_);
lean_dec(v_t_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val(lean_object* v_00_u03c6_82_, lean_object* v_t_83_){
_start:
{
lean_inc(v_t_83_);
return v_t_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_val___boxed(lean_object* v_00_u03c6_84_, lean_object* v_t_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_HC_Frame_A_val(v_00_u03c6_84_, v_t_85_);
lean_dec(v_t_85_);
lean_dec_ref(v_00_u03c6_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal___redArg(lean_object* v_u_87_){
_start:
{
lean_inc(v_u_87_);
return v_u_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal___redArg___boxed(lean_object* v_u_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_tree_Formalism_HC_Frame_A_ofVal___redArg(v_u_88_);
lean_dec(v_u_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal(lean_object* v_00_u03c6_90_, lean_object* v_u_91_, lean_object* v_hu_92_){
_start:
{
lean_inc(v_u_91_);
return v_u_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A_ofVal___boxed(lean_object* v_00_u03c6_93_, lean_object* v_u_94_, lean_object* v_hu_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_Formalism_HC_Frame_A_ofVal(v_00_u03c6_93_, v_u_94_, v_hu_95_);
lean_dec(v_u_94_);
lean_dec_ref(v_00_u03c6_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_h(lean_object* v_00_u03c6_97_){
_start:
{
lean_object* v_h0_98_; 
v_h0_98_ = lean_ctor_get(v_00_u03c6_97_, 3);
lean_inc(v_h0_98_);
return v_h0_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_h___boxed(lean_object* v_00_u03c6_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_tree_Formalism_HC_Frame_h(v_00_u03c6_99_);
lean_dec_ref(v_00_u03c6_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_a0(lean_object* v_00_u03c6_101_){
_start:
{
lean_object* v_gen0_102_; 
v_gen0_102_ = lean_ctor_get(v_00_u03c6_101_, 4);
lean_inc(v_gen0_102_);
return v_gen0_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_a0___boxed(lean_object* v_00_u03c6_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_tree_Formalism_HC_Frame_a0(v_00_u03c6_103_);
lean_dec_ref(v_00_u03c6_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_zmultiples___at___00Formalism_HC_Frame_A0_spec__0(lean_object* v_00_u03c6_105_, lean_object* v_g_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(0);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubgroup_zmultiples___at___00Formalism_HC_Frame_A0_spec__0___boxed(lean_object* v_00_u03c6_108_, lean_object* v_g_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_tree_AddSubgroup_zmultiples___at___00Formalism_HC_Frame_A0_spec__0(v_00_u03c6_108_, v_g_109_);
lean_dec(v_g_109_);
lean_dec_ref(v_00_u03c6_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A0(lean_object* v_00_u03c6_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_A0___boxed(lean_object* v_00_u03c6_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_tree_Formalism_HC_Frame_A0(v_00_u03c6_113_);
lean_dec_ref(v_00_u03c6_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_dig(lean_object* v_00_u03c6_115_, lean_object* v_s_116_){
_start:
{
lean_object* v_grp_117_; lean_object* v_toAddMonoid_118_; lean_object* v_gen0_119_; lean_object* v_toNSMul_120_; lean_object* v___x_121_; 
v_grp_117_ = lean_ctor_get(v_00_u03c6_115_, 2);
v_toAddMonoid_118_ = lean_ctor_get(v_grp_117_, 0);
lean_inc_ref(v_toAddMonoid_118_);
v_gen0_119_ = lean_ctor_get(v_00_u03c6_115_, 4);
lean_inc(v_gen0_119_);
lean_dec_ref(v_00_u03c6_115_);
v_toNSMul_120_ = lean_ctor_get(v_toAddMonoid_118_, 2);
lean_inc(v_toNSMul_120_);
lean_dec_ref(v_toAddMonoid_118_);
v___x_121_ = lean_apply_2(v_toNSMul_120_, v_s_116_, v_gen0_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofNat(lean_object* v_00_u03c6_122_, lean_object* v_u_123_){
_start:
{
lean_object* v_ord_124_; lean_object* v___x_125_; 
v_ord_124_ = lean_ctor_get(v_00_u03c6_122_, 1);
v___x_125_ = lean_nat_mod(v_u_123_, v_ord_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_ofNat___boxed(lean_object* v_00_u03c6_126_, lean_object* v_u_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_tree_Formalism_HC_Frame_ofNat(v_00_u03c6_126_, v_u_127_);
lean_dec(v_u_127_);
lean_dec_ref(v_00_u03c6_126_);
return v_res_128_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_129_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_hH___lam__0___closed__1(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_mathlib_Additive_toMul(lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_hH___lam__0(lean_object* v_00_u03c6_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_h0_133_; lean_object* v___x_134_; lean_object* v_toFun_135_; lean_object* v___x_136_; lean_object* v_toFun_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_h0_133_ = lean_ctor_get(v_00_u03c6_131_, 3);
lean_inc(v_h0_133_);
lean_dec_ref(v_00_u03c6_131_);
v___x_134_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0, &lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0_once, _init_lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0);
v_toFun_135_ = lean_ctor_get(v___x_134_, 0);
v___x_136_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_hH___lam__0___closed__1, &lp_tree_Formalism_HC_Frame_hH___lam__0___closed__1_once, _init_lp_tree_Formalism_HC_Frame_hH___lam__0___closed__1);
v_toFun_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_toFun_135_);
v___x_138_ = lean_apply_1(v_toFun_135_, v_a_132_);
v___x_139_ = lean_apply_1(v_h0_133_, v___x_138_);
lean_inc(v_toFun_137_);
v___x_140_ = lean_apply_1(v_toFun_137_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_hH(lean_object* v_00_u03c6_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_hH___lam__0), 2, 1);
lean_closure_set(v___f_142_, 0, v_00_u03c6_141_);
return v___f_142_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_iota___redArg___closed__0(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iota___redArg(lean_object* v_t_144_){
_start:
{
lean_object* v___x_145_; lean_object* v_toFun_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_iota___redArg___closed__0, &lp_tree_Formalism_HC_Frame_iota___redArg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_iota___redArg___closed__0);
v_toFun_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_toFun_146_);
v___x_147_ = lean_apply_1(v_toFun_146_, v_t_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iota(lean_object* v_00_u03c6_148_, lean_object* v_t_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lp_tree_Formalism_HC_Frame_iota___redArg(v_t_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iota___boxed(lean_object* v_00_u03c6_151_, lean_object* v_t_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_tree_Formalism_HC_Frame_iota(v_00_u03c6_151_, v_t_152_);
lean_dec_ref(v_00_u03c6_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iotaInv___redArg(lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; lean_object* v_toFun_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0, &lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0_once, _init_lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0);
v_toFun_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_toFun_156_);
v___x_157_ = lean_apply_1(v_toFun_156_, v_a_154_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iotaInv(lean_object* v_00_u03c6_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lp_tree_Formalism_HC_Frame_iotaInv___redArg(v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iotaInv___boxed(lean_object* v_00_u03c6_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_tree_Formalism_HC_Frame_iotaInv(v_00_u03c6_161_, v_a_162_);
lean_dec_ref(v_00_u03c6_161_);
return v_res_163_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_sg___closed__0(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_sg___closed__1(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__0, &lp_tree_Formalism_HC_Frame_sg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__0);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_sg___closed__2(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__0, &lp_tree_Formalism_HC_Frame_sg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__0);
v___x_169_ = lean_int_neg(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_sg___closed__3(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__2, &lp_tree_Formalism_HC_Frame_sg___closed__2_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__2);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_sg___closed__4(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__1, &lp_tree_Formalism_HC_Frame_sg___closed__1_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__1);
v___x_173_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__3, &lp_tree_Formalism_HC_Frame_sg___closed__3_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__3);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_sg(lean_object* v_00_u03c6_175_){
_start:
{
lean_object* v_grp_176_; lean_object* v___x_177_; lean_object* v_toZero_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_189_; 
v_grp_176_ = lean_ctor_get(v_00_u03c6_175_, 2);
v___x_177_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_grp_176_);
v_toZero_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v___x_177_, 1);
lean_dec(v_unused_190_);
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_toZero_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v_toFun_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_182_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_iota___redArg___closed__0, &lp_tree_Formalism_HC_Frame_iota___redArg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_iota___redArg___closed__0);
v_toFun_183_ = lean_ctor_get(v___x_182_, 0);
v___x_184_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__4, &lp_tree_Formalism_HC_Frame_sg___closed__4_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__4);
lean_inc(v_toFun_183_);
v___x_185_ = lean_apply_1(v_toFun_183_, v_toZero_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_185_);
lean_ctor_set(v___x_180_, 0, v___x_184_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_sg___boxed(lean_object* v_00_u03c6_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lp_tree_Formalism_HC_Frame_sg(v_00_u03c6_191_);
lean_dec_ref(v_00_u03c6_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_cc(lean_object* v_00_u03c6_193_){
_start:
{
lean_object* v_grp_194_; lean_object* v___x_195_; lean_object* v_toZero_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_207_; 
v_grp_194_ = lean_ctor_get(v_00_u03c6_193_, 2);
v___x_195_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_grp_194_);
v_toZero_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v___x_195_, 1);
lean_dec(v_unused_208_);
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_toZero_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v_toFun_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_200_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_iota___redArg___closed__0, &lp_tree_Formalism_HC_Frame_iota___redArg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_iota___redArg___closed__0);
v_toFun_201_ = lean_ctor_get(v___x_200_, 0);
v___x_202_ = lp_tree_Formalism_FrobeniusOrbits_c0;
lean_inc(v_toFun_201_);
v___x_203_ = lean_apply_1(v_toFun_201_, v_toZero_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_203_);
lean_ctor_set(v___x_198_, 0, v___x_202_);
v___x_205_ = v___x_198_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_cc___boxed(lean_object* v_00_u03c6_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = lp_tree_Formalism_HC_Frame_cc(v_00_u03c6_209_);
lean_dec_ref(v_00_u03c6_209_);
return v_res_210_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_iod___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__3, &lp_tree_Formalism_HC_Frame_sg___closed__3_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__3);
v___x_212_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__1, &lp_tree_Formalism_HC_Frame_sg___closed__1_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__1);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iod(lean_object* v_00_u03c6_214_){
_start:
{
lean_object* v_grp_215_; lean_object* v___x_216_; lean_object* v_toZero_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_228_; 
v_grp_215_ = lean_ctor_get(v_00_u03c6_214_, 2);
v___x_216_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v_grp_215_);
v_toZero_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v___x_216_, 1);
lean_dec(v_unused_229_);
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_228_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_toZero_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_228_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v_toFun_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_221_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_iota___redArg___closed__0, &lp_tree_Formalism_HC_Frame_iota___redArg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_iota___redArg___closed__0);
v_toFun_222_ = lean_ctor_get(v___x_221_, 0);
v___x_223_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_iod___closed__0, &lp_tree_Formalism_HC_Frame_iod___closed__0_once, _init_lp_tree_Formalism_HC_Frame_iod___closed__0);
lean_inc(v_toFun_222_);
v___x_224_ = lean_apply_1(v_toFun_222_, v_toZero_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_224_);
lean_ctor_set(v___x_219_, 0, v___x_223_);
v___x_226_ = v___x_219_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_iod___boxed(lean_object* v_00_u03c6_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = lp_tree_Formalism_HC_Frame_iod(v_00_u03c6_230_);
lean_dec_ref(v_00_u03c6_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___lam__0(lean_object* v_self_232_){
_start:
{
lean_object* v_fst_233_; 
v_fst_233_ = lean_ctor_get(v_self_232_, 0);
lean_inc(v_fst_233_);
return v_fst_233_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___lam__0___boxed(lean_object* v_self_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___lam__0(v_self_234_);
lean_dec_ref(v_self_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0(lean_object* v_00_u03c6_237_){
_start:
{
lean_object* v___f_238_; 
v___f_238_ = ((lean_object*)(lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___closed__0));
return v___f_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0___boxed(lean_object* v_00_u03c6_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = lp_tree_MonoidHom_fst___at___00Formalism_HC_Frame_chD_spec__0(v_00_u03c6_239_);
lean_dec_ref(v_00_u03c6_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chD(lean_object* v_00_u03c6_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = ((lean_object*)(lp_tree_Formalism_HC_Frame_chD___closed__1));
return v___f_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chD___boxed(lean_object* v_00_u03c6_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_tree_Formalism_HC_Frame_chD(v_00_u03c6_247_);
lean_dec_ref(v_00_u03c6_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chQ(lean_object* v_00_u03c6_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = ((lean_object*)(lp_tree_Formalism_HC_Frame_chQ___closed__1));
return v___f_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chQ___boxed(lean_object* v_00_u03c6_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = lp_tree_Formalism_HC_Frame_chQ(v_00_u03c6_255_);
lean_dec_ref(v_00_u03c6_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0___lam__0(lean_object* v_f_257_, lean_object* v_u_258_){
_start:
{
lean_object* v_val_259_; lean_object* v_inv_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_269_; 
v_val_259_ = lean_ctor_get(v_u_258_, 0);
v_inv_260_ = lean_ctor_get(v_u_258_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_u_258_);
if (v_isSharedCheck_269_ == 0)
{
v___x_262_ = v_u_258_;
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_inv_260_);
lean_inc(v_val_259_);
lean_dec(v_u_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_269_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
lean_inc_ref(v_f_257_);
v___x_264_ = lean_apply_1(v_f_257_, v_val_259_);
v___x_265_ = lean_apply_1(v_f_257_, v_inv_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_265_);
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_267_ = v___x_262_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0(lean_object* v_f_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_271_, 0, v_f_270_);
return v___f_271_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_chC___closed__0(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lp_mathlib_Complex_commRing;
v___x_273_ = lp_mathlib_Ring_toNonAssocRing___redArg(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_chC___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_chC___closed__0, &lp_tree_Formalism_HC_Frame_chC___closed__0_once, _init_lp_tree_Formalism_HC_Frame_chC___closed__0);
v___x_275_ = lp_mathlib_Int_castRingHom___redArg(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_chC___closed__2(void){
_start:
{
lean_object* v___x_276_; lean_object* v___f_277_; 
v___x_276_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_chC___closed__1, &lp_tree_Formalism_HC_Frame_chC___closed__1_once, _init_lp_tree_Formalism_HC_Frame_chC___closed__1);
v___f_277_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_277_, 0, v___x_276_);
return v___f_277_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chC(lean_object* v_00_u03c6_278_){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___f_281_; 
v___f_279_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_chC___closed__2, &lp_tree_Formalism_HC_Frame_chC___closed__2_once, _init_lp_tree_Formalism_HC_Frame_chC___closed__2);
v___x_280_ = lp_tree_Formalism_HC_Frame_chD(v_00_u03c6_278_);
v___f_281_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_281_, 0, v___x_280_);
lean_closure_set(v___f_281_, 1, v___f_279_);
return v___f_281_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_chC___boxed(lean_object* v_00_u03c6_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = lp_tree_Formalism_HC_Frame_chC(v_00_u03c6_282_);
lean_dec_ref(v_00_u03c6_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___redArg(lean_object* v_f_284_){
_start:
{
lean_inc_ref(v_f_284_);
return v_f_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___redArg___boxed(lean_object* v_f_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___redArg(v_f_285_);
lean_dec_ref(v_f_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0(lean_object* v_f_287_, lean_object* v_map__mul_288_){
_start:
{
lean_inc_ref(v_f_287_);
return v_f_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0___boxed(lean_object* v_f_289_, lean_object* v_map__mul_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_HC_Frame_chC_spec__0_spec__0(v_f_289_, v_map__mul_290_);
lean_dec_ref(v_f_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0_spec__1(lean_object* v_00_u03c6_292_, lean_object* v_mc_293_, lean_object* v_f_294_, lean_object* v_S_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c6_297_, lean_object* v_mc_298_, lean_object* v_f_299_, lean_object* v_S_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = lp_tree_Submonoid_comap___at___00MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0_spec__1(v_00_u03c6_297_, v_mc_298_, v_f_299_, v_S_300_);
lean_dec_ref(v_f_299_);
lean_dec_ref(v_00_u03c6_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___redArg(lean_object* v_00_u03c6_302_, lean_object* v_f_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___redArg___boxed(lean_object* v_00_u03c6_305_, lean_object* v_f_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___redArg(v_00_u03c6_305_, v_f_306_);
lean_dec_ref(v_f_306_);
lean_dec_ref(v_00_u03c6_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0(lean_object* v_00_u03c6_308_, lean_object* v_f_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_box(0);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0___boxed(lean_object* v_00_u03c6_311_, lean_object* v_f_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = lp_tree_MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0(v_00_u03c6_311_, v_f_312_);
lean_dec_ref(v_f_312_);
lean_dec_ref(v_00_u03c6_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_Psi(lean_object* v_00_u03c6_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_Psi___boxed(lean_object* v_00_u03c6_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = lp_tree_Formalism_HC_Frame_Psi(v_00_u03c6_316_);
lean_dec_ref(v_00_u03c6_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0(lean_object* v_00_u03c6_318_, lean_object* v_mc_319_, lean_object* v_f_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0___boxed(lean_object* v_00_u03c6_322_, lean_object* v_mc_323_, lean_object* v_f_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = lp_tree_MonoidHom_mker___at___00MonoidHom_ker___at___00Formalism_HC_Frame_Psi_spec__0_spec__0(v_00_u03c6_322_, v_mc_323_, v_f_324_);
lean_dec_ref(v_f_324_);
lean_dec_ref(v_00_u03c6_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_placeOf(lean_object* v_00_u03c6_326_, lean_object* v_g_327_){
_start:
{
lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_fst_328_ = lean_ctor_get(v_g_327_, 0);
v_snd_329_ = lean_ctor_get(v_g_327_, 1);
v_fst_330_ = lean_ctor_get(v_fst_328_, 0);
v_snd_331_ = lean_ctor_get(v_fst_328_, 1);
lean_inc_n(v_snd_331_, 2);
v___x_332_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_333_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__1, &lp_tree_Formalism_HC_Frame_sg___closed__1_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__1);
v___x_334_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_332_, v_snd_331_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v_grp_335_; lean_object* v_toAddMonoid_336_; lean_object* v_toAddSemigroup_337_; lean_object* v___x_338_; lean_object* v_fst_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_391_; 
lean_inc(v_fst_330_);
lean_inc(v_snd_329_);
lean_dec_ref(v_g_327_);
v_grp_335_ = lean_ctor_get(v_00_u03c6_326_, 2);
v_toAddMonoid_336_ = lean_ctor_get(v_grp_335_, 0);
v_toAddSemigroup_337_ = lean_ctor_get(v_toAddMonoid_336_, 0);
lean_inc(v_toAddSemigroup_337_);
v___x_338_ = lp_tree_Formalism_HC_Frame_cc(v_00_u03c6_326_);
lean_dec_ref(v_00_u03c6_326_);
v_fst_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_fst_339_);
v_fst_340_ = lean_ctor_get(v_fst_339_, 0);
v_snd_341_ = lean_ctor_get(v_fst_339_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_fst_339_);
if (v_isSharedCheck_391_ == 0)
{
v___x_343_ = v_fst_339_;
v_isShared_344_ = v_isSharedCheck_391_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snd_341_);
lean_inc(v_fst_340_);
lean_dec(v_fst_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_391_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_389_; 
v_snd_345_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v___x_338_, 0);
lean_dec(v_unused_390_);
v___x_347_ = v___x_338_;
v_isShared_348_ = v_isSharedCheck_389_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_dec(v___x_338_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_389_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_val_349_; lean_object* v_inv_350_; lean_object* v_val_351_; lean_object* v_inv_352_; lean_object* v_val_353_; lean_object* v_inv_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_388_; 
v_val_349_ = lean_ctor_get(v_fst_340_, 0);
lean_inc(v_val_349_);
v_inv_350_ = lean_ctor_get(v_fst_340_, 1);
lean_inc(v_inv_350_);
lean_dec(v_fst_340_);
v_val_351_ = lean_ctor_get(v_fst_330_, 0);
lean_inc(v_val_351_);
v_inv_352_ = lean_ctor_get(v_fst_330_, 1);
lean_inc(v_inv_352_);
lean_dec(v_fst_330_);
v_val_353_ = lean_ctor_get(v_snd_341_, 0);
v_inv_354_ = lean_ctor_get(v_snd_341_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_snd_341_);
if (v_isSharedCheck_388_ == 0)
{
v___x_356_ = v_snd_341_;
v_isShared_357_ = v_isSharedCheck_388_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_inv_354_);
lean_inc(v_val_353_);
lean_dec(v_snd_341_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_388_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_val_358_; lean_object* v_inv_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_387_; 
v_val_358_ = lean_ctor_get(v_snd_331_, 0);
v_inv_359_ = lean_ctor_get(v_snd_331_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_snd_331_);
if (v_isSharedCheck_387_ == 0)
{
v___x_361_ = v_snd_331_;
v_isShared_362_ = v_isSharedCheck_387_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_inv_359_);
lean_inc(v_val_358_);
lean_dec(v_snd_331_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_387_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v_toFun_364_; lean_object* v___x_365_; lean_object* v_toFun_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_363_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0, &lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0_once, _init_lp_tree_Formalism_HC_Frame_hH___lam__0___closed__0);
v_toFun_364_ = lean_ctor_get(v___x_363_, 0);
v___x_365_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_iota___redArg___closed__0, &lp_tree_Formalism_HC_Frame_iota___redArg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_iota___redArg___closed__0);
v_toFun_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_toFun_364_);
v___x_367_ = lean_apply_1(v_toFun_364_, v_snd_345_);
v___x_368_ = lean_int_mul(v_val_349_, v_val_351_);
lean_dec(v_val_351_);
lean_dec(v_val_349_);
v___x_369_ = lean_int_mul(v_inv_352_, v_inv_350_);
lean_dec(v_inv_350_);
lean_dec(v_inv_352_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_369_);
lean_ctor_set(v___x_361_, 0, v___x_368_);
v___x_371_ = v___x_361_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_386_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_372_ = lean_int_mul(v_val_353_, v_val_358_);
lean_dec(v_val_358_);
lean_dec(v_val_353_);
v___x_373_ = lean_int_mul(v_inv_359_, v_inv_354_);
lean_dec(v_inv_354_);
lean_dec(v_inv_359_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v___x_373_);
lean_ctor_set(v___x_356_, 0, v___x_372_);
v___x_375_ = v___x_356_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_385_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_375_);
lean_ctor_set(v___x_343_, 0, v___x_371_);
v___x_377_ = v___x_343_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_384_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
lean_inc(v_toFun_364_);
v___x_378_ = lean_apply_1(v_toFun_364_, v_snd_329_);
v___x_379_ = lean_apply_2(v_toAddSemigroup_337_, v___x_367_, v___x_378_);
lean_inc(v_toFun_366_);
v___x_380_ = lean_apply_1(v_toFun_366_, v___x_379_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_380_);
lean_ctor_set(v___x_347_, 0, v___x_377_);
v___x_382_ = v___x_347_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v_snd_331_);
lean_dec_ref(v_00_u03c6_326_);
return v_g_327_;
}
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_tau1___redArg___closed__0(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__1, &lp_tree_Formalism_HC_Frame_sg___closed__1_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__1);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau1___redArg(lean_object* v_t_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_tau1___redArg___closed__0, &lp_tree_Formalism_HC_Frame_tau1___redArg___closed__0_once, _init_lp_tree_Formalism_HC_Frame_tau1___redArg___closed__0);
v___x_396_ = lp_tree_Formalism_HC_Frame_iota___redArg(v_t_394_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau1(lean_object* v_00_u03c6_398_, lean_object* v_t_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lp_tree_Formalism_HC_Frame_tau1___redArg(v_t_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau1___boxed(lean_object* v_00_u03c6_401_, lean_object* v_t_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = lp_tree_Formalism_HC_Frame_tau1(v_00_u03c6_401_, v_t_402_);
lean_dec_ref(v_00_u03c6_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau2___redArg(lean_object* v_t_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_sg___closed__4, &lp_tree_Formalism_HC_Frame_sg___closed__4_once, _init_lp_tree_Formalism_HC_Frame_sg___closed__4);
v___x_406_ = lp_tree_Formalism_HC_Frame_iota___redArg(v_t_404_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau2(lean_object* v_00_u03c6_408_, lean_object* v_t_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lp_tree_Formalism_HC_Frame_tau2___redArg(v_t_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_tau2___boxed(lean_object* v_00_u03c6_411_, lean_object* v_t_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = lp_tree_Formalism_HC_Frame_tau2(v_00_u03c6_411_, v_t_412_);
lean_dec_ref(v_00_u03c6_411_);
return v_res_413_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection(uint8_t builtin) {
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
res = initialize_tree_Formalism_FrobeniusOrbits_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
