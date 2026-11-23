// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_ZMod_unitOfCoprime___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_cc(lean_object*);
lean_object* lp_mathlib_Nat_primeFactors(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_F(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_F___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submonoid_copy___at___00Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submonoid_copy___at___00Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subring_toAddSubgroup___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subring_toAddSubgroup___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_galE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_galE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_galE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_conj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_conj___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_HostRaw_psAt___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_HostRaw_psAt___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_psAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_psAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_psAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN___redArg(lean_object* v_H_1_){
_start:
{
lean_object* v_q_2_; lean_object* v_d_3_; lean_object* v_QS_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_q_2_ = lean_ctor_get(v_H_1_, 0);
v_d_3_ = lean_ctor_get(v_H_1_, 1);
v_QS_4_ = lean_ctor_get(v_H_1_, 2);
v___x_5_ = lean_nat_mul(v_QS_4_, v_q_2_);
v___x_6_ = lean_nat_mul(v___x_5_, v_d_3_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN___redArg___boxed(lean_object* v_H_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_HC_HostRaw_condN___redArg(v_H_7_);
lean_dec_ref(v_H_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN(lean_object* v_00_u03c6_9_, lean_object* v_H_10_){
_start:
{
lean_object* v_q_11_; lean_object* v_d_12_; lean_object* v_QS_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_q_11_ = lean_ctor_get(v_H_10_, 0);
v_d_12_ = lean_ctor_get(v_H_10_, 1);
v_QS_13_ = lean_ctor_get(v_H_10_, 2);
v___x_14_ = lean_nat_mul(v_QS_13_, v_q_11_);
v___x_15_ = lean_nat_mul(v___x_14_, v_d_12_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_condN___boxed(lean_object* v_00_u03c6_16_, lean_object* v_H_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_HC_HostRaw_condN(v_00_u03c6_16_, v_H_17_);
lean_dec_ref(v_H_17_);
lean_dec_ref(v_00_u03c6_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small___redArg(lean_object* v_H_19_){
_start:
{
lean_object* v_QS_20_; lean_object* v___x_21_; 
v_QS_20_ = lean_ctor_get(v_H_19_, 2);
v___x_21_ = lp_mathlib_Nat_primeFactors(v_QS_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small___redArg___boxed(lean_object* v_H_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_HC_HostRaw_small___redArg(v_H_22_);
lean_dec_ref(v_H_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small(lean_object* v_00_u03c6_24_, lean_object* v_H_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_Formalism_HC_HostRaw_small___redArg(v_H_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_small___boxed(lean_object* v_00_u03c6_27_, lean_object* v_H_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_HC_HostRaw_small(v_00_u03c6_27_, v_H_28_);
lean_dec_ref(v_H_28_);
lean_dec_ref(v_00_u03c6_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_F(lean_object* v_00_u03c6_30_, lean_object* v_H_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_F___boxed(lean_object* v_00_u03c6_33_, lean_object* v_H_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Formalism_HC_HostRaw_F(v_00_u03c6_33_, v_H_34_);
lean_dec_ref(v_H_34_);
lean_dec_ref(v_00_u03c6_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submonoid_copy___at___00Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6_spec__10(lean_object* v_H_36_, lean_object* v_S_37_, lean_object* v_s_38_, lean_object* v_hs_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submonoid_copy___at___00Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_H_41_, lean_object* v_S_42_, lean_object* v_s_43_, lean_object* v_hs_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Submonoid_copy___at___00Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6_spec__10(v_H_41_, v_S_42_, v_s_43_, v_hs_44_);
lean_dec_ref(v_H_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__4(lean_object* v_H_46_, lean_object* v_00_u03b9_47_, lean_object* v_s_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__4___boxed(lean_object* v_H_50_, lean_object* v_00_u03b9_51_, lean_object* v_s_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__4(v_H_50_, v_00_u03b9_51_, v_s_52_);
lean_dec_ref(v_s_52_);
lean_dec_ref(v_H_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__1(lean_object* v_H_54_, lean_object* v_00_u03b9_55_, lean_object* v_s_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__1___boxed(lean_object* v_H_58_, lean_object* v_00_u03b9_59_, lean_object* v_s_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__1(v_H_58_, v_00_u03b9_59_, v_s_60_);
lean_dec_ref(v_s_60_);
lean_dec_ref(v_H_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__0(lean_object* v_t_62_, lean_object* v_h_63_){
_start:
{
return v_t_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__1(lean_object* v_H_64_, lean_object* v_t_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_H_67_, lean_object* v_t_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___lam__1(v_H_67_, v_t_68_);
lean_dec_ref(v_H_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg(lean_object* v_H_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg___boxed(lean_object* v_H_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___redArg(v_H_72_);
lean_dec_ref(v_H_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K___redArg(lean_object* v_H_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K___redArg___boxed(lean_object* v_H_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_HC_HostRaw_K___redArg(v_H_76_);
lean_dec_ref(v_H_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K(lean_object* v_00_u03c6_78_, lean_object* v_H_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_K___boxed(lean_object* v_00_u03c6_81_, lean_object* v_H_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_tree_Formalism_HC_HostRaw_K(v_00_u03c6_81_, v_H_82_);
lean_dec_ref(v_H_82_);
lean_dec_ref(v_00_u03c6_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___redArg(lean_object* v_H_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___redArg___boxed(lean_object* v_H_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___redArg(v_H_86_);
lean_dec_ref(v_H_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0(lean_object* v_H_88_, lean_object* v_S_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0___boxed(lean_object* v_H_91_, lean_object* v_S_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0(v_H_91_, v_S_92_);
lean_dec_ref(v_H_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subring_toAddSubgroup___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__2(lean_object* v_H_94_, lean_object* v_self_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subring_toAddSubgroup___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__2___boxed(lean_object* v_H_97_, lean_object* v_self_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_tree_Subring_toAddSubgroup___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__2(v_H_97_, v_self_98_);
lean_dec_ref(v_H_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0(lean_object* v_H_100_, lean_object* v_s_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0___boxed(lean_object* v_H_103_, lean_object* v_s_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_tree_Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0(v_H_103_, v_s_104_);
lean_dec_ref(v_H_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__4(lean_object* v_H_106_, lean_object* v_00_u03b9_107_, lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_H_110_, lean_object* v_00_u03b9_111_, lean_object* v_s_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__4(v_H_110_, v_00_u03b9_111_, v_s_112_);
lean_dec_ref(v_s_112_);
lean_dec_ref(v_H_110_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__5(lean_object* v_H_114_, lean_object* v_00_u03b9_115_, lean_object* v_s_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_H_118_, lean_object* v_00_u03b9_119_, lean_object* v_s_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_iInf___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__5(v_H_118_, v_00_u03b9_119_, v_s_120_);
lean_dec_ref(v_s_120_);
lean_dec_ref(v_H_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__6(lean_object* v_H_122_, lean_object* v_S_123_, lean_object* v_s_124_, lean_object* v_hs_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_copy___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_H_127_, lean_object* v_S_128_, lean_object* v_s_129_, lean_object* v_hs_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_AddSubmonoid_copy___at___00iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3_spec__6(v_H_127_, v_S_128_, v_s_129_, v_hs_130_);
lean_dec_ref(v_H_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_S_132_, lean_object* v_h_133_){
_start:
{
return v_S_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__1(lean_object* v_H_134_, lean_object* v_S_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_box(0);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__1___boxed(lean_object* v_H_137_, lean_object* v_S_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___lam__1(v_H_137_, v_S_138_);
lean_dec_ref(v_H_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg(lean_object* v_H_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_H_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___redArg(v_H_142_);
lean_dec_ref(v_H_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3(lean_object* v_H_144_, lean_object* v_00_u03b9_145_, lean_object* v_s_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_box(0);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3___boxed(lean_object* v_H_148_, lean_object* v_00_u03b9_149_, lean_object* v_s_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__3(v_H_148_, v_00_u03b9_149_, v_s_150_);
lean_dec_ref(v_s_150_);
lean_dec_ref(v_H_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___redArg(lean_object* v_H_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_H_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___redArg(v_H_154_);
lean_dec_ref(v_H_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5(lean_object* v_H_156_, lean_object* v_00_u03b9_157_, lean_object* v_s_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5___boxed(lean_object* v_H_160_, lean_object* v_00_u03b9_161_, lean_object* v_s_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_tree_iInf___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__5(v_H_160_, v_00_u03b9_161_, v_s_162_);
lean_dec_ref(v_s_162_);
lean_dec_ref(v_H_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___redArg(lean_object* v_H_164_, lean_object* v_sm_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_H_167_, lean_object* v_sm_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___redArg(v_H_167_, v_sm_168_);
lean_dec_ref(v_H_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6(lean_object* v_H_170_, lean_object* v_s_171_, lean_object* v_sm_172_, lean_object* v_sa_173_, lean_object* v_hm_174_, lean_object* v_ha_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6___boxed(lean_object* v_H_177_, lean_object* v_s_178_, lean_object* v_sm_179_, lean_object* v_sa_180_, lean_object* v_hm_181_, lean_object* v_ha_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = lp_tree_Subring_mk_x27___at___00Subfield_closure___at___00IntermediateField_adjoin___at___00Formalism_HC_HostRaw_K_spec__0_spec__0_spec__6(v_H_177_, v_s_178_, v_sm_179_, v_sa_180_, v_hm_181_, v_ha_182_);
lean_dec_ref(v_H_177_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_galE___redArg(lean_object* v_H_184_, lean_object* v_00_u03c3_185_){
_start:
{
lean_object* v_gal_186_; lean_object* v_toFun_187_; lean_object* v___x_188_; 
v_gal_186_ = lean_ctor_get(v_H_184_, 4);
lean_inc_ref(v_gal_186_);
lean_dec_ref(v_H_184_);
v_toFun_187_ = lean_ctor_get(v_gal_186_, 0);
lean_inc(v_toFun_187_);
lean_dec_ref(v_gal_186_);
v___x_188_ = lean_apply_1(v_toFun_187_, v_00_u03c3_185_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_galE(lean_object* v_00_u03c6_189_, lean_object* v_H_190_, lean_object* v_00_u03c3_191_){
_start:
{
lean_object* v_gal_192_; lean_object* v_toFun_193_; lean_object* v___x_194_; 
v_gal_192_ = lean_ctor_get(v_H_190_, 4);
lean_inc_ref(v_gal_192_);
lean_dec_ref(v_H_190_);
v_toFun_193_ = lean_ctor_get(v_gal_192_, 0);
lean_inc(v_toFun_193_);
lean_dec_ref(v_gal_192_);
v___x_194_ = lean_apply_1(v_toFun_193_, v_00_u03c3_191_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_galE___boxed(lean_object* v_00_u03c6_195_, lean_object* v_H_196_, lean_object* v_00_u03c3_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_tree_Formalism_HC_HostRaw_galE(v_00_u03c6_195_, v_H_196_, v_00_u03c3_197_);
lean_dec_ref(v_00_u03c6_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0___redArg(lean_object* v_h_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lp_mathlib_Equiv_symm___redArg(v_h_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0(lean_object* v_H_201_, lean_object* v_00_u03c6_202_, lean_object* v_h_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lp_mathlib_Equiv_symm___redArg(v_h_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0___boxed(lean_object* v_H_205_, lean_object* v_00_u03c6_206_, lean_object* v_h_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = lp_tree_MulEquiv_symm___at___00Formalism_HC_HostRaw_conj_spec__0(v_H_205_, v_00_u03c6_206_, v_h_207_);
lean_dec_ref(v_00_u03c6_206_);
lean_dec_ref(v_H_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_conj(lean_object* v_00_u03c6_209_, lean_object* v_H_210_){
_start:
{
lean_object* v_gal_211_; lean_object* v___x_212_; lean_object* v_toFun_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_gal_211_ = lean_ctor_get(v_H_210_, 4);
lean_inc_ref(v_gal_211_);
lean_dec_ref(v_H_210_);
v___x_212_ = lp_mathlib_Equiv_symm___redArg(v_gal_211_);
v_toFun_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_toFun_213_);
lean_dec_ref(v___x_212_);
v___x_214_ = lp_tree_Formalism_HC_Frame_cc(v_00_u03c6_209_);
v___x_215_ = lean_apply_1(v_toFun_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_conj___boxed(lean_object* v_00_u03c6_216_, lean_object* v_H_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_tree_Formalism_HC_HostRaw_conj(v_00_u03c6_216_, v_H_217_);
lean_dec_ref(v_00_u03c6_216_);
return v_res_218_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_HostRaw_psAt___redArg___closed__0(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_psAt___redArg(lean_object* v_H_221_, lean_object* v_p_222_){
_start:
{
lean_object* v_q_223_; lean_object* v_d_224_; lean_object* v_QS_225_; lean_object* v_art_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_q_223_ = lean_ctor_get(v_H_221_, 0);
lean_inc(v_q_223_);
v_d_224_ = lean_ctor_get(v_H_221_, 1);
lean_inc(v_d_224_);
v_QS_225_ = lean_ctor_get(v_H_221_, 2);
lean_inc(v_QS_225_);
v_art_226_ = lean_ctor_get(v_H_221_, 8);
lean_inc_ref(v_art_226_);
lean_dec_ref(v_H_221_);
v___x_227_ = lean_nat_mul(v_QS_225_, v_q_223_);
lean_dec(v_q_223_);
lean_dec(v_QS_225_);
v___x_228_ = lean_nat_mul(v___x_227_, v_d_224_);
lean_dec(v_d_224_);
lean_dec(v___x_227_);
v___x_229_ = lean_nat_gcd(v_p_222_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_nat_dec_eq(v___x_229_, v___x_230_);
lean_dec(v___x_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v___x_228_);
lean_dec_ref(v_art_226_);
lean_dec(v_p_222_);
v___x_232_ = lean_obj_once(&lp_tree_Formalism_HC_HostRaw_psAt___redArg___closed__0, &lp_tree_Formalism_HC_HostRaw_psAt___redArg___closed__0_once, _init_lp_tree_Formalism_HC_HostRaw_psAt___redArg___closed__0);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_fst_235_; lean_object* v_fst_236_; lean_object* v_val_237_; 
v___x_233_ = lp_mathlib_ZMod_unitOfCoprime___redArg(v___x_228_, v_p_222_);
v___x_234_ = lean_apply_1(v_art_226_, v___x_233_);
v_fst_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_fst_235_);
lean_dec_ref(v___x_234_);
v_fst_236_ = lean_ctor_get(v_fst_235_, 0);
lean_inc(v_fst_236_);
lean_dec(v_fst_235_);
v_val_237_ = lean_ctor_get(v_fst_236_, 0);
lean_inc(v_val_237_);
lean_dec(v_fst_236_);
return v_val_237_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_psAt(lean_object* v_00_u03c6_238_, lean_object* v_H_239_, lean_object* v_p_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lp_tree_Formalism_HC_HostRaw_psAt___redArg(v_H_239_, v_p_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_HostRaw_psAt___boxed(lean_object* v_00_u03c6_242_, lean_object* v_H_243_, lean_object* v_p_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_tree_Formalism_HC_HostRaw_psAt(v_00_u03c6_242_, v_H_243_, v_p_244_);
lean_dec_ref(v_00_u03c6_242_);
return v_res_245_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
