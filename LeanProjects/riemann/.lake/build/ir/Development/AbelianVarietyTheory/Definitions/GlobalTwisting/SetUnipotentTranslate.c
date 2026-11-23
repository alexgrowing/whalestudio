// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_lev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_lev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_lev___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_ledTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_ledTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_ledTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_instTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_instTr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_instTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_latTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_latTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_latTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_cmpTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_cmpTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_cmpTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_twTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_twTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_twTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_thTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_thTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_thTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_errTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_errTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_errTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nchTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nchTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nchTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_xdTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_xdTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_sideTr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_sideTr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_sideTr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_ofPt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_ofPt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00GlobalTheory_EX_OB_nPrime_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00GlobalTheory_EX_OB_nPrime_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_setUnipotentTranslate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_setUnipotentTranslate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_lev___redArg(lean_object* v_O_1_, lean_object* v_u_2_){
_start:
{
lean_object* v_ex_3_; lean_object* v_lev_4_; lean_object* v___x_5_; 
v_ex_3_ = lean_ctor_get(v_O_1_, 7);
lean_inc_ref(v_ex_3_);
lean_dec_ref(v_O_1_);
v_lev_4_ = lean_ctor_get(v_ex_3_, 0);
lean_inc_ref(v_lev_4_);
lean_dec_ref(v_ex_3_);
v___x_5_ = lean_apply_1(v_lev_4_, v_u_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_lev(lean_object* v_D_6_, lean_object* v_O_7_, lean_object* v_u_8_){
_start:
{
lean_object* v_ex_9_; lean_object* v_lev_10_; lean_object* v___x_11_; 
v_ex_9_ = lean_ctor_get(v_O_7_, 7);
lean_inc_ref(v_ex_9_);
lean_dec_ref(v_O_7_);
v_lev_10_ = lean_ctor_get(v_ex_9_, 0);
lean_inc_ref(v_lev_10_);
lean_dec_ref(v_ex_9_);
v___x_11_ = lean_apply_1(v_lev_10_, v_u_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_lev___boxed(lean_object* v_D_12_, lean_object* v_O_13_, lean_object* v_u_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_GlobalTheory_EX_OB_Obj_lev(v_D_12_, v_O_13_, v_u_14_);
lean_dec_ref(v_D_12_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th___redArg(lean_object* v_O_16_){
_start:
{
lean_object* v_ex_17_; lean_object* v_th_18_; 
v_ex_17_ = lean_ctor_get(v_O_16_, 7);
v_th_18_ = lean_ctor_get(v_ex_17_, 1);
lean_inc_ref(v_th_18_);
return v_th_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th___redArg___boxed(lean_object* v_O_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_GlobalTheory_EX_OB_Obj_th___redArg(v_O_19_);
lean_dec_ref(v_O_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th(lean_object* v_D_21_, lean_object* v_O_22_){
_start:
{
lean_object* v_ex_23_; lean_object* v_th_24_; 
v_ex_23_ = lean_ctor_get(v_O_22_, 7);
v_th_24_ = lean_ctor_get(v_ex_23_, 1);
lean_inc_ref(v_th_24_);
return v_th_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_th___boxed(lean_object* v_D_25_, lean_object* v_O_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_GlobalTheory_EX_OB_Obj_th(v_D_25_, v_O_26_);
lean_dec_ref(v_O_26_);
lean_dec_ref(v_D_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp___redArg(lean_object* v_O_28_){
_start:
{
lean_object* v_ex_29_; lean_object* v_cmp_30_; 
v_ex_29_ = lean_ctor_get(v_O_28_, 7);
v_cmp_30_ = lean_ctor_get(v_ex_29_, 2);
lean_inc_ref(v_cmp_30_);
return v_cmp_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp___redArg___boxed(lean_object* v_O_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_GlobalTheory_EX_OB_Obj_cmp___redArg(v_O_31_);
lean_dec_ref(v_O_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp(lean_object* v_D_33_, lean_object* v_O_34_){
_start:
{
lean_object* v_ex_35_; lean_object* v_cmp_36_; 
v_ex_35_ = lean_ctor_get(v_O_34_, 7);
v_cmp_36_ = lean_ctor_get(v_ex_35_, 2);
lean_inc_ref(v_cmp_36_);
return v_cmp_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_cmp___boxed(lean_object* v_D_37_, lean_object* v_O_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_GlobalTheory_EX_OB_Obj_cmp(v_D_37_, v_O_38_);
lean_dec_ref(v_O_38_);
lean_dec_ref(v_D_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw___redArg(lean_object* v_O_40_){
_start:
{
lean_object* v_ex_41_; lean_object* v_tw_42_; 
v_ex_41_ = lean_ctor_get(v_O_40_, 7);
v_tw_42_ = lean_ctor_get(v_ex_41_, 3);
lean_inc_ref(v_tw_42_);
return v_tw_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw___redArg___boxed(lean_object* v_O_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_GlobalTheory_EX_OB_Obj_tw___redArg(v_O_43_);
lean_dec_ref(v_O_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw(lean_object* v_D_45_, lean_object* v_O_46_){
_start:
{
lean_object* v_ex_47_; lean_object* v_tw_48_; 
v_ex_47_ = lean_ctor_get(v_O_46_, 7);
v_tw_48_ = lean_ctor_get(v_ex_47_, 3);
lean_inc_ref(v_tw_48_);
return v_tw_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_tw___boxed(lean_object* v_D_49_, lean_object* v_O_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_GlobalTheory_EX_OB_Obj_tw(v_D_49_, v_O_50_);
lean_dec_ref(v_O_50_);
lean_dec_ref(v_D_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX___redArg(lean_object* v_O_52_){
_start:
{
lean_object* v_ex_53_; lean_object* v_errX_54_; 
v_ex_53_ = lean_ctor_get(v_O_52_, 7);
v_errX_54_ = lean_ctor_get(v_ex_53_, 5);
lean_inc_ref(v_errX_54_);
return v_errX_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX___redArg___boxed(lean_object* v_O_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_tree_GlobalTheory_EX_OB_Obj_errX___redArg(v_O_55_);
lean_dec_ref(v_O_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX(lean_object* v_D_57_, lean_object* v_O_58_){
_start:
{
lean_object* v_ex_59_; lean_object* v_errX_60_; 
v_ex_59_ = lean_ctor_get(v_O_58_, 7);
v_errX_60_ = lean_ctor_get(v_ex_59_, 5);
lean_inc_ref(v_errX_60_);
return v_errX_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_errX___boxed(lean_object* v_D_61_, lean_object* v_O_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_tree_GlobalTheory_EX_OB_Obj_errX(v_D_61_, v_O_62_);
lean_dec_ref(v_O_62_);
lean_dec_ref(v_D_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch___redArg(lean_object* v_O_64_){
_start:
{
lean_object* v_ex_65_; lean_object* v_nch_66_; 
v_ex_65_ = lean_ctor_get(v_O_64_, 7);
v_nch_66_ = lean_ctor_get(v_ex_65_, 6);
lean_inc_ref(v_nch_66_);
return v_nch_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch___redArg___boxed(lean_object* v_O_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_GlobalTheory_EX_OB_Obj_nch___redArg(v_O_67_);
lean_dec_ref(v_O_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch(lean_object* v_D_69_, lean_object* v_O_70_){
_start:
{
lean_object* v_ex_71_; lean_object* v_nch_72_; 
v_ex_71_ = lean_ctor_get(v_O_70_, 7);
v_nch_72_ = lean_ctor_get(v_ex_71_, 6);
lean_inc_ref(v_nch_72_);
return v_nch_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_nch___boxed(lean_object* v_D_73_, lean_object* v_O_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_tree_GlobalTheory_EX_OB_Obj_nch(v_D_73_, v_O_74_);
lean_dec_ref(v_O_74_);
lean_dec_ref(v_D_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd___redArg(lean_object* v_O_76_){
_start:
{
lean_object* v_ex_77_; lean_object* v_xd_78_; 
v_ex_77_ = lean_ctor_get(v_O_76_, 7);
v_xd_78_ = lean_ctor_get(v_ex_77_, 7);
lean_inc(v_xd_78_);
return v_xd_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd___redArg___boxed(lean_object* v_O_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_tree_GlobalTheory_EX_OB_Obj_xd___redArg(v_O_79_);
lean_dec_ref(v_O_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd(lean_object* v_D_81_, lean_object* v_O_82_){
_start:
{
lean_object* v_ex_83_; lean_object* v_xd_84_; 
v_ex_83_ = lean_ctor_get(v_O_82_, 7);
v_xd_84_ = lean_ctor_get(v_ex_83_, 7);
lean_inc(v_xd_84_);
return v_xd_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_xd___boxed(lean_object* v_D_85_, lean_object* v_O_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_GlobalTheory_EX_OB_Obj_xd(v_D_85_, v_O_86_);
lean_dec_ref(v_O_86_);
lean_dec_ref(v_D_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0___redArg(lean_object* v_O_88_){
_start:
{
lean_object* v_ex_89_; lean_object* v_p0_90_; 
v_ex_89_ = lean_ctor_get(v_O_88_, 7);
v_p0_90_ = lean_ctor_get(v_ex_89_, 8);
lean_inc_ref(v_p0_90_);
return v_p0_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0___redArg___boxed(lean_object* v_O_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_tree_GlobalTheory_EX_OB_Obj_p0___redArg(v_O_91_);
lean_dec_ref(v_O_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0(lean_object* v_D_93_, lean_object* v_O_94_){
_start:
{
lean_object* v_ex_95_; lean_object* v_p0_96_; 
v_ex_95_ = lean_ctor_get(v_O_94_, 7);
v_p0_96_ = lean_ctor_get(v_ex_95_, 8);
lean_inc_ref(v_p0_96_);
return v_p0_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_p0___boxed(lean_object* v_D_97_, lean_object* v_O_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_tree_GlobalTheory_EX_OB_Obj_p0(v_D_97_, v_O_98_);
lean_dec_ref(v_O_98_);
lean_dec_ref(v_D_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_ledTr___redArg(lean_object* v_L_100_){
_start:
{
lean_object* v_sc_101_; lean_object* v_aT_102_; lean_object* v_bT_103_; lean_object* v_supp_104_; lean_object* v_gain_105_; lean_object* v_F_106_; lean_object* v_E_107_; lean_object* v_tau_108_; lean_object* v_io_109_; lean_object* v_j0_110_; lean_object* v_logDerivativeAtOne_111_; lean_object* v_NuLat_112_; lean_object* v_de2_113_; lean_object* v_LaG_114_; lean_object* v_Sc_115_; lean_object* v_etaSz_116_; lean_object* v_Cc_117_; lean_object* v_TTw_118_; lean_object* v_Ct_119_; lean_object* v_CGam_120_; lean_object* v_wPart_121_; lean_object* v_lenMN_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_sc_101_ = lean_ctor_get(v_L_100_, 0);
v_aT_102_ = lean_ctor_get(v_L_100_, 1);
v_bT_103_ = lean_ctor_get(v_L_100_, 2);
v_supp_104_ = lean_ctor_get(v_L_100_, 3);
v_gain_105_ = lean_ctor_get(v_L_100_, 4);
v_F_106_ = lean_ctor_get(v_L_100_, 5);
v_E_107_ = lean_ctor_get(v_L_100_, 6);
v_tau_108_ = lean_ctor_get(v_L_100_, 7);
v_io_109_ = lean_ctor_get(v_L_100_, 8);
v_j0_110_ = lean_ctor_get(v_L_100_, 9);
v_logDerivativeAtOne_111_ = lean_ctor_get(v_L_100_, 10);
v_NuLat_112_ = lean_ctor_get(v_L_100_, 11);
v_de2_113_ = lean_ctor_get(v_L_100_, 12);
v_LaG_114_ = lean_ctor_get(v_L_100_, 13);
v_Sc_115_ = lean_ctor_get(v_L_100_, 14);
v_etaSz_116_ = lean_ctor_get(v_L_100_, 15);
v_Cc_117_ = lean_ctor_get(v_L_100_, 16);
v_TTw_118_ = lean_ctor_get(v_L_100_, 17);
v_Ct_119_ = lean_ctor_get(v_L_100_, 18);
v_CGam_120_ = lean_ctor_get(v_L_100_, 19);
v_wPart_121_ = lean_ctor_get(v_L_100_, 20);
v_lenMN_122_ = lean_ctor_get(v_L_100_, 21);
v_isSharedCheck_129_ = !lean_is_exclusive(v_L_100_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v_L_100_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_lenMN_122_);
lean_inc(v_wPart_121_);
lean_inc(v_CGam_120_);
lean_inc(v_Ct_119_);
lean_inc(v_TTw_118_);
lean_inc(v_Cc_117_);
lean_inc(v_etaSz_116_);
lean_inc(v_Sc_115_);
lean_inc(v_LaG_114_);
lean_inc(v_de2_113_);
lean_inc(v_NuLat_112_);
lean_inc(v_logDerivativeAtOne_111_);
lean_inc(v_j0_110_);
lean_inc(v_io_109_);
lean_inc(v_tau_108_);
lean_inc(v_E_107_);
lean_inc(v_F_106_);
lean_inc(v_gain_105_);
lean_inc(v_supp_104_);
lean_inc(v_bT_103_);
lean_inc(v_aT_102_);
lean_inc(v_sc_101_);
lean_dec(v_L_100_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_sc_101_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_aT_102_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_bT_103_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_supp_104_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_gain_105_);
lean_ctor_set(v_reuseFailAlloc_128_, 5, v_F_106_);
lean_ctor_set(v_reuseFailAlloc_128_, 6, v_E_107_);
lean_ctor_set(v_reuseFailAlloc_128_, 7, v_tau_108_);
lean_ctor_set(v_reuseFailAlloc_128_, 8, v_io_109_);
lean_ctor_set(v_reuseFailAlloc_128_, 9, v_j0_110_);
lean_ctor_set(v_reuseFailAlloc_128_, 10, v_logDerivativeAtOne_111_);
lean_ctor_set(v_reuseFailAlloc_128_, 11, v_NuLat_112_);
lean_ctor_set(v_reuseFailAlloc_128_, 12, v_de2_113_);
lean_ctor_set(v_reuseFailAlloc_128_, 13, v_LaG_114_);
lean_ctor_set(v_reuseFailAlloc_128_, 14, v_Sc_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 15, v_etaSz_116_);
lean_ctor_set(v_reuseFailAlloc_128_, 16, v_Cc_117_);
lean_ctor_set(v_reuseFailAlloc_128_, 17, v_TTw_118_);
lean_ctor_set(v_reuseFailAlloc_128_, 18, v_Ct_119_);
lean_ctor_set(v_reuseFailAlloc_128_, 19, v_CGam_120_);
lean_ctor_set(v_reuseFailAlloc_128_, 20, v_wPart_121_);
lean_ctor_set(v_reuseFailAlloc_128_, 21, v_lenMN_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_ledTr(lean_object* v_D_130_, lean_object* v_N_131_, lean_object* v_h_132_, lean_object* v_L_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lp_tree_GlobalTheory_EX_OB_ledTr___redArg(v_L_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_ledTr___boxed(lean_object* v_D_135_, lean_object* v_N_136_, lean_object* v_h_137_, lean_object* v_L_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_tree_GlobalTheory_EX_OB_ledTr(v_D_135_, v_N_136_, v_h_137_, v_L_138_);
lean_dec(v_h_137_);
lean_dec_ref(v_N_136_);
lean_dec_ref(v_D_135_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_instTr___redArg(lean_object* v_X_140_){
_start:
{
lean_object* v_bs_141_; lean_object* v_off_142_; lean_object* v_kapI_143_; lean_object* v_ep_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_bs_141_ = lean_ctor_get(v_X_140_, 0);
v_off_142_ = lean_ctor_get(v_X_140_, 1);
v_kapI_143_ = lean_ctor_get(v_X_140_, 2);
v_ep_144_ = lean_ctor_get(v_X_140_, 3);
v_isSharedCheck_151_ = !lean_is_exclusive(v_X_140_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v_X_140_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_ep_144_);
lean_inc(v_kapI_143_);
lean_inc(v_off_142_);
lean_inc(v_bs_141_);
lean_dec(v_X_140_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_bs_141_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_off_142_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_kapI_143_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_ep_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_instTr(lean_object* v_D_152_, lean_object* v_N_153_, lean_object* v_h_154_, lean_object* v_L_155_, lean_object* v_X_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lp_tree_GlobalTheory_EX_OB_instTr___redArg(v_X_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_instTr___boxed(lean_object* v_D_158_, lean_object* v_N_159_, lean_object* v_h_160_, lean_object* v_L_161_, lean_object* v_X_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_tree_GlobalTheory_EX_OB_instTr(v_D_158_, v_N_159_, v_h_160_, v_L_161_, v_X_162_);
lean_dec_ref(v_L_161_);
lean_dec(v_h_160_);
lean_dec_ref(v_N_159_);
lean_dec_ref(v_D_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr___redArg(lean_object* v_x_164_){
_start:
{
lean_inc_ref(v_x_164_);
return v_x_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr___redArg___boxed(lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_tree_GlobalTheory_EX_OB_gatTr___redArg(v_x_165_);
lean_dec_ref(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr(lean_object* v_D_167_, lean_object* v_N_168_, lean_object* v_h_169_, lean_object* v_x_170_){
_start:
{
lean_inc_ref(v_x_170_);
return v_x_170_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_gatTr___boxed(lean_object* v_D_171_, lean_object* v_N_172_, lean_object* v_h_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = lp_tree_GlobalTheory_EX_OB_gatTr(v_D_171_, v_N_172_, v_h_173_, v_x_174_);
lean_dec_ref(v_x_174_);
lean_dec(v_h_173_);
lean_dec_ref(v_N_172_);
lean_dec_ref(v_D_171_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_latTr___redArg(lean_object* v_x_176_){
_start:
{
lean_object* v_vOf_177_; lean_object* v_Fl_178_; lean_object* v_Lv_179_; lean_object* v_Ch_180_; lean_object* v_Vram_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_vOf_177_ = lean_ctor_get(v_x_176_, 0);
v_Fl_178_ = lean_ctor_get(v_x_176_, 1);
v_Lv_179_ = lean_ctor_get(v_x_176_, 2);
v_Ch_180_ = lean_ctor_get(v_x_176_, 3);
v_Vram_181_ = lean_ctor_get(v_x_176_, 4);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_176_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v_x_176_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_Vram_181_);
lean_inc(v_Ch_180_);
lean_inc(v_Lv_179_);
lean_inc(v_Fl_178_);
lean_inc(v_vOf_177_);
lean_dec(v_x_176_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_vOf_177_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_Fl_178_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_Lv_179_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_Ch_180_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v_Vram_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_latTr(lean_object* v_D_189_, lean_object* v_N_190_, lean_object* v_h_191_, lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lp_tree_GlobalTheory_EX_OB_latTr___redArg(v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_latTr___boxed(lean_object* v_D_194_, lean_object* v_N_195_, lean_object* v_h_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_tree_GlobalTheory_EX_OB_latTr(v_D_194_, v_N_195_, v_h_196_, v_x_197_);
lean_dec(v_h_196_);
lean_dec_ref(v_N_195_);
lean_dec_ref(v_D_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_cmpTr___redArg(lean_object* v_x_199_){
_start:
{
lean_object* v_embW_200_; lean_object* v_cmp_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_embW_200_ = lean_ctor_get(v_x_199_, 0);
v_cmp_201_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v_x_199_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_cmp_201_);
lean_inc(v_embW_200_);
lean_dec(v_x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_embW_200_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_cmp_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_cmpTr(lean_object* v_D_209_, lean_object* v_N_210_, lean_object* v_h_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lp_tree_GlobalTheory_EX_OB_cmpTr___redArg(v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_cmpTr___boxed(lean_object* v_D_214_, lean_object* v_N_215_, lean_object* v_h_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_tree_GlobalTheory_EX_OB_cmpTr(v_D_214_, v_N_215_, v_h_216_, v_x_217_);
lean_dec(v_h_216_);
lean_dec_ref(v_N_215_);
lean_dec_ref(v_D_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_twTr___redArg(lean_object* v_x_219_){
_start:
{
lean_object* v_A_220_; lean_object* v_fm_221_; lean_object* v_e0_222_; lean_object* v_eMu0_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v_A_220_ = lean_ctor_get(v_x_219_, 0);
v_fm_221_ = lean_ctor_get(v_x_219_, 1);
v_e0_222_ = lean_ctor_get(v_x_219_, 2);
v_eMu0_223_ = lean_ctor_get(v_x_219_, 3);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v_x_219_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_eMu0_223_);
lean_inc(v_e0_222_);
lean_inc(v_fm_221_);
lean_inc(v_A_220_);
lean_dec(v_x_219_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_A_220_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_fm_221_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_e0_222_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_eMu0_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_twTr(lean_object* v_D_231_, lean_object* v_N_232_, lean_object* v_h_233_, lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lp_tree_GlobalTheory_EX_OB_twTr___redArg(v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_twTr___boxed(lean_object* v_D_236_, lean_object* v_N_237_, lean_object* v_h_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = lp_tree_GlobalTheory_EX_OB_twTr(v_D_236_, v_N_237_, v_h_238_, v_x_239_);
lean_dec(v_h_238_);
lean_dec_ref(v_N_237_);
lean_dec_ref(v_D_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_thTr___redArg(lean_object* v_x_241_){
_start:
{
lean_object* v_afAdd_242_; lean_object* v_afMod_243_; lean_object* v_cusp_244_; lean_object* v_pet_245_; lean_object* v_actR_246_; lean_object* v_gfGrp_247_; lean_object* v_actF_248_; lean_object* v_Ksph_249_; lean_object* v_typ_250_; lean_object* v_chrGrp_251_; lean_object* v_infTy_252_; lean_object* v_chrOf_253_; lean_object* v_etaT_254_; lean_object* v_schAdd_255_; lean_object* v_schMod_256_; lean_object* v_kfin_257_; lean_object* v_th_258_; lean_object* v_Xs_259_; lean_object* v_Ys_260_; lean_object* v_iXYs_261_; lean_object* v_iYXm_262_; lean_object* v_YsLow_263_; lean_object* v_conjAF_264_; lean_object* v_fjAdd_265_; lean_object* v_fjMod_266_; lean_object* v_Bper_267_; lean_object* v_Btop_268_; lean_object* v_pos1_269_; lean_object* v_posSym_270_; lean_object* v_colAF_271_; lean_object* v_rowAF_272_; lean_object* v_PhiY_273_; lean_object* v_PhiYup_274_; lean_object* v_mY_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_afAdd_242_ = lean_ctor_get(v_x_241_, 0);
v_afMod_243_ = lean_ctor_get(v_x_241_, 1);
v_cusp_244_ = lean_ctor_get(v_x_241_, 2);
v_pet_245_ = lean_ctor_get(v_x_241_, 3);
v_actR_246_ = lean_ctor_get(v_x_241_, 4);
v_gfGrp_247_ = lean_ctor_get(v_x_241_, 5);
v_actF_248_ = lean_ctor_get(v_x_241_, 6);
v_Ksph_249_ = lean_ctor_get(v_x_241_, 7);
v_typ_250_ = lean_ctor_get(v_x_241_, 8);
v_chrGrp_251_ = lean_ctor_get(v_x_241_, 9);
v_infTy_252_ = lean_ctor_get(v_x_241_, 10);
v_chrOf_253_ = lean_ctor_get(v_x_241_, 11);
v_etaT_254_ = lean_ctor_get(v_x_241_, 12);
v_schAdd_255_ = lean_ctor_get(v_x_241_, 13);
v_schMod_256_ = lean_ctor_get(v_x_241_, 14);
v_kfin_257_ = lean_ctor_get(v_x_241_, 15);
v_th_258_ = lean_ctor_get(v_x_241_, 16);
v_Xs_259_ = lean_ctor_get(v_x_241_, 17);
v_Ys_260_ = lean_ctor_get(v_x_241_, 18);
v_iXYs_261_ = lean_ctor_get(v_x_241_, 19);
v_iYXm_262_ = lean_ctor_get(v_x_241_, 20);
v_YsLow_263_ = lean_ctor_get(v_x_241_, 21);
v_conjAF_264_ = lean_ctor_get(v_x_241_, 22);
v_fjAdd_265_ = lean_ctor_get(v_x_241_, 23);
v_fjMod_266_ = lean_ctor_get(v_x_241_, 24);
v_Bper_267_ = lean_ctor_get(v_x_241_, 25);
v_Btop_268_ = lean_ctor_get(v_x_241_, 26);
v_pos1_269_ = lean_ctor_get(v_x_241_, 27);
v_posSym_270_ = lean_ctor_get(v_x_241_, 28);
v_colAF_271_ = lean_ctor_get(v_x_241_, 29);
v_rowAF_272_ = lean_ctor_get(v_x_241_, 30);
v_PhiY_273_ = lean_ctor_get(v_x_241_, 31);
v_PhiYup_274_ = lean_ctor_get(v_x_241_, 32);
v_mY_275_ = lean_ctor_get(v_x_241_, 33);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v_x_241_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_mY_275_);
lean_inc(v_PhiYup_274_);
lean_inc(v_PhiY_273_);
lean_inc(v_rowAF_272_);
lean_inc(v_colAF_271_);
lean_inc(v_posSym_270_);
lean_inc(v_pos1_269_);
lean_inc(v_Btop_268_);
lean_inc(v_Bper_267_);
lean_inc(v_fjMod_266_);
lean_inc(v_fjAdd_265_);
lean_inc(v_conjAF_264_);
lean_inc(v_YsLow_263_);
lean_inc(v_iYXm_262_);
lean_inc(v_iXYs_261_);
lean_inc(v_Ys_260_);
lean_inc(v_Xs_259_);
lean_inc(v_th_258_);
lean_inc(v_kfin_257_);
lean_inc(v_schMod_256_);
lean_inc(v_schAdd_255_);
lean_inc(v_etaT_254_);
lean_inc(v_chrOf_253_);
lean_inc(v_infTy_252_);
lean_inc(v_chrGrp_251_);
lean_inc(v_typ_250_);
lean_inc(v_Ksph_249_);
lean_inc(v_actF_248_);
lean_inc(v_gfGrp_247_);
lean_inc(v_actR_246_);
lean_inc(v_pet_245_);
lean_inc(v_cusp_244_);
lean_inc(v_afMod_243_);
lean_inc(v_afAdd_242_);
lean_dec(v_x_241_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 34, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_afAdd_242_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_afMod_243_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_cusp_244_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_pet_245_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_actR_246_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_gfGrp_247_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_actF_248_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_Ksph_249_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_typ_250_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_chrGrp_251_);
lean_ctor_set(v_reuseFailAlloc_281_, 10, v_infTy_252_);
lean_ctor_set(v_reuseFailAlloc_281_, 11, v_chrOf_253_);
lean_ctor_set(v_reuseFailAlloc_281_, 12, v_etaT_254_);
lean_ctor_set(v_reuseFailAlloc_281_, 13, v_schAdd_255_);
lean_ctor_set(v_reuseFailAlloc_281_, 14, v_schMod_256_);
lean_ctor_set(v_reuseFailAlloc_281_, 15, v_kfin_257_);
lean_ctor_set(v_reuseFailAlloc_281_, 16, v_th_258_);
lean_ctor_set(v_reuseFailAlloc_281_, 17, v_Xs_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 18, v_Ys_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 19, v_iXYs_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 20, v_iYXm_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 21, v_YsLow_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 22, v_conjAF_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 23, v_fjAdd_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 24, v_fjMod_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 25, v_Bper_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 26, v_Btop_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 27, v_pos1_269_);
lean_ctor_set(v_reuseFailAlloc_281_, 28, v_posSym_270_);
lean_ctor_set(v_reuseFailAlloc_281_, 29, v_colAF_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 30, v_rowAF_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 31, v_PhiY_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 32, v_PhiYup_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 33, v_mY_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_thTr(lean_object* v_D_283_, lean_object* v_N_284_, lean_object* v_h_285_, lean_object* v_x_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lp_tree_GlobalTheory_EX_OB_thTr___redArg(v_x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_thTr___boxed(lean_object* v_D_288_, lean_object* v_N_289_, lean_object* v_h_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_tree_GlobalTheory_EX_OB_thTr(v_D_288_, v_N_289_, v_h_290_, v_x_291_);
lean_dec(v_h_290_);
lean_dec_ref(v_N_289_);
lean_dec_ref(v_D_288_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_errTr___redArg(lean_object* v_x_293_){
_start:
{
lean_object* v_piG_294_; lean_object* v_piT_295_; lean_object* v_vPl_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_piG_294_ = lean_ctor_get(v_x_293_, 0);
v_piT_295_ = lean_ctor_get(v_x_293_, 1);
v_vPl_296_ = lean_ctor_get(v_x_293_, 2);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v_x_293_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_vPl_296_);
lean_inc(v_piT_295_);
lean_inc(v_piG_294_);
lean_dec(v_x_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_piG_294_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_piT_295_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_vPl_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_errTr(lean_object* v_D_304_, lean_object* v_N_305_, lean_object* v_h_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lp_tree_GlobalTheory_EX_OB_errTr___redArg(v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_errTr___boxed(lean_object* v_D_309_, lean_object* v_N_310_, lean_object* v_h_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = lp_tree_GlobalTheory_EX_OB_errTr(v_D_309_, v_N_310_, v_h_311_, v_x_312_);
lean_dec(v_h_311_);
lean_dec_ref(v_N_310_);
lean_dec_ref(v_D_309_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nchTr___redArg(lean_object* v_x_314_){
_start:
{
lean_object* v_twI_315_; lean_object* v_sd_316_; lean_object* v_Q_317_; lean_object* v_k_x27_318_; lean_object* v_psi_x27_319_; lean_object* v_crOe_320_; lean_object* v_algOe_321_; lean_object* v_algOOe_322_; lean_object* v_embW_323_; lean_object* v_eMt_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_twI_315_ = lean_ctor_get(v_x_314_, 0);
v_sd_316_ = lean_ctor_get(v_x_314_, 1);
v_Q_317_ = lean_ctor_get(v_x_314_, 2);
v_k_x27_318_ = lean_ctor_get(v_x_314_, 3);
v_psi_x27_319_ = lean_ctor_get(v_x_314_, 4);
v_crOe_320_ = lean_ctor_get(v_x_314_, 5);
v_algOe_321_ = lean_ctor_get(v_x_314_, 6);
v_algOOe_322_ = lean_ctor_get(v_x_314_, 7);
v_embW_323_ = lean_ctor_get(v_x_314_, 8);
v_eMt_324_ = lean_ctor_get(v_x_314_, 9);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v_x_314_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_eMt_324_);
lean_inc(v_embW_323_);
lean_inc(v_algOOe_322_);
lean_inc(v_algOe_321_);
lean_inc(v_crOe_320_);
lean_inc(v_psi_x27_319_);
lean_inc(v_k_x27_318_);
lean_inc(v_Q_317_);
lean_inc(v_sd_316_);
lean_inc(v_twI_315_);
lean_dec(v_x_314_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_twI_315_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_sd_316_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_Q_317_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_k_x27_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_psi_x27_319_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v_crOe_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_algOe_321_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_algOOe_322_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_embW_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 9, v_eMt_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nchTr(lean_object* v_D_332_, lean_object* v_N_333_, lean_object* v_h_334_, lean_object* v_x_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lp_tree_GlobalTheory_EX_OB_nchTr___redArg(v_x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nchTr___boxed(lean_object* v_D_337_, lean_object* v_N_338_, lean_object* v_h_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = lp_tree_GlobalTheory_EX_OB_nchTr(v_D_337_, v_N_338_, v_h_339_, v_x_340_);
lean_dec(v_h_339_);
lean_dec_ref(v_N_338_);
lean_dec_ref(v_D_337_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_xdTr(lean_object* v_D_342_, lean_object* v_N_343_, lean_object* v_h_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_box(0);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_xdTr___boxed(lean_object* v_D_347_, lean_object* v_N_348_, lean_object* v_h_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = lp_tree_GlobalTheory_EX_OB_xdTr(v_D_347_, v_N_348_, v_h_349_, v_x_350_);
lean_dec(v_h_349_);
lean_dec_ref(v_N_348_);
lean_dec_ref(v_D_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr___redArg___lam__0(lean_object* v_md_352_, lean_object* v_S_353_, lean_object* v_00_u03ba_354_, lean_object* v_p_355_, lean_object* v_x_356_, lean_object* v_la_357_, lean_object* v_z_358_){
_start:
{
lean_object* v___x_359_; lean_object* v_Z_360_; lean_object* v_cov_361_; lean_object* v_lvl_362_; lean_object* v_lie_363_; lean_object* v_om_364_; lean_object* v_lieW_365_; lean_object* v_omW_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v___x_359_ = lean_apply_6(v_md_352_, v_S_353_, v_00_u03ba_354_, v_p_355_, lean_box(0), v_la_357_, v_z_358_);
v_Z_360_ = lean_ctor_get(v___x_359_, 0);
v_cov_361_ = lean_ctor_get(v___x_359_, 1);
v_lvl_362_ = lean_ctor_get(v___x_359_, 2);
v_lie_363_ = lean_ctor_get(v___x_359_, 3);
v_om_364_ = lean_ctor_get(v___x_359_, 4);
v_lieW_365_ = lean_ctor_get(v___x_359_, 5);
v_omW_366_ = lean_ctor_get(v___x_359_, 6);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_359_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_omW_366_);
lean_inc(v_lieW_365_);
lean_inc(v_om_364_);
lean_inc(v_lie_363_);
lean_inc(v_lvl_362_);
lean_inc(v_cov_361_);
lean_inc(v_Z_360_);
lean_dec(v___x_359_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_Z_360_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_cov_361_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_lvl_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_lie_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_om_364_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_lieW_365_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_omW_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr___redArg(lean_object* v_X_374_){
_start:
{
lean_object* v_geo_375_; lean_object* v_levPr_376_; lean_object* v_shv_377_; lean_object* v_plpFin_378_; lean_object* v_wtP_379_; lean_object* v_plP_380_; lean_object* v_jC_381_; lean_object* v_md_382_; lean_object* v_vdd_383_; lean_object* v_degM_384_; lean_object* v_htMdl_385_; lean_object* v_htCurve_386_; lean_object* v_MjH_387_; lean_object* v_jM_388_; lean_object* v_Qp_389_; lean_object* v_finQ_390_; lean_object* v_qv_391_; lean_object* v_nu_392_; lean_object* v_ZQ_393_; lean_object* v_quotientLocalValueFirst_394_; lean_object* v_typeDim_395_; lean_object* v_compFin_396_; lean_object* v_degHH_397_; lean_object* v_Yv_398_; lean_object* v_Ybd_399_; lean_object* v_Lw_400_; lean_object* v_iMj_401_; lean_object* v_logLam_402_; lean_object* v_kapR_403_; lean_object* v_surfCh2_404_; lean_object* v_surfDegOm_405_; lean_object* v_surfFpCh2_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_414_; 
v_geo_375_ = lean_ctor_get(v_X_374_, 0);
v_levPr_376_ = lean_ctor_get(v_X_374_, 1);
v_shv_377_ = lean_ctor_get(v_X_374_, 2);
v_plpFin_378_ = lean_ctor_get(v_X_374_, 3);
v_wtP_379_ = lean_ctor_get(v_X_374_, 4);
v_plP_380_ = lean_ctor_get(v_X_374_, 5);
v_jC_381_ = lean_ctor_get(v_X_374_, 6);
v_md_382_ = lean_ctor_get(v_X_374_, 7);
v_vdd_383_ = lean_ctor_get(v_X_374_, 8);
v_degM_384_ = lean_ctor_get(v_X_374_, 9);
v_htMdl_385_ = lean_ctor_get(v_X_374_, 10);
v_htCurve_386_ = lean_ctor_get(v_X_374_, 11);
v_MjH_387_ = lean_ctor_get(v_X_374_, 12);
v_jM_388_ = lean_ctor_get(v_X_374_, 13);
v_Qp_389_ = lean_ctor_get(v_X_374_, 14);
v_finQ_390_ = lean_ctor_get(v_X_374_, 15);
v_qv_391_ = lean_ctor_get(v_X_374_, 16);
v_nu_392_ = lean_ctor_get(v_X_374_, 17);
v_ZQ_393_ = lean_ctor_get(v_X_374_, 18);
v_quotientLocalValueFirst_394_ = lean_ctor_get(v_X_374_, 19);
v_typeDim_395_ = lean_ctor_get(v_X_374_, 20);
v_compFin_396_ = lean_ctor_get(v_X_374_, 21);
v_degHH_397_ = lean_ctor_get(v_X_374_, 22);
v_Yv_398_ = lean_ctor_get(v_X_374_, 23);
v_Ybd_399_ = lean_ctor_get(v_X_374_, 24);
v_Lw_400_ = lean_ctor_get(v_X_374_, 25);
v_iMj_401_ = lean_ctor_get(v_X_374_, 26);
v_logLam_402_ = lean_ctor_get(v_X_374_, 27);
v_kapR_403_ = lean_ctor_get(v_X_374_, 28);
v_surfCh2_404_ = lean_ctor_get(v_X_374_, 29);
v_surfDegOm_405_ = lean_ctor_get(v_X_374_, 30);
v_surfFpCh2_406_ = lean_ctor_get(v_X_374_, 31);
v_isSharedCheck_414_ = !lean_is_exclusive(v_X_374_);
if (v_isSharedCheck_414_ == 0)
{
v___x_408_ = v_X_374_;
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_surfFpCh2_406_);
lean_inc(v_surfDegOm_405_);
lean_inc(v_surfCh2_404_);
lean_inc(v_kapR_403_);
lean_inc(v_logLam_402_);
lean_inc(v_iMj_401_);
lean_inc(v_Lw_400_);
lean_inc(v_Ybd_399_);
lean_inc(v_Yv_398_);
lean_inc(v_degHH_397_);
lean_inc(v_compFin_396_);
lean_inc(v_typeDim_395_);
lean_inc(v_quotientLocalValueFirst_394_);
lean_inc(v_ZQ_393_);
lean_inc(v_nu_392_);
lean_inc(v_qv_391_);
lean_inc(v_finQ_390_);
lean_inc(v_Qp_389_);
lean_inc(v_jM_388_);
lean_inc(v_MjH_387_);
lean_inc(v_htCurve_386_);
lean_inc(v_htMdl_385_);
lean_inc(v_degM_384_);
lean_inc(v_vdd_383_);
lean_inc(v_md_382_);
lean_inc(v_jC_381_);
lean_inc(v_plP_380_);
lean_inc(v_wtP_379_);
lean_inc(v_plpFin_378_);
lean_inc(v_shv_377_);
lean_inc(v_levPr_376_);
lean_inc(v_geo_375_);
lean_dec(v_X_374_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___f_410_; lean_object* v___x_412_; 
v___f_410_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_EX_OB_divTr___redArg___lam__0), 7, 1);
lean_closure_set(v___f_410_, 0, v_md_382_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 7, v___f_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 32, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_geo_375_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_levPr_376_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_shv_377_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_plpFin_378_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_wtP_379_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_plP_380_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_jC_381_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v___f_410_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_vdd_383_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_degM_384_);
lean_ctor_set(v_reuseFailAlloc_413_, 10, v_htMdl_385_);
lean_ctor_set(v_reuseFailAlloc_413_, 11, v_htCurve_386_);
lean_ctor_set(v_reuseFailAlloc_413_, 12, v_MjH_387_);
lean_ctor_set(v_reuseFailAlloc_413_, 13, v_jM_388_);
lean_ctor_set(v_reuseFailAlloc_413_, 14, v_Qp_389_);
lean_ctor_set(v_reuseFailAlloc_413_, 15, v_finQ_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 16, v_qv_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 17, v_nu_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 18, v_ZQ_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 19, v_quotientLocalValueFirst_394_);
lean_ctor_set(v_reuseFailAlloc_413_, 20, v_typeDim_395_);
lean_ctor_set(v_reuseFailAlloc_413_, 21, v_compFin_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 22, v_degHH_397_);
lean_ctor_set(v_reuseFailAlloc_413_, 23, v_Yv_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 24, v_Ybd_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 25, v_Lw_400_);
lean_ctor_set(v_reuseFailAlloc_413_, 26, v_iMj_401_);
lean_ctor_set(v_reuseFailAlloc_413_, 27, v_logLam_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 28, v_kapR_403_);
lean_ctor_set(v_reuseFailAlloc_413_, 29, v_surfCh2_404_);
lean_ctor_set(v_reuseFailAlloc_413_, 30, v_surfDegOm_405_);
lean_ctor_set(v_reuseFailAlloc_413_, 31, v_surfFpCh2_406_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr(lean_object* v_D_415_, lean_object* v_N_416_, lean_object* v_h_417_, lean_object* v_X_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lp_tree_GlobalTheory_EX_OB_divTr___redArg(v_X_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_divTr___boxed(lean_object* v_D_420_, lean_object* v_N_421_, lean_object* v_h_422_, lean_object* v_X_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = lp_tree_GlobalTheory_EX_OB_divTr(v_D_420_, v_N_421_, v_h_422_, v_X_423_);
lean_dec(v_h_422_);
lean_dec_ref(v_N_421_);
lean_dec_ref(v_D_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_sideTr___redArg(lean_object* v_S_425_){
_start:
{
lean_object* v_instAmb_426_; lean_object* v_instAmbi_427_; lean_object* v_instMult_428_; lean_object* v_instMulti_429_; lean_object* v_multZero_430_; lean_object* v_multTop_431_; lean_object* v_io_432_; lean_object* v_Mtilde_433_; lean_object* v_cen_434_; lean_object* v_eOp_435_; lean_object* v_RR_436_; lean_object* v_jEE_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_instAmb_426_ = lean_ctor_get(v_S_425_, 0);
v_instAmbi_427_ = lean_ctor_get(v_S_425_, 1);
v_instMult_428_ = lean_ctor_get(v_S_425_, 2);
v_instMulti_429_ = lean_ctor_get(v_S_425_, 3);
v_multZero_430_ = lean_ctor_get(v_S_425_, 4);
v_multTop_431_ = lean_ctor_get(v_S_425_, 5);
v_io_432_ = lean_ctor_get(v_S_425_, 6);
v_Mtilde_433_ = lean_ctor_get(v_S_425_, 7);
v_cen_434_ = lean_ctor_get(v_S_425_, 8);
v_eOp_435_ = lean_ctor_get(v_S_425_, 9);
v_RR_436_ = lean_ctor_get(v_S_425_, 10);
v_jEE_437_ = lean_ctor_get(v_S_425_, 11);
v_isSharedCheck_444_ = !lean_is_exclusive(v_S_425_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v_S_425_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_jEE_437_);
lean_inc(v_RR_436_);
lean_inc(v_eOp_435_);
lean_inc(v_cen_434_);
lean_inc(v_Mtilde_433_);
lean_inc(v_io_432_);
lean_inc(v_multTop_431_);
lean_inc(v_multZero_430_);
lean_inc(v_instMulti_429_);
lean_inc(v_instMult_428_);
lean_inc(v_instAmbi_427_);
lean_inc(v_instAmb_426_);
lean_dec(v_S_425_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_instAmb_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_instAmbi_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_instMult_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_instMulti_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_multZero_430_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_multTop_431_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_io_432_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_Mtilde_433_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_cen_434_);
lean_ctor_set(v_reuseFailAlloc_443_, 9, v_eOp_435_);
lean_ctor_set(v_reuseFailAlloc_443_, 10, v_RR_436_);
lean_ctor_set(v_reuseFailAlloc_443_, 11, v_jEE_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_sideTr(lean_object* v_D_445_, lean_object* v_N_446_, lean_object* v_h_447_, lean_object* v_EE_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_S_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = lp_tree_GlobalTheory_EX_OB_sideTr___redArg(v_S_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_sideTr___boxed(lean_object* v_D_454_, lean_object* v_N_455_, lean_object* v_h_456_, lean_object* v_EE_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_S_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = lp_tree_GlobalTheory_EX_OB_sideTr(v_D_454_, v_N_455_, v_h_456_, v_EE_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_S_461_);
lean_dec_ref(v_inst_459_);
lean_dec_ref(v_inst_458_);
lean_dec(v_h_456_);
lean_dec_ref(v_N_455_);
lean_dec_ref(v_D_454_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___redArg(lean_object* v_x_463_, lean_object* v_h__1_464_, lean_object* v_h__2_465_){
_start:
{
lean_object* v_zero_466_; uint8_t v_isZero_467_; 
v_zero_466_ = lean_unsigned_to_nat(0u);
v_isZero_467_ = lean_nat_dec_eq(v_x_463_, v_zero_466_);
if (v_isZero_467_ == 1)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_h__2_465_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_apply_1(v_h__1_464_, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v_one_470_; lean_object* v_n_471_; lean_object* v___x_472_; 
lean_dec(v_h__1_464_);
v_one_470_ = lean_unsigned_to_nat(1u);
v_n_471_ = lean_nat_sub(v_x_463_, v_one_470_);
v___x_472_ = lean_apply_1(v_h__2_465_, v_n_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___redArg___boxed(lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___redArg(v_x_473_, v_h__1_474_, v_h__2_475_);
lean_dec(v_x_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter(lean_object* v_motive_477_, lean_object* v_x_478_, lean_object* v_h__1_479_, lean_object* v_h__2_480_){
_start:
{
lean_object* v_zero_481_; uint8_t v_isZero_482_; 
v_zero_481_ = lean_unsigned_to_nat(0u);
v_isZero_482_ = lean_nat_dec_eq(v_x_478_, v_zero_481_);
if (v_isZero_482_ == 1)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v_h__2_480_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_apply_1(v_h__1_479_, v___x_483_);
return v___x_484_;
}
else
{
lean_object* v_one_485_; lean_object* v_n_486_; lean_object* v___x_487_; 
lean_dec(v_h__1_479_);
v_one_485_ = lean_unsigned_to_nat(1u);
v_n_486_ = lean_nat_sub(v_x_478_, v_one_485_);
v___x_487_ = lean_apply_1(v_h__2_480_, v_n_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter___boxed(lean_object* v_motive_488_, lean_object* v_x_489_, lean_object* v_h__1_490_, lean_object* v_h__2_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = lp_tree___private_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate_0__Formalism_BasicNotions_RowSide_downTo_match__1_splitter(v_motive_488_, v_x_489_, v_h__1_490_, v_h__2_491_);
lean_dec(v_x_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_ofPt(lean_object* v_C_493_, lean_object* v_p_494_){
_start:
{
lean_object* v_ta_495_; lean_object* v_xa_496_; lean_object* v_L_497_; lean_object* v_gatT_498_; lean_object* v_Gx_499_; lean_object* v_Gy_500_; lean_object* v_GK_501_; lean_object* v_cX_502_; lean_object* v_X_503_; lean_object* v_ex_504_; lean_object* v___x_505_; 
v_ta_495_ = lean_ctor_get(v_p_494_, 3);
v_xa_496_ = lean_ctor_get(v_p_494_, 4);
v_L_497_ = lean_ctor_get(v_p_494_, 1);
v_gatT_498_ = lean_ctor_get(v_p_494_, 2);
v_Gx_499_ = lean_ctor_get(v_ta_495_, 0);
v_Gy_500_ = lean_ctor_get(v_ta_495_, 1);
v_GK_501_ = lean_ctor_get(v_C_493_, 9);
v_cX_502_ = lean_ctor_get(v_C_493_, 10);
v_X_503_ = lean_ctor_get(v_xa_496_, 0);
v_ex_504_ = lean_ctor_get(v_xa_496_, 1);
lean_inc_ref(v_ex_504_);
lean_inc_ref(v_cX_502_);
lean_inc_ref(v_X_503_);
lean_inc_ref(v_GK_501_);
lean_inc_ref(v_Gy_500_);
lean_inc_ref(v_Gx_499_);
lean_inc_ref(v_gatT_498_);
lean_inc_ref(v_L_497_);
v___x_505_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_505_, 0, v_L_497_);
lean_ctor_set(v___x_505_, 1, v_gatT_498_);
lean_ctor_set(v___x_505_, 2, v_Gx_499_);
lean_ctor_set(v___x_505_, 3, v_Gy_500_);
lean_ctor_set(v___x_505_, 4, v_GK_501_);
lean_ctor_set(v___x_505_, 5, v_X_503_);
lean_ctor_set(v___x_505_, 6, v_cX_502_);
lean_ctor_set(v___x_505_, 7, v_ex_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Obj_ofPt___boxed(lean_object* v_C_506_, lean_object* v_p_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = lp_tree_GlobalTheory_EX_OB_Obj_ofPt(v_C_506_, v_p_507_);
lean_dec_ref(v_p_507_);
lean_dec_ref(v_C_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg(lean_object* v_Y_509_){
_start:
{
lean_object* v_lev_510_; lean_object* v_th_511_; lean_object* v_cmp_512_; lean_object* v_tw_513_; lean_object* v_ker_514_; lean_object* v_errX_515_; lean_object* v_nch_516_; lean_object* v_xd_517_; lean_object* v_p0_518_; lean_object* v_amb_519_; lean_object* v_amb0_520_; lean_object* v_gauge_521_; lean_object* v___x_522_; 
v_lev_510_ = lean_ctor_get(v_Y_509_, 2);
v_th_511_ = lean_ctor_get(v_Y_509_, 3);
v_cmp_512_ = lean_ctor_get(v_Y_509_, 4);
v_tw_513_ = lean_ctor_get(v_Y_509_, 5);
v_ker_514_ = lean_ctor_get(v_Y_509_, 7);
v_errX_515_ = lean_ctor_get(v_Y_509_, 8);
v_nch_516_ = lean_ctor_get(v_Y_509_, 9);
v_xd_517_ = lean_ctor_get(v_Y_509_, 10);
lean_inc(v_xd_517_);
v_p0_518_ = lean_ctor_get(v_Y_509_, 11);
v_amb_519_ = lean_ctor_get(v_Y_509_, 12);
v_amb0_520_ = lean_ctor_get(v_Y_509_, 13);
v_gauge_521_ = lean_ctor_get(v_Y_509_, 14);
lean_inc_ref(v_gauge_521_);
lean_inc_ref(v_amb0_520_);
lean_inc_ref(v_amb_519_);
lean_inc_ref(v_p0_518_);
lean_inc_ref(v_nch_516_);
lean_inc_ref(v_errX_515_);
lean_inc_ref(v_ker_514_);
lean_inc_ref(v_tw_513_);
lean_inc_ref(v_cmp_512_);
lean_inc_ref(v_th_511_);
lean_inc_ref(v_lev_510_);
v___x_522_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_522_, 0, v_lev_510_);
lean_ctor_set(v___x_522_, 1, v_th_511_);
lean_ctor_set(v___x_522_, 2, v_cmp_512_);
lean_ctor_set(v___x_522_, 3, v_tw_513_);
lean_ctor_set(v___x_522_, 4, v_ker_514_);
lean_ctor_set(v___x_522_, 5, v_errX_515_);
lean_ctor_set(v___x_522_, 6, v_nch_516_);
lean_ctor_set(v___x_522_, 7, v_xd_517_);
lean_ctor_set(v___x_522_, 8, v_p0_518_);
lean_ctor_set(v___x_522_, 9, v_amb_519_);
lean_ctor_set(v___x_522_, 10, v_amb0_520_);
lean_ctor_set(v___x_522_, 11, v_gauge_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg___boxed(lean_object* v_Y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg(v_Y_523_);
lean_dec_ref(v_Y_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra(lean_object* v_C_525_, lean_object* v_D_526_, lean_object* v_Y_527_, lean_object* v_p_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg(v_Y_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_extra___boxed(lean_object* v_C_530_, lean_object* v_D_531_, lean_object* v_Y_532_, lean_object* v_p_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = lp_tree_GlobalTheory_EX_OB_LedPart_extra(v_C_530_, v_D_531_, v_Y_532_, v_p_533_);
lean_dec_ref(v_p_533_);
lean_dec_ref(v_Y_532_);
lean_dec_ref(v_D_531_);
lean_dec_ref(v_C_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj___redArg(lean_object* v_C_535_, lean_object* v_Y_536_, lean_object* v_p_537_){
_start:
{
lean_object* v_ta_538_; lean_object* v_L_539_; lean_object* v_gatT_540_; lean_object* v_X_541_; lean_object* v_Gy_542_; lean_object* v_Gx_543_; lean_object* v_GK_544_; lean_object* v_cX_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_ta_538_ = lean_ctor_get(v_p_537_, 1);
v_L_539_ = lean_ctor_get(v_p_537_, 0);
v_gatT_540_ = lean_ctor_get(v_Y_536_, 0);
v_X_541_ = lean_ctor_get(v_Y_536_, 1);
v_Gy_542_ = lean_ctor_get(v_Y_536_, 6);
v_Gx_543_ = lean_ctor_get(v_ta_538_, 0);
v_GK_544_ = lean_ctor_get(v_C_535_, 9);
v_cX_545_ = lean_ctor_get(v_C_535_, 10);
v___x_546_ = lp_tree_GlobalTheory_EX_OB_LedPart_extra___redArg(v_Y_536_);
lean_inc_ref(v_cX_545_);
lean_inc_ref(v_X_541_);
lean_inc_ref(v_GK_544_);
lean_inc_ref(v_Gy_542_);
lean_inc_ref(v_Gx_543_);
lean_inc_ref(v_gatT_540_);
lean_inc_ref(v_L_539_);
v___x_547_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_547_, 0, v_L_539_);
lean_ctor_set(v___x_547_, 1, v_gatT_540_);
lean_ctor_set(v___x_547_, 2, v_Gx_543_);
lean_ctor_set(v___x_547_, 3, v_Gy_542_);
lean_ctor_set(v___x_547_, 4, v_GK_544_);
lean_ctor_set(v___x_547_, 5, v_X_541_);
lean_ctor_set(v___x_547_, 6, v_cX_545_);
lean_ctor_set(v___x_547_, 7, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj___redArg___boxed(lean_object* v_C_548_, lean_object* v_Y_549_, lean_object* v_p_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = lp_tree_GlobalTheory_EX_OB_Lay_obj___redArg(v_C_548_, v_Y_549_, v_p_550_);
lean_dec_ref(v_p_550_);
lean_dec_ref(v_Y_549_);
lean_dec_ref(v_C_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj(lean_object* v_C_552_, lean_object* v_D_553_, lean_object* v_Y_554_, lean_object* v_p_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lp_tree_GlobalTheory_EX_OB_Lay_obj___redArg(v_C_552_, v_Y_554_, v_p_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_obj___boxed(lean_object* v_C_557_, lean_object* v_D_558_, lean_object* v_Y_559_, lean_object* v_p_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = lp_tree_GlobalTheory_EX_OB_Lay_obj(v_C_557_, v_D_558_, v_Y_559_, v_p_560_);
lean_dec_ref(v_p_560_);
lean_dec_ref(v_Y_559_);
lean_dec_ref(v_D_558_);
lean_dec_ref(v_C_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00GlobalTheory_EX_OB_nPrime_spec__0(lean_object* v___x_562_, lean_object* v___x_563_, lean_object* v_s_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00GlobalTheory_EX_OB_nPrime_spec__0___boxed(lean_object* v___x_566_, lean_object* v___x_567_, lean_object* v_s_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = lp_tree_Submodule_span___at___00GlobalTheory_EX_OB_nPrime_spec__0(v___x_566_, v___x_567_, v_s_568_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v___x_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime___redArg(lean_object* v_D_570_, lean_object* v_u_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime___redArg___boxed(lean_object* v_D_573_, lean_object* v_u_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = lp_tree_GlobalTheory_EX_OB_nPrime___redArg(v_D_573_, v_u_574_);
lean_dec(v_u_574_);
lean_dec_ref(v_D_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime(lean_object* v_D_576_, lean_object* v_L_577_, lean_object* v_u_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_box(0);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_nPrime___boxed(lean_object* v_D_580_, lean_object* v_L_581_, lean_object* v_u_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = lp_tree_GlobalTheory_EX_OB_nPrime(v_D_580_, v_L_581_, v_u_582_);
lean_dec(v_u_582_);
lean_dec_ref(v_L_581_);
lean_dec_ref(v_D_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt___redArg(lean_object* v_p_584_){
_start:
{
lean_object* v_xa_585_; lean_object* v_ex_586_; lean_object* v_ta_587_; lean_object* v_gatT_588_; lean_object* v_X_589_; lean_object* v_lev_590_; lean_object* v_th_591_; lean_object* v_cmp_592_; lean_object* v_tw_593_; lean_object* v_ker_594_; lean_object* v_errX_595_; lean_object* v_nch_596_; lean_object* v_xd_597_; lean_object* v_p0_598_; lean_object* v_amb_599_; lean_object* v_amb0_600_; lean_object* v_gauge_601_; lean_object* v_Gy_602_; lean_object* v___x_603_; 
v_xa_585_ = lean_ctor_get(v_p_584_, 4);
v_ex_586_ = lean_ctor_get(v_xa_585_, 1);
v_ta_587_ = lean_ctor_get(v_p_584_, 3);
v_gatT_588_ = lean_ctor_get(v_p_584_, 2);
v_X_589_ = lean_ctor_get(v_xa_585_, 0);
v_lev_590_ = lean_ctor_get(v_ex_586_, 0);
v_th_591_ = lean_ctor_get(v_ex_586_, 1);
v_cmp_592_ = lean_ctor_get(v_ex_586_, 2);
v_tw_593_ = lean_ctor_get(v_ex_586_, 3);
v_ker_594_ = lean_ctor_get(v_ex_586_, 4);
v_errX_595_ = lean_ctor_get(v_ex_586_, 5);
v_nch_596_ = lean_ctor_get(v_ex_586_, 6);
v_xd_597_ = lean_ctor_get(v_ex_586_, 7);
lean_inc(v_xd_597_);
v_p0_598_ = lean_ctor_get(v_ex_586_, 8);
v_amb_599_ = lean_ctor_get(v_ex_586_, 9);
v_amb0_600_ = lean_ctor_get(v_ex_586_, 10);
v_gauge_601_ = lean_ctor_get(v_ex_586_, 11);
v_Gy_602_ = lean_ctor_get(v_ta_587_, 1);
lean_inc_ref(v_gauge_601_);
lean_inc_ref(v_amb0_600_);
lean_inc_ref(v_amb_599_);
lean_inc_ref(v_p0_598_);
lean_inc_ref(v_nch_596_);
lean_inc_ref(v_errX_595_);
lean_inc_ref(v_ker_594_);
lean_inc_ref(v_Gy_602_);
lean_inc_ref(v_tw_593_);
lean_inc_ref(v_cmp_592_);
lean_inc_ref(v_th_591_);
lean_inc_ref(v_lev_590_);
lean_inc_ref(v_X_589_);
lean_inc_ref(v_gatT_588_);
v___x_603_ = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(v___x_603_, 0, v_gatT_588_);
lean_ctor_set(v___x_603_, 1, v_X_589_);
lean_ctor_set(v___x_603_, 2, v_lev_590_);
lean_ctor_set(v___x_603_, 3, v_th_591_);
lean_ctor_set(v___x_603_, 4, v_cmp_592_);
lean_ctor_set(v___x_603_, 5, v_tw_593_);
lean_ctor_set(v___x_603_, 6, v_Gy_602_);
lean_ctor_set(v___x_603_, 7, v_ker_594_);
lean_ctor_set(v___x_603_, 8, v_errX_595_);
lean_ctor_set(v___x_603_, 9, v_nch_596_);
lean_ctor_set(v___x_603_, 10, v_xd_597_);
lean_ctor_set(v___x_603_, 11, v_p0_598_);
lean_ctor_set(v___x_603_, 12, v_amb_599_);
lean_ctor_set(v___x_603_, 13, v_amb0_600_);
lean_ctor_set(v___x_603_, 14, v_gauge_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt___redArg___boxed(lean_object* v_p_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = lp_tree_GlobalTheory_EX_OB_Lay_ofPt___redArg(v_p_604_);
lean_dec_ref(v_p_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt(lean_object* v_C_606_, lean_object* v_p_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lp_tree_GlobalTheory_EX_OB_Lay_ofPt___redArg(v_p_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_Lay_ofPt___boxed(lean_object* v_C_609_, lean_object* v_p_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = lp_tree_GlobalTheory_EX_OB_Lay_ofPt(v_C_609_, v_p_610_);
lean_dec_ref(v_p_610_);
lean_dec_ref(v_C_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___redArg(lean_object* v_p_612_){
_start:
{
lean_object* v_L_613_; lean_object* v_ta_614_; lean_object* v___x_615_; 
v_L_613_ = lean_ctor_get(v_p_612_, 1);
v_ta_614_ = lean_ctor_get(v_p_612_, 3);
lean_inc_ref(v_ta_614_);
lean_inc_ref(v_L_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_L_613_);
lean_ctor_set(v___x_615_, 1, v_ta_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___redArg___boxed(lean_object* v_p_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___redArg(v_p_616_);
lean_dec_ref(v_p_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt(lean_object* v_C_618_, lean_object* v_p_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___redArg(v_p_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_LedPart_ofPt___boxed(lean_object* v_C_621_, lean_object* v_p_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = lp_tree_GlobalTheory_EX_OB_LedPart_ofPt(v_C_621_, v_p_622_);
lean_dec_ref(v_p_622_);
lean_dec_ref(v_C_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_setUnipotentTranslate(lean_object* v_R_624_, lean_object* v_H_625_, lean_object* v_u0_626_){
_start:
{
lean_object* v_toHostAx_627_; lean_object* v_sqq_628_; lean_object* v_splitBound_629_; lean_object* v_00_u03c6_u2080_630_; lean_object* v_00_U0001d51f_631_; lean_object* v_levelPrimes_632_; lean_object* v_g_633_; lean_object* v_pde_634_; lean_object* v_pde_x27_635_; lean_object* v_ccK_636_; lean_object* v_TT_637_; lean_object* v_T2_638_; lean_object* v_Lw_639_; lean_object* v_CT2_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_649_; 
v_toHostAx_627_ = lean_ctor_get(v_H_625_, 0);
v_sqq_628_ = lean_ctor_get(v_H_625_, 1);
v_splitBound_629_ = lean_ctor_get(v_H_625_, 2);
v_00_u03c6_u2080_630_ = lean_ctor_get(v_H_625_, 3);
v_00_U0001d51f_631_ = lean_ctor_get(v_H_625_, 4);
v_levelPrimes_632_ = lean_ctor_get(v_H_625_, 5);
v_g_633_ = lean_ctor_get(v_H_625_, 6);
v_pde_634_ = lean_ctor_get(v_H_625_, 7);
v_pde_x27_635_ = lean_ctor_get(v_H_625_, 8);
v_ccK_636_ = lean_ctor_get(v_H_625_, 9);
v_TT_637_ = lean_ctor_get(v_H_625_, 10);
v_T2_638_ = lean_ctor_get(v_H_625_, 11);
v_Lw_639_ = lean_ctor_get(v_H_625_, 13);
v_CT2_640_ = lean_ctor_get(v_H_625_, 14);
v_isSharedCheck_649_ = !lean_is_exclusive(v_H_625_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_H_625_, 12);
lean_dec(v_unused_650_);
v___x_642_ = v_H_625_;
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_CT2_640_);
lean_inc(v_Lw_639_);
lean_inc(v_T2_638_);
lean_inc(v_TT_637_);
lean_inc(v_ccK_636_);
lean_inc(v_pde_x27_635_);
lean_inc(v_pde_634_);
lean_inc(v_g_633_);
lean_inc(v_levelPrimes_632_);
lean_inc(v_00_U0001d51f_631_);
lean_inc(v_00_u03c6_u2080_630_);
lean_inc(v_splitBound_629_);
lean_inc(v_sqq_628_);
lean_inc(v_toHostAx_627_);
lean_dec(v_H_625_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_649_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_toFrame_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v_toFrame_644_ = lean_ctor_get(v_R_624_, 0);
v___x_645_ = lp_tree_Formalism_HC_Frame_ofNat(v_toFrame_644_, v_u0_626_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 12, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_toHostAx_627_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_sqq_628_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_splitBound_629_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_00_u03c6_u2080_630_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_00_U0001d51f_631_);
lean_ctor_set(v_reuseFailAlloc_648_, 5, v_levelPrimes_632_);
lean_ctor_set(v_reuseFailAlloc_648_, 6, v_g_633_);
lean_ctor_set(v_reuseFailAlloc_648_, 7, v_pde_634_);
lean_ctor_set(v_reuseFailAlloc_648_, 8, v_pde_x27_635_);
lean_ctor_set(v_reuseFailAlloc_648_, 9, v_ccK_636_);
lean_ctor_set(v_reuseFailAlloc_648_, 10, v_TT_637_);
lean_ctor_set(v_reuseFailAlloc_648_, 11, v_T2_638_);
lean_ctor_set(v_reuseFailAlloc_648_, 12, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 13, v_Lw_639_);
lean_ctor_set(v_reuseFailAlloc_648_, 14, v_CT2_640_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_OB_setUnipotentTranslate___boxed(lean_object* v_R_651_, lean_object* v_H_652_, lean_object* v_u0_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = lp_tree_GlobalTheory_EX_OB_setUnipotentTranslate(v_R_651_, v_H_652_, v_u0_653_);
lean_dec(v_u0_653_);
lean_dec_ref(v_R_651_);
return v_res_654_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LogCondLeThree(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_AuxiliaryPrimeMemAvoidedPrimes(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_DuStarPos(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_AssembleLattice(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRanksRankValFrame(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsHcParamOfCode(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MPowFiveMulFMulLLe(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_KitExOfHostWeightObj(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsWeightsInWindows(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LogCondLeThree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_AuxiliaryPrimeMemAvoidedPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_DuStarPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_AssembleLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRanksRankValFrame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsHcParamOfCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MPowFiveMulFMulLLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_KitExOfHostWeightObj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsWeightsInWindows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
