// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
// Imports: public import Init public meta import Init public import Mathlib public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.ConjSqrtMinusD public import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
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
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Host_sqrtMinusD___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_List_prod___at___00Nat_equivProdNatFactoredNumbers_spec__1(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_rtE(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_rtE___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_L2_Pj_w0E_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_w0E(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_mE(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_mE___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_pIdeal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_pIdeal_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4___closed__0 = (const lean_object*)&lp_tree_LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iSup___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iSup___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_DistribSMul_toAddMonoidHom___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_DistribSMul_toAddMonoidHom___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_map___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_map___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_L2_Pj_MbOf_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_L2_Pj_MbOf_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_MbOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_MbOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelDeep___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelDeep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latW_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latW_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latW(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latW___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_rtE(lean_object* v_D_1_){
_start:
{
lean_object* v_host_2_; lean_object* v___x_3_; 
v_host_2_ = lean_ctor_get(v_D_1_, 1);
v___x_3_ = lp_tree_Formalism_BasicNotions_Host_sqrtMinusD___redArg(v_host_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_rtE___boxed(lean_object* v_D_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_L2_Pj_rtE(v_D_4_);
lean_dec_ref(v_D_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_L2_Pj_w0E_spec__0(lean_object* v___x_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_instField_8_; lean_object* v___x_9_; lean_object* v_toRing_10_; lean_object* v___x_11_; lean_object* v_toAddMonoidWithOne_12_; lean_object* v_toNatCast_13_; lean_object* v___x_14_; 
v_instField_8_ = lean_ctor_get(v___x_6_, 3);
lean_inc_ref(v_instField_8_);
lean_dec_ref(v___x_6_);
v___x_9_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_8_);
v_toRing_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toRing_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_10_);
v_toAddMonoidWithOne_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc_ref(v_toAddMonoidWithOne_12_);
lean_dec_ref(v___x_11_);
v_toNatCast_13_ = lean_ctor_get(v_toAddMonoidWithOne_12_, 0);
lean_inc(v_toNatCast_13_);
lean_dec_ref(v_toAddMonoidWithOne_12_);
v___x_14_ = lean_apply_1(v_toNatCast_13_, v_a_7_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_w0E(lean_object* v_D_15_){
_start:
{
lean_object* v_host_16_; lean_object* v_toHostAx_17_; lean_object* v_instField_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_toDiv_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_toSemiring_24_; lean_object* v___x_25_; lean_object* v_toAdd_26_; lean_object* v_toRing_27_; lean_object* v___x_28_; lean_object* v_toAddMonoidWithOne_29_; lean_object* v_toOne_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_host_16_ = lean_ctor_get(v_D_15_, 1);
lean_inc_ref(v_host_16_);
lean_dec_ref(v_D_15_);
v_toHostAx_17_ = lean_ctor_get(v_host_16_, 0);
lean_inc_ref(v_toHostAx_17_);
v_instField_18_ = lean_ctor_get(v_toHostAx_17_, 3);
lean_inc_ref(v_instField_18_);
v___x_19_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_18_);
v___x_20_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_19_);
v_toDiv_21_ = lean_ctor_get(v___x_20_, 2);
lean_inc(v_toDiv_21_);
lean_dec_ref(v___x_20_);
v___x_22_ = lp_mathlib_Field_toSemifield___redArg(v_instField_18_);
v___x_23_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_22_);
v_toSemiring_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_toSemiring_24_);
lean_dec_ref(v___x_23_);
v___x_25_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_24_);
v_toAdd_26_ = lean_ctor_get(v___x_25_, 1);
lean_inc(v_toAdd_26_);
lean_dec_ref(v___x_25_);
v_toRing_27_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_toRing_27_);
lean_dec_ref(v___x_19_);
v___x_28_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_27_);
v_toAddMonoidWithOne_29_ = lean_ctor_get(v___x_28_, 1);
lean_inc_ref(v_toAddMonoidWithOne_29_);
lean_dec_ref(v___x_28_);
v_toOne_30_ = lean_ctor_get(v_toAddMonoidWithOne_29_, 2);
lean_inc(v_toOne_30_);
lean_dec_ref(v_toAddMonoidWithOne_29_);
v___x_31_ = lp_tree_Formalism_BasicNotions_Host_sqrtMinusD___redArg(v_host_16_);
lean_dec_ref(v_host_16_);
v___x_32_ = lean_apply_2(v_toAdd_26_, v_toOne_30_, v___x_31_);
v___x_33_ = lean_unsigned_to_nat(2u);
v___x_34_ = lp_tree_Nat_cast___at___00Formalism_L2_Pj_w0E_spec__0(v_toHostAx_17_, v___x_33_);
v___x_35_ = lean_apply_2(v_toDiv_21_, v___x_32_, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_mE(lean_object* v_D_36_){
_start:
{
lean_object* v_host_37_; lean_object* v_toHostAx_38_; lean_object* v_d_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_host_37_ = lean_ctor_get(v_D_36_, 1);
v_toHostAx_38_ = lean_ctor_get(v_host_37_, 0);
v_d_39_ = lean_ctor_get(v_toHostAx_38_, 1);
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_add(v_d_39_, v___x_40_);
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lean_nat_shiftr(v___x_41_, v___x_42_);
lean_dec(v___x_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_mE___boxed(lean_object* v_D_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_L2_Pj_mE(v_D_44_);
lean_dec_ref(v_D_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_pIdeal_spec__0(lean_object* v___x_46_, lean_object* v_s_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_pIdeal_spec__0___boxed(lean_object* v___x_49_, lean_object* v_s_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_Submodule_span___at___00Formalism_L2_Pj_pIdeal_spec__0(v___x_49_, v_s_50_);
lean_dec_ref(v___x_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal___redArg(lean_object* v_D_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_box(0);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal___redArg___boxed(lean_object* v_D_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_L2_Pj_pIdeal___redArg(v_D_54_);
lean_dec_ref(v_D_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal(lean_object* v_D_56_, lean_object* v_p_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_pIdeal___boxed(lean_object* v_D_59_, lean_object* v_p_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_Pj_pIdeal(v_D_59_, v_p_60_);
lean_dec(v_p_60_);
lean_dec_ref(v_D_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__8(lean_object* v___x_62_, lean_object* v_p_63_, lean_object* v_s_64_, lean_object* v_hs_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__8___boxed(lean_object* v___x_67_, lean_object* v_p_68_, lean_object* v_s_69_, lean_object* v_hs_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Submodule_copy___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__8(v___x_67_, v_p_68_, v_s_69_, v_hs_70_);
lean_dec_ref(v___x_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__7(lean_object* v___x_72_, lean_object* v_00_u03c3_u2081_u2082_73_, lean_object* v_inst_74_, lean_object* v_f_75_, lean_object* v_p_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__7___boxed(lean_object* v___x_78_, lean_object* v_00_u03c3_u2081_u2082_79_, lean_object* v_inst_80_, lean_object* v_f_81_, lean_object* v_p_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_tree_Submodule_map___at___00LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5_spec__7(v___x_78_, v_00_u03c3_u2081_u2082_79_, v_inst_80_, v_f_81_, v_p_82_);
lean_dec(v_f_81_);
lean_dec(v_00_u03c3_u2081_u2082_79_);
lean_dec_ref(v___x_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___redArg(lean_object* v___x_84_, lean_object* v_00_u03c4_u2081_u2082_85_, lean_object* v_f_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___redArg___boxed(lean_object* v___x_88_, lean_object* v_00_u03c4_u2081_u2082_89_, lean_object* v_f_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___redArg(v___x_88_, v_00_u03c4_u2081_u2082_89_, v_f_90_);
lean_dec(v_f_90_);
lean_dec(v_00_u03c4_u2081_u2082_89_);
lean_dec_ref(v___x_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg___lam__0(lean_object* v_instField_92_, lean_object* v_f_93_, lean_object* v_x_94_, lean_object* v_b_95_){
_start:
{
lean_object* v_toCommRing_96_; lean_object* v_toSemiring_97_; lean_object* v_toMonoid_98_; lean_object* v_toSemigroup_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_toCommRing_96_ = lean_ctor_get(v_instField_92_, 0);
lean_inc_ref(v_toCommRing_96_);
lean_dec_ref(v_instField_92_);
v_toSemiring_97_ = lean_ctor_get(v_toCommRing_96_, 0);
lean_inc_ref(v_toSemiring_97_);
lean_dec_ref(v_toCommRing_96_);
v_toMonoid_98_ = lean_ctor_get(v_toSemiring_97_, 1);
lean_inc_ref(v_toMonoid_98_);
lean_dec_ref(v_toSemiring_97_);
v_toSemigroup_99_ = lean_ctor_get(v_toMonoid_98_, 0);
lean_inc(v_toSemigroup_99_);
lean_dec_ref(v_toMonoid_98_);
v___x_100_ = lean_apply_1(v_f_93_, v_b_95_);
v___x_101_ = lean_apply_2(v_toSemigroup_99_, v___x_100_, v_x_94_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg(lean_object* v___x_102_, lean_object* v_f_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_instField_105_; lean_object* v___f_106_; 
v_instField_105_ = lean_ctor_get(v___x_102_, 3);
lean_inc_ref(v_instField_105_);
lean_dec_ref(v___x_102_);
v___f_106_ = lean_alloc_closure((void*)(lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg___lam__0), 4, 3);
lean_closure_set(v___f_106_, 0, v_instField_105_);
lean_closure_set(v___f_106_, 1, v_f_103_);
lean_closure_set(v___f_106_, 2, v_x_104_);
return v___f_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4(lean_object* v___x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; 
v___f_110_ = ((lean_object*)(lp_tree_LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4___closed__0));
v___x_111_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg(v___x_108_, v___f_110_, v_x_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_iSup___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__3(lean_object* v___x_112_, lean_object* v_00_u03b9_113_, lean_object* v_s_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_iSup___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__3___boxed(lean_object* v___x_116_, lean_object* v_00_u03b9_117_, lean_object* v_s_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_tree_iSup___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__3(v___x_116_, v_00_u03b9_117_, v_s_118_);
lean_dec_ref(v_s_118_);
lean_dec_ref(v___x_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_DistribSMul_toAddMonoidHom___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__1___lam__0(lean_object* v_instField_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_toCommRing_123_; lean_object* v_toSemiring_124_; lean_object* v_toMonoid_125_; lean_object* v_toSemigroup_126_; lean_object* v___x_127_; 
v_toCommRing_123_ = lean_ctor_get(v_instField_120_, 0);
lean_inc_ref(v_toCommRing_123_);
lean_dec_ref(v_instField_120_);
v_toSemiring_124_ = lean_ctor_get(v_toCommRing_123_, 0);
lean_inc_ref(v_toSemiring_124_);
lean_dec_ref(v_toCommRing_123_);
v_toMonoid_125_ = lean_ctor_get(v_toSemiring_124_, 1);
lean_inc_ref(v_toMonoid_125_);
lean_dec_ref(v_toSemiring_124_);
v_toSemigroup_126_ = lean_ctor_get(v_toMonoid_125_, 0);
lean_inc(v_toSemigroup_126_);
lean_dec_ref(v_toMonoid_125_);
v___x_127_ = lean_apply_2(v_toSemigroup_126_, v_x_121_, v_x_122_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_DistribSMul_toAddMonoidHom___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__1(lean_object* v___x_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_instField_130_; lean_object* v___f_131_; 
v_instField_130_ = lean_ctor_get(v___x_128_, 3);
lean_inc_ref(v_instField_130_);
lean_dec_ref(v___x_128_);
v___f_131_ = lean_alloc_closure((void*)(lp_tree_DistribSMul_toAddMonoidHom___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_131_, 0, v_instField_130_);
lean_closure_set(v___f_131_, 1, v_x_129_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_map___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__2(lean_object* v___x_132_, lean_object* v_mc_133_, lean_object* v_f_134_, lean_object* v_S_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_box(0);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddSubmonoid_map___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__2___boxed(lean_object* v___x_137_, lean_object* v_mc_138_, lean_object* v_f_139_, lean_object* v_S_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_tree_AddSubmonoid_map___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__2(v___x_137_, v_mc_138_, v_f_139_, v_S_140_);
lean_dec(v_f_139_);
lean_dec_ref(v___x_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___lam__0(lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_s_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___lam__0___boxed(lean_object* v___x_146_, lean_object* v___x_147_, lean_object* v_s_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___lam__0(v___x_146_, v___x_147_, v_s_148_);
lean_dec(v_s_148_);
lean_dec_ref(v___x_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6(lean_object* v___x_150_, lean_object* v_init_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
return v_init_151_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6___boxed(lean_object* v___x_154_, lean_object* v_init_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6(v___x_154_, v_init_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec_ref(v___x_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_L2_Pj_MbOf_spec__1(lean_object* v___x_158_, lean_object* v_l_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(0);
v___x_161_ = lp_tree_List_foldr___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__6(v___x_158_, v___x_160_, v_l_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_prod___at___00Formalism_L2_Pj_MbOf_spec__1___boxed(lean_object* v___x_162_, lean_object* v_l_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = lp_tree_List_prod___at___00Formalism_L2_Pj_MbOf_spec__1(v___x_162_, v_l_163_);
lean_dec(v_l_163_);
lean_dec_ref(v___x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0___redArg(lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
if (lean_obj_tag(v_a_165_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = l_List_reverse___redArg(v_a_166_);
return v___x_167_;
}
else
{
lean_object* v_tail_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_177_; 
v_tail_168_ = lean_ctor_get(v_a_165_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_a_165_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v_a_165_, 0);
lean_dec(v_unused_178_);
v___x_170_ = v_a_165_;
v_isShared_171_ = v_isSharedCheck_177_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_tail_168_);
lean_dec(v_a_165_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_177_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_box(0);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v_a_166_);
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_a_166_);
v___x_174_ = v_reuseFailAlloc_176_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
v_a_165_ = v_tail_168_;
v_a_166_ = v___x_174_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_MbOf(lean_object* v_D_179_, lean_object* v_ps_180_){
_start:
{
lean_object* v_host_181_; lean_object* v_toHostAx_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_host_181_ = lean_ctor_get(v_D_179_, 1);
v_toHostAx_182_ = lean_ctor_get(v_host_181_, 0);
v___x_183_ = lean_box(0);
v___x_184_ = lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0___redArg(v_ps_180_, v___x_183_);
v___x_185_ = lp_tree_List_prod___at___00Formalism_L2_Pj_MbOf_spec__1(v_toHostAx_182_, v___x_184_);
lean_dec(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_MbOf___boxed(lean_object* v_D_186_, lean_object* v_ps_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_tree_Formalism_L2_Pj_MbOf(v_D_186_, v_ps_187_);
lean_dec_ref(v_D_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0(lean_object* v_D_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0___redArg(v_a_190_, v_a_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0___boxed(lean_object* v_D_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = lp_tree_List_mapTR_loop___at___00Formalism_L2_Pj_MbOf_spec__0(v_D_193_, v_a_194_, v_a_195_);
lean_dec_ref(v_D_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5(lean_object* v___x_197_, lean_object* v_inst_198_, lean_object* v_f_199_, lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lp_tree_LinearMap_smulRight___at___00LinearMap_toSpanSingleton___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__4_spec__5___redArg(v___x_197_, v_f_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5(lean_object* v___x_202_, lean_object* v_00_u03c4_u2081_u2082_203_, lean_object* v_inst_204_, lean_object* v_f_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5___boxed(lean_object* v___x_207_, lean_object* v_00_u03c4_u2081_u2082_208_, lean_object* v_inst_209_, lean_object* v_f_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_LinearMap_range___at___00List_prod___at___00Formalism_L2_Pj_MbOf_spec__1_spec__5(v___x_207_, v_00_u03c4_u2081_u2082_208_, v_inst_209_, v_f_210_);
lean_dec(v_f_210_);
lean_dec(v_00_u03c4_u2081_u2082_208_);
lean_dec_ref(v___x_207_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___redArg(lean_object* v_D_212_, lean_object* v_ps_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = lp_mathlib_List_prod___at___00Nat_equivProdNatFactoredNumbers_spec__1(v_ps_213_);
v___x_215_ = lp_tree_Formalism_L2_Pj_MbOf(v_D_212_, v_ps_213_);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___redArg___boxed(lean_object* v_D_218_, lean_object* v_ps_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = lp_tree_Formalism_L2_Pj_levelOfPs___redArg(v_D_218_, v_ps_219_);
lean_dec_ref(v_D_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs(lean_object* v_D_221_, lean_object* v_hU_222_, lean_object* v_ps_223_, lean_object* v_hp_224_, lean_object* v_hne_225_, lean_object* v_hP_226_, lean_object* v_hC_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lp_tree_Formalism_L2_Pj_levelOfPs___redArg(v_D_221_, v_ps_223_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___boxed(lean_object* v_D_229_, lean_object* v_hU_230_, lean_object* v_ps_231_, lean_object* v_hp_232_, lean_object* v_hne_233_, lean_object* v_hP_234_, lean_object* v_hC_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = lp_tree_Formalism_L2_Pj_levelOfPs(v_D_229_, v_hU_230_, v_ps_231_, v_hp_232_, v_hne_233_, v_hP_234_, v_hC_235_);
lean_dec_ref(v_D_229_);
return v_res_236_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(2u);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_nat_mod(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_unsigned_to_nat(2u);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_mod(v___x_241_, v___x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOf___redArg(lean_object* v_D_243_){
_start:
{
lean_object* v_host_244_; lean_object* v_g_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_host_244_ = lean_ctor_get(v_D_243_, 1);
v_g_245_ = lean_ctor_get(v_host_244_, 6);
v___x_246_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0, &lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0);
lean_inc_ref_n(v_g_245_, 2);
v___x_247_ = lean_apply_1(v_g_245_, v___x_246_);
v___x_248_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1, &lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1_once, _init_lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1);
v___x_249_ = lean_apply_1(v_g_245_, v___x_248_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_247_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lp_tree_Formalism_L2_Pj_levelOfPs___redArg(v_D_243_, v___x_252_);
lean_dec_ref(v_D_243_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelOf(lean_object* v_D_254_, lean_object* v_hU_255_, lean_object* v_hS_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lp_tree_Formalism_L2_Pj_levelOf___redArg(v_D_254_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelDeep___redArg(lean_object* v_D_258_){
_start:
{
lean_object* v_host_259_; lean_object* v_g_260_; lean_object* v_pde_261_; lean_object* v_pde_x27_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_host_259_ = lean_ctor_get(v_D_258_, 1);
v_g_260_ = lean_ctor_get(v_host_259_, 6);
v_pde_261_ = lean_ctor_get(v_host_259_, 7);
v_pde_x27_262_ = lean_ctor_get(v_host_259_, 8);
v___x_263_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0, &lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__0);
lean_inc_ref_n(v_g_260_, 2);
v___x_264_ = lean_apply_1(v_g_260_, v___x_263_);
v___x_265_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1, &lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1_once, _init_lp_tree_Formalism_L2_Pj_levelOf___redArg___closed__1);
v___x_266_ = lean_apply_1(v_g_260_, v___x_265_);
v___x_267_ = lean_box(0);
lean_inc(v_pde_x27_262_);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v_pde_x27_262_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_inc(v_pde_261_);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v_pde_261_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_266_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_264_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lp_tree_Formalism_L2_Pj_levelOfPs___redArg(v_D_258_, v___x_271_);
lean_dec_ref(v_D_258_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelDeep(lean_object* v_D_273_, lean_object* v_hU_274_, lean_object* v_hS_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lp_tree_Formalism_L2_Pj_levelDeep___redArg(v_D_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latW_spec__0(lean_object* v___x_277_, lean_object* v___x_278_, lean_object* v_s_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_L2_Pj_latW_spec__0___boxed(lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v_s_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_tree_Submodule_span___at___00Formalism_L2_Pj_latW_spec__0(v___x_281_, v___x_282_, v_s_283_);
lean_dec_ref(v___x_282_);
lean_dec_ref(v___x_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latW(lean_object* v_D_285_, lean_object* v_j_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_latW___boxed(lean_object* v_D_288_, lean_object* v_j_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = lp_tree_Formalism_L2_Pj_latW(v_D_288_, v_j_289_);
lean_dec(v_j_289_);
lean_dec_ref(v_D_288_);
return v_res_290_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_ConjSqrtMinusD(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_HalfOneAddSqrtNegIsIntegral(uint8_t builtin) {
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
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_ConjSqrtMinusD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
