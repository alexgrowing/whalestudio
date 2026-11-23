// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.BoundaryLocalData
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Host_sqrtMinusD___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_MainNotions_BoundaryLocalData_w0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_w0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_MainNotions_BoundaryLocalData_w0_spec__0(lean_object* v___x_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_instField_3_; lean_object* v___x_4_; lean_object* v_toRing_5_; lean_object* v___x_6_; lean_object* v_toAddMonoidWithOne_7_; lean_object* v_toNatCast_8_; lean_object* v___x_9_; 
v_instField_3_ = lean_ctor_get(v___x_1_, 3);
lean_inc_ref(v_instField_3_);
lean_dec_ref(v___x_1_);
v___x_4_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_3_);
v_toRing_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toRing_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_5_);
v_toAddMonoidWithOne_7_ = lean_ctor_get(v___x_6_, 1);
lean_inc_ref(v_toAddMonoidWithOne_7_);
lean_dec_ref(v___x_6_);
v_toNatCast_8_ = lean_ctor_get(v_toAddMonoidWithOne_7_, 0);
lean_inc(v_toNatCast_8_);
lean_dec_ref(v_toAddMonoidWithOne_7_);
v___x_9_ = lean_apply_1(v_toNatCast_8_, v_a_2_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_w0(lean_object* v_D_10_){
_start:
{
lean_object* v_host_11_; lean_object* v_toHostAx_12_; lean_object* v_instField_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_toDiv_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toSemiring_19_; lean_object* v___x_20_; lean_object* v_toAdd_21_; lean_object* v_toRing_22_; lean_object* v___x_23_; lean_object* v_toAddMonoidWithOne_24_; lean_object* v_toOne_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_host_11_ = lean_ctor_get(v_D_10_, 1);
lean_inc_ref(v_host_11_);
lean_dec_ref(v_D_10_);
v_toHostAx_12_ = lean_ctor_get(v_host_11_, 0);
lean_inc_ref(v_toHostAx_12_);
v_instField_13_ = lean_ctor_get(v_toHostAx_12_, 3);
lean_inc_ref(v_instField_13_);
v___x_14_ = lp_mathlib_Field_toDivisionRing___redArg(v_instField_13_);
v___x_15_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_14_);
v_toDiv_16_ = lean_ctor_get(v___x_15_, 2);
lean_inc(v_toDiv_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lp_mathlib_Field_toSemifield___redArg(v_instField_13_);
v___x_18_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_17_);
v_toSemiring_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_toSemiring_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_19_);
v_toAdd_21_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_toAdd_21_);
lean_dec_ref(v___x_20_);
v_toRing_22_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toRing_22_);
lean_dec_ref(v___x_14_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_22_);
v_toAddMonoidWithOne_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_toAddMonoidWithOne_24_);
lean_dec_ref(v___x_23_);
v_toOne_25_ = lean_ctor_get(v_toAddMonoidWithOne_24_, 2);
lean_inc(v_toOne_25_);
lean_dec_ref(v_toAddMonoidWithOne_24_);
v___x_26_ = lp_tree_Formalism_BasicNotions_Host_sqrtMinusD___redArg(v_host_11_);
lean_dec_ref(v_host_11_);
v___x_27_ = lean_apply_2(v_toAdd_21_, v_toOne_25_, v___x_26_);
v___x_28_ = lean_unsigned_to_nat(2u);
v___x_29_ = lp_tree_Nat_cast___at___00Formalism_MainNotions_BoundaryLocalData_w0_spec__0(v_toHostAx_12_, v___x_28_);
v___x_30_ = lean_apply_2(v_toDiv_16_, v___x_27_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA___redArg(lean_object* v_D_31_, lean_object* v_L_32_, lean_object* v_B_33_, lean_object* v_Z_34_, lean_object* v_y_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_xAdd_37_; lean_object* v_xMod_38_; lean_object* v_multiplicationLatticeFirst_39_; lean_object* v_multiplicationLatticeSecond_40_; lean_object* v___x_41_; lean_object* v_toAddMonoid_42_; lean_object* v_toAddSemigroup_43_; lean_object* v_ylMod_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_xAdd_37_ = lean_ctor_get(v_B_33_, 0);
lean_inc_ref(v_xAdd_37_);
v_xMod_38_ = lean_ctor_get(v_B_33_, 1);
lean_inc(v_xMod_38_);
v_multiplicationLatticeFirst_39_ = lean_ctor_get(v_B_33_, 4);
lean_inc(v_multiplicationLatticeFirst_39_);
v_multiplicationLatticeSecond_40_ = lean_ctor_get(v_B_33_, 5);
lean_inc(v_multiplicationLatticeSecond_40_);
lean_dec_ref(v_B_33_);
lean_inc_n(v_y_35_, 4);
lean_inc_n(v_Z_34_, 4);
v___x_41_ = lean_apply_2(v_xAdd_37_, v_Z_34_, v_y_35_);
v_toAddMonoid_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_toAddMonoid_42_);
lean_dec_ref(v___x_41_);
v_toAddSemigroup_43_ = lean_ctor_get(v_toAddMonoid_42_, 0);
lean_inc(v_toAddSemigroup_43_);
lean_dec_ref(v_toAddMonoid_42_);
v_ylMod_44_ = lean_ctor_get(v_L_32_, 5);
lean_inc(v_ylMod_44_);
lean_dec_ref(v_L_32_);
v___x_45_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_w0(v_D_31_);
lean_inc_n(v_a_36_, 2);
lean_inc(v___x_45_);
v___x_46_ = lean_apply_4(v_ylMod_44_, v_Z_34_, v_y_35_, v___x_45_, v_a_36_);
lean_inc(v___x_46_);
v___x_47_ = lean_apply_4(v_multiplicationLatticeFirst_39_, v_Z_34_, v_y_35_, v_a_36_, v___x_46_);
v___x_48_ = lean_apply_4(v_multiplicationLatticeSecond_40_, v_Z_34_, v_y_35_, v_a_36_, v___x_46_);
v___x_49_ = lean_apply_4(v_xMod_38_, v_Z_34_, v_y_35_, v___x_45_, v___x_48_);
v___x_50_ = lean_apply_2(v_toAddSemigroup_43_, v___x_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA(lean_object* v_D_51_, lean_object* v_r_52_, lean_object* v_j_53_, lean_object* v_p_54_, lean_object* v_L_55_, lean_object* v_B_56_, lean_object* v_Z_57_, lean_object* v_y_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA___redArg(v_D_51_, v_L_55_, v_B_56_, v_Z_57_, v_y_58_, v_a_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA___boxed(lean_object* v_D_61_, lean_object* v_r_62_, lean_object* v_j_63_, lean_object* v_p_64_, lean_object* v_L_65_, lean_object* v_B_66_, lean_object* v_Z_67_, lean_object* v_y_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_shiftA(v_D_61_, v_r_62_, v_j_63_, v_p_64_, v_L_65_, v_B_66_, v_Z_67_, v_y_68_, v_a_69_);
lean_dec(v_p_64_);
lean_dec(v_j_63_);
lean_dec(v_r_62_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA___redArg(lean_object* v_D_71_, lean_object* v_L_72_, lean_object* v_B_73_, lean_object* v_Z_74_, lean_object* v_y_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_mulC_77_; lean_object* v_ylMod_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_mulC_77_ = lean_ctor_get(v_B_73_, 6);
lean_inc_ref(v_mulC_77_);
lean_dec_ref(v_B_73_);
v_ylMod_78_ = lean_ctor_get(v_L_72_, 5);
lean_inc(v_ylMod_78_);
lean_dec_ref(v_L_72_);
v___x_79_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_w0(v_D_71_);
lean_inc(v_a_76_);
lean_inc(v_y_75_);
lean_inc(v_Z_74_);
v___x_80_ = lean_apply_4(v_ylMod_78_, v_Z_74_, v_y_75_, v___x_79_, v_a_76_);
v___x_81_ = lean_apply_4(v_mulC_77_, v_Z_74_, v_y_75_, v_a_76_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA(lean_object* v_D_82_, lean_object* v_r_83_, lean_object* v_j_84_, lean_object* v_p_85_, lean_object* v_L_86_, lean_object* v_B_87_, lean_object* v_Z_88_, lean_object* v_y_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA___redArg(v_D_82_, v_L_86_, v_B_87_, v_Z_88_, v_y_89_, v_a_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA___boxed(lean_object* v_D_92_, lean_object* v_r_93_, lean_object* v_j_94_, lean_object* v_p_95_, lean_object* v_L_96_, lean_object* v_B_97_, lean_object* v_Z_98_, lean_object* v_y_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA(v_D_92_, v_r_93_, v_j_94_, v_p_95_, v_L_96_, v_B_97_, v_Z_98_, v_y_99_, v_a_100_);
lean_dec(v_p_95_);
lean_dec(v_j_94_);
lean_dec(v_r_93_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib___redArg(lean_object* v_D_102_, lean_object* v_B_103_, lean_object* v_z_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_iYm_106_; lean_object* v_phib_107_; lean_object* v_taub_108_; lean_object* v___x_109_; lean_object* v_toFun_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_iYm_106_ = lean_ctor_get(v_B_103_, 13);
lean_inc(v_iYm_106_);
v_phib_107_ = lean_ctor_get(v_B_103_, 16);
lean_inc_ref(v_phib_107_);
v_taub_108_ = lean_ctor_get(v_B_103_, 17);
lean_inc_ref(v_taub_108_);
lean_dec_ref(v_B_103_);
lean_inc_n(v_z_104_, 2);
v___x_109_ = lean_apply_1(v_phib_107_, v_z_104_);
v_toFun_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_toFun_110_);
lean_dec_ref(v___x_109_);
v___x_111_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_w0(v_D_102_);
lean_inc(v_a_105_);
v___x_112_ = lean_apply_3(v_iYm_106_, v_z_104_, v___x_111_, v_a_105_);
v___x_113_ = lean_apply_1(v_toFun_110_, v___x_112_);
v___x_114_ = lean_apply_3(v_taub_108_, v_z_104_, v_a_105_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib(lean_object* v_D_115_, lean_object* v_r_116_, lean_object* v_j_117_, lean_object* v_p_118_, lean_object* v_L_119_, lean_object* v_B_120_, lean_object* v_z_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib___redArg(v_D_115_, v_B_120_, v_z_121_, v_a_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib___boxed(lean_object* v_D_124_, lean_object* v_r_125_, lean_object* v_j_126_, lean_object* v_p_127_, lean_object* v_L_128_, lean_object* v_B_129_, lean_object* v_z_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psib(v_D_124_, v_r_125_, v_j_126_, v_p_127_, v_L_128_, v_B_129_, v_z_130_, v_a_131_);
lean_dec_ref(v_L_128_);
lean_dec(v_p_127_);
lean_dec(v_j_126_);
lean_dec(v_r_125_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN___redArg(lean_object* v_L_133_, lean_object* v_B_134_, lean_object* v_y_135_, lean_object* v_a_136_, lean_object* v_i_137_){
_start:
{
lean_object* v_Xm_138_; lean_object* v_phi_139_; lean_object* v___x_140_; lean_object* v_toFun_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_Xm_138_ = lean_ctor_get(v_L_133_, 0);
lean_inc(v_Xm_138_);
lean_dec_ref(v_L_133_);
v_phi_139_ = lean_ctor_get(v_B_134_, 2);
lean_inc_ref(v_phi_139_);
lean_dec_ref(v_B_134_);
v___x_140_ = lean_apply_2(v_phi_139_, v_Xm_138_, v_y_135_);
v_toFun_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_toFun_141_);
lean_dec_ref(v___x_140_);
v___x_142_ = lean_apply_1(v_a_136_, v_i_137_);
v___x_143_ = lean_apply_1(v_toFun_141_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN(lean_object* v_D_144_, lean_object* v_r_145_, lean_object* v_j_146_, lean_object* v_p_147_, lean_object* v_L_148_, lean_object* v_B_149_, lean_object* v_y_150_, lean_object* v_nW_151_, lean_object* v_a_152_, lean_object* v_i_153_){
_start:
{
lean_object* v_Xm_154_; lean_object* v_phi_155_; lean_object* v___x_156_; lean_object* v_toFun_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_Xm_154_ = lean_ctor_get(v_L_148_, 0);
lean_inc(v_Xm_154_);
lean_dec_ref(v_L_148_);
v_phi_155_ = lean_ctor_get(v_B_149_, 2);
lean_inc_ref(v_phi_155_);
lean_dec_ref(v_B_149_);
v___x_156_ = lean_apply_2(v_phi_155_, v_Xm_154_, v_y_150_);
v_toFun_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_toFun_157_);
lean_dec_ref(v___x_156_);
v___x_158_ = lean_apply_1(v_a_152_, v_i_153_);
v___x_159_ = lean_apply_1(v_toFun_157_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN___boxed(lean_object* v_D_160_, lean_object* v_r_161_, lean_object* v_j_162_, lean_object* v_p_163_, lean_object* v_L_164_, lean_object* v_B_165_, lean_object* v_y_166_, lean_object* v_nW_167_, lean_object* v_a_168_, lean_object* v_i_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_phiN(v_D_160_, v_r_161_, v_j_162_, v_p_163_, v_L_164_, v_B_165_, v_y_166_, v_nW_167_, v_a_168_, v_i_169_);
lean_dec(v_nW_167_);
lean_dec(v_p_163_);
lean_dec(v_j_162_);
lean_dec(v_r_161_);
lean_dec_ref(v_D_160_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___redArg___lam__0(lean_object* v_a_171_, lean_object* v_D_172_, lean_object* v_L_173_, lean_object* v_B_174_, lean_object* v_Xm_175_, lean_object* v_y_176_, lean_object* v_i_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_apply_1(v_a_171_, v_i_177_);
v___x_179_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiA___redArg(v_D_172_, v_L_173_, v_B_174_, v_Xm_175_, v_y_176_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___lam__0(lean_object* v___x_180_, lean_object* v_x1_181_, lean_object* v_x2_182_){
_start:
{
lean_object* v___x_183_; lean_object* v_toMul_184_; lean_object* v_val_185_; lean_object* v_inv_186_; lean_object* v_val_187_; lean_object* v_inv_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_197_; 
v___x_183_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_180_);
v_toMul_184_ = lean_ctor_get(v___x_183_, 1);
lean_inc(v_toMul_184_);
lean_dec_ref(v___x_183_);
v_val_185_ = lean_ctor_get(v_x1_181_, 0);
lean_inc(v_val_185_);
v_inv_186_ = lean_ctor_get(v_x1_181_, 1);
lean_inc(v_inv_186_);
lean_dec_ref(v_x1_181_);
v_val_187_ = lean_ctor_get(v_x2_182_, 0);
v_inv_188_ = lean_ctor_get(v_x2_182_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x2_182_);
if (v_isSharedCheck_197_ == 0)
{
v___x_190_ = v_x2_182_;
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_inv_188_);
lean_inc(v_val_187_);
lean_dec(v_x2_182_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
lean_inc(v_toMul_184_);
v___x_192_ = lean_apply_2(v_toMul_184_, v_val_185_, v_val_187_);
v___x_193_ = lean_apply_2(v_toMul_184_, v_inv_188_, v_inv_186_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v___x_193_);
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_195_ = v___x_190_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___lam__0___boxed(lean_object* v___x_198_, lean_object* v_x1_199_, lean_object* v_x2_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___lam__0(v___x_198_, v_x1_199_, v_x2_200_);
lean_dec_ref(v___x_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0(lean_object* v___x_202_, lean_object* v_s_203_){
_start:
{
lean_object* v_toField_204_; lean_object* v_toCommRing_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_toOne_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_217_; 
v_toField_204_ = lean_ctor_get(v___x_202_, 1);
v_toCommRing_205_ = lean_ctor_get(v_toField_204_, 0);
v___x_206_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_205_);
v___x_207_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_206_);
v_toOne_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v___x_207_, 1);
lean_dec(v_unused_218_);
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_toOne_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___f_212_; lean_object* v___x_214_; 
v___f_212_ = lean_alloc_closure((void*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_212_, 0, v___x_206_);
lean_inc(v_toOne_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_toOne_208_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_toOne_208_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_toOne_208_);
v___x_214_ = v_reuseFailAlloc_216_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = l_List_foldrTR___redArg(v___f_212_, v___x_214_, v_s_203_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0___boxed(lean_object* v___x_219_, lean_object* v_s_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0(v___x_219_, v_s_220_);
lean_dec_ref(v___x_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg(lean_object* v___x_222_, lean_object* v_s_223_, lean_object* v_f_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lp_mathlib_Multiset_map___redArg(v_f_224_, v_s_223_);
v___x_226_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0_spec__0(v___x_222_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg___boxed(lean_object* v___x_227_, lean_object* v_s_228_, lean_object* v_f_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg(v___x_227_, v_s_228_, v_f_229_);
lean_dec_ref(v___x_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___redArg(lean_object* v_D_231_, lean_object* v_L_232_, lean_object* v_B_233_, lean_object* v_y_234_, lean_object* v_nW_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_Xm_237_; lean_object* v_fld_238_; lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_Xm_237_ = lean_ctor_get(v_L_232_, 0);
lean_inc_n(v_Xm_237_, 2);
v_fld_238_ = lean_ctor_get(v_L_232_, 3);
lean_inc_ref(v_fld_238_);
lean_inc(v_y_234_);
v___f_239_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___redArg___lam__0), 7, 6);
lean_closure_set(v___f_239_, 0, v_a_236_);
lean_closure_set(v___f_239_, 1, v_D_231_);
lean_closure_set(v___f_239_, 2, v_L_232_);
lean_closure_set(v___f_239_, 3, v_B_233_);
lean_closure_set(v___f_239_, 4, v_Xm_237_);
lean_closure_set(v___f_239_, 5, v_y_234_);
v___x_240_ = lean_apply_2(v_fld_238_, v_Xm_237_, v_y_234_);
v___x_241_ = l_List_finRange(v_nW_235_);
v___x_242_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg(v___x_240_, v___x_241_, v___f_239_);
lean_dec_ref(v___x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN(lean_object* v_D_243_, lean_object* v_r_244_, lean_object* v_j_245_, lean_object* v_p_246_, lean_object* v_L_247_, lean_object* v_B_248_, lean_object* v_y_249_, lean_object* v_nW_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___redArg(v_D_243_, v_L_247_, v_B_248_, v_y_249_, v_nW_250_, v_a_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN___boxed(lean_object* v_D_253_, lean_object* v_r_254_, lean_object* v_j_255_, lean_object* v_p_256_, lean_object* v_L_257_, lean_object* v_B_258_, lean_object* v_y_259_, lean_object* v_nW_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_psiN(v_D_253_, v_r_254_, v_j_255_, v_p_256_, v_L_257_, v_B_258_, v_y_259_, v_nW_260_, v_a_261_);
lean_dec(v_p_256_);
lean_dec(v_j_255_);
lean_dec(v_r_254_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0(lean_object* v___x_263_, lean_object* v_00_u03b9_264_, lean_object* v_s_265_, lean_object* v_f_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg(v___x_263_, v_s_265_, v_f_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___boxed(lean_object* v___x_268_, lean_object* v_00_u03b9_269_, lean_object* v_s_270_, lean_object* v_f_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0(v___x_268_, v_00_u03b9_269_, v_s_270_, v_f_271_);
lean_dec_ref(v___x_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___redArg___lam__0(lean_object* v_B_273_, lean_object* v_a_274_, lean_object* v_00_u03c7_275_, lean_object* v_Xm_276_, lean_object* v_y_277_, lean_object* v_i_278_){
_start:
{
lean_object* v_tau_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_tau_279_ = lean_ctor_get(v_B_273_, 3);
lean_inc_ref(v_tau_279_);
lean_dec_ref(v_B_273_);
lean_inc(v_i_278_);
v___x_280_ = lean_apply_1(v_a_274_, v_i_278_);
v___x_281_ = lean_apply_1(v_00_u03c7_275_, v_i_278_);
v___x_282_ = lean_apply_4(v_tau_279_, v_Xm_276_, v_y_277_, v___x_280_, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___redArg(lean_object* v_L_283_, lean_object* v_B_284_, lean_object* v_y_285_, lean_object* v_nW_286_, lean_object* v_a_287_, lean_object* v_00_u03c7_288_){
_start:
{
lean_object* v_Xm_289_; lean_object* v_fld_290_; lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_Xm_289_ = lean_ctor_get(v_L_283_, 0);
lean_inc_n(v_Xm_289_, 2);
v_fld_290_ = lean_ctor_get(v_L_283_, 3);
lean_inc_ref(v_fld_290_);
lean_dec_ref(v_L_283_);
lean_inc(v_y_285_);
v___f_291_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___redArg___lam__0), 6, 5);
lean_closure_set(v___f_291_, 0, v_B_284_);
lean_closure_set(v___f_291_, 1, v_a_287_);
lean_closure_set(v___f_291_, 2, v_00_u03c7_288_);
lean_closure_set(v___f_291_, 3, v_Xm_289_);
lean_closure_set(v___f_291_, 4, v_y_285_);
v___x_292_ = lean_apply_2(v_fld_290_, v_Xm_289_, v_y_285_);
v___x_293_ = l_List_finRange(v_nW_286_);
v___x_294_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_BoundaryLocalData_LocB_psiN_spec__0___redArg(v___x_292_, v___x_293_, v___f_291_);
lean_dec_ref(v___x_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN(lean_object* v_D_295_, lean_object* v_r_296_, lean_object* v_j_297_, lean_object* v_p_298_, lean_object* v_L_299_, lean_object* v_B_300_, lean_object* v_y_301_, lean_object* v_nW_302_, lean_object* v_a_303_, lean_object* v_00_u03c7_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___redArg(v_L_299_, v_B_300_, v_y_301_, v_nW_302_, v_a_303_, v_00_u03c7_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN___boxed(lean_object* v_D_306_, lean_object* v_r_307_, lean_object* v_j_308_, lean_object* v_p_309_, lean_object* v_L_310_, lean_object* v_B_311_, lean_object* v_y_312_, lean_object* v_nW_313_, lean_object* v_a_314_, lean_object* v_00_u03c7_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_tauN(v_D_306_, v_r_307_, v_j_308_, v_p_309_, v_L_310_, v_B_311_, v_y_312_, v_nW_313_, v_a_314_, v_00_u03c7_315_);
lean_dec(v_p_309_);
lean_dec(v_j_308_);
lean_dec(v_r_307_);
lean_dec_ref(v_D_306_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0___redArg(lean_object* v_h_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lp_mathlib_Equiv_symm___redArg(v_h_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0(lean_object* v_L_319_, lean_object* v___x_320_, lean_object* v_y_321_, lean_object* v_B_322_, lean_object* v_h_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lp_mathlib_Equiv_symm___redArg(v_h_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0___boxed(lean_object* v_L_325_, lean_object* v___x_326_, lean_object* v_y_327_, lean_object* v_B_328_, lean_object* v_h_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = lp_tree_AddEquiv_symm___at___00Formalism_MainNotions_BoundaryLocalData_LocB_beN_spec__0(v_L_325_, v___x_326_, v_y_327_, v_B_328_, v_h_329_);
lean_dec_ref(v_B_328_);
lean_dec(v_y_327_);
lean_dec(v___x_326_);
lean_dec_ref(v_L_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___redArg___lam__0(lean_object* v_L_331_, lean_object* v_B_332_, lean_object* v_y_333_, lean_object* v_00_u03c7_334_, lean_object* v_i_335_){
_start:
{
lean_object* v_Xm_336_; lean_object* v_be_337_; lean_object* v_phi_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_toFun_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_Xm_336_ = lean_ctor_get(v_L_331_, 0);
lean_inc_n(v_Xm_336_, 2);
v_be_337_ = lean_ctor_get(v_L_331_, 6);
lean_inc(v_be_337_);
lean_dec_ref(v_L_331_);
v_phi_338_ = lean_ctor_get(v_B_332_, 2);
lean_inc_ref(v_phi_338_);
lean_dec_ref(v_B_332_);
lean_inc(v_y_333_);
v___x_339_ = lean_apply_2(v_phi_338_, v_Xm_336_, v_y_333_);
v___x_340_ = lp_mathlib_Equiv_symm___redArg(v___x_339_);
v_toFun_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_toFun_341_);
lean_dec_ref(v___x_340_);
v___x_342_ = lean_apply_1(v_00_u03c7_334_, v_i_335_);
v___x_343_ = lean_apply_1(v_toFun_341_, v___x_342_);
lean_inc(v___x_343_);
v___x_344_ = lean_apply_4(v_be_337_, v_Xm_336_, v_y_333_, v___x_343_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___redArg(lean_object* v_L_345_, lean_object* v_B_346_, lean_object* v_y_347_, lean_object* v_nW_348_, lean_object* v_00_u03c7_349_){
_start:
{
lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___f_350_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___redArg___lam__0), 5, 4);
lean_closure_set(v___f_350_, 0, v_L_345_);
lean_closure_set(v___f_350_, 1, v_B_346_);
lean_closure_set(v___f_350_, 2, v_y_347_);
lean_closure_set(v___f_350_, 3, v_00_u03c7_349_);
v___x_351_ = l_List_finRange(v_nW_348_);
v___x_352_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_351_, v___f_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN(lean_object* v_D_353_, lean_object* v_r_354_, lean_object* v_j_355_, lean_object* v_p_356_, lean_object* v_L_357_, lean_object* v_B_358_, lean_object* v_y_359_, lean_object* v_nW_360_, lean_object* v_00_u03c7_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___redArg(v_L_357_, v_B_358_, v_y_359_, v_nW_360_, v_00_u03c7_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN___boxed(lean_object* v_D_363_, lean_object* v_r_364_, lean_object* v_j_365_, lean_object* v_p_366_, lean_object* v_L_367_, lean_object* v_B_368_, lean_object* v_y_369_, lean_object* v_nW_370_, lean_object* v_00_u03c7_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beN(v_D_363_, v_r_364_, v_j_365_, v_p_366_, v_L_367_, v_B_368_, v_y_369_, v_nW_370_, v_00_u03c7_371_);
lean_dec(v_p_366_);
lean_dec(v_j_365_);
lean_dec(v_r_364_);
lean_dec_ref(v_D_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___redArg___lam__0(lean_object* v_L_373_, lean_object* v_B_374_, lean_object* v_y_375_, lean_object* v_a_376_, lean_object* v_00_u03c7_377_, lean_object* v_i_378_){
_start:
{
lean_object* v_Xm_379_; lean_object* v_be_380_; lean_object* v_phi_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_toFun_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_Xm_379_ = lean_ctor_get(v_L_373_, 0);
lean_inc_n(v_Xm_379_, 2);
v_be_380_ = lean_ctor_get(v_L_373_, 6);
lean_inc(v_be_380_);
lean_dec_ref(v_L_373_);
v_phi_381_ = lean_ctor_get(v_B_374_, 2);
lean_inc_ref(v_phi_381_);
lean_dec_ref(v_B_374_);
lean_inc(v_y_375_);
v___x_382_ = lean_apply_2(v_phi_381_, v_Xm_379_, v_y_375_);
v___x_383_ = lp_mathlib_Equiv_symm___redArg(v___x_382_);
v_toFun_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_toFun_384_);
lean_dec_ref(v___x_383_);
lean_inc(v_i_378_);
v___x_385_ = lean_apply_1(v_a_376_, v_i_378_);
v___x_386_ = lean_apply_1(v_00_u03c7_377_, v_i_378_);
v___x_387_ = lean_apply_1(v_toFun_384_, v___x_386_);
v___x_388_ = lean_apply_4(v_be_380_, v_Xm_379_, v_y_375_, v___x_385_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___redArg(lean_object* v_L_389_, lean_object* v_B_390_, lean_object* v_y_391_, lean_object* v_nW_392_, lean_object* v_a_393_, lean_object* v_00_u03c7_394_){
_start:
{
lean_object* v___f_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___f_395_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___redArg___lam__0), 6, 5);
lean_closure_set(v___f_395_, 0, v_L_389_);
lean_closure_set(v___f_395_, 1, v_B_390_);
lean_closure_set(v___f_395_, 2, v_y_391_);
lean_closure_set(v___f_395_, 3, v_a_393_);
lean_closure_set(v___f_395_, 4, v_00_u03c7_394_);
v___x_396_ = l_List_finRange(v_nW_392_);
v___x_397_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_396_, v___f_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix(lean_object* v_D_398_, lean_object* v_r_399_, lean_object* v_j_400_, lean_object* v_p_401_, lean_object* v_L_402_, lean_object* v_B_403_, lean_object* v_y_404_, lean_object* v_nW_405_, lean_object* v_a_406_, lean_object* v_00_u03c7_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___redArg(v_L_402_, v_B_403_, v_y_404_, v_nW_405_, v_a_406_, v_00_u03c7_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix___boxed(lean_object* v_D_409_, lean_object* v_r_410_, lean_object* v_j_411_, lean_object* v_p_412_, lean_object* v_L_413_, lean_object* v_B_414_, lean_object* v_y_415_, lean_object* v_nW_416_, lean_object* v_a_417_, lean_object* v_00_u03c7_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_beMix(v_D_409_, v_r_410_, v_j_411_, v_p_412_, v_L_413_, v_B_414_, v_y_415_, v_nW_416_, v_a_417_, v_00_u03c7_418_);
lean_dec(v_p_412_);
lean_dec(v_j_411_);
lean_dec(v_r_410_);
lean_dec_ref(v_D_409_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc___redArg(lean_object* v_B_420_, lean_object* v_y_421_, lean_object* v_nW_422_, lean_object* v_n_423_, lean_object* v_s_424_, lean_object* v_00_u03c7_425_){
_start:
{
lean_object* v_nB_426_; lean_object* v_sgc_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_nB_426_ = lean_ctor_get(v_B_420_, 29);
lean_inc(v_nB_426_);
v_sgc_427_ = lean_ctor_get(v_B_420_, 30);
lean_inc(v_sgc_427_);
lean_dec_ref(v_B_420_);
lean_inc(v_00_u03c7_425_);
lean_inc(v_n_423_);
lean_inc(v_nW_422_);
lean_inc(v_y_421_);
v___x_428_ = lean_apply_5(v_sgc_427_, v_y_421_, v_nW_422_, v_n_423_, v_00_u03c7_425_, v_s_424_);
v___x_429_ = lean_apply_5(v_nB_426_, v_y_421_, v_nW_422_, v_n_423_, v_00_u03c7_425_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc(lean_object* v_D_430_, lean_object* v_r_431_, lean_object* v_j_432_, lean_object* v_p_433_, lean_object* v_L_434_, lean_object* v_B_435_, lean_object* v_y_436_, lean_object* v_nW_437_, lean_object* v_n_438_, lean_object* v_s_439_, lean_object* v_00_u03c7_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc___redArg(v_B_435_, v_y_436_, v_nW_437_, v_n_438_, v_s_439_, v_00_u03c7_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc___boxed(lean_object* v_D_442_, lean_object* v_r_443_, lean_object* v_j_444_, lean_object* v_p_445_, lean_object* v_L_446_, lean_object* v_B_447_, lean_object* v_y_448_, lean_object* v_nW_449_, lean_object* v_n_450_, lean_object* v_s_451_, lean_object* v_00_u03c7_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = lp_tree_Formalism_MainNotions_BoundaryLocalData_LocB_nfc(v_D_442_, v_r_443_, v_j_444_, v_p_445_, v_L_446_, v_B_447_, v_y_448_, v_nW_449_, v_n_450_, v_s_451_, v_00_u03c7_452_);
lean_dec_ref(v_L_446_);
lean_dec(v_p_445_);
lean_dec(v_j_444_);
lean_dec(v_r_443_);
lean_dec_ref(v_D_442_);
return v_res_453_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_BoundaryLocalData(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
