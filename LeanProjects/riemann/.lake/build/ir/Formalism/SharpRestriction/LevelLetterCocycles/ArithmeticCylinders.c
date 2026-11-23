// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_eigSp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_eigSp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_eigSp(lean_object* v_O_1_, lean_object* v_K_2_, lean_object* v_V_3_, lean_object* v_X_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_T_12_, lean_object* v_act_13_, lean_object* v_00_u03c0_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_eigSp___boxed(lean_object* v_O_16_, lean_object* v_K_17_, lean_object* v_V_18_, lean_object* v_X_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_T_27_, lean_object* v_act_28_, lean_object* v_00_u03c0_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_eigSp(v_O_16_, v_K_17_, v_V_18_, v_X_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_T_27_, v_act_28_, v_00_u03c0_29_);
lean_dec(v_00_u03c0_29_);
lean_dec(v_act_28_);
lean_dec(v_inst_25_);
lean_dec(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___redArg(lean_object* v_inst_31_, lean_object* v_N_32_, lean_object* v_M_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_nat_dec_lt(v_a_34_, v_N_32_);
if (v___x_36_ == 0)
{
lean_dec(v_b_35_);
lean_dec(v_a_34_);
lean_dec(v_M_33_);
lean_inc(v_inst_31_);
return v_inst_31_;
}
else
{
uint8_t v___x_37_; 
v___x_37_ = lean_nat_dec_lt(v_b_35_, v_N_32_);
if (v___x_37_ == 0)
{
lean_dec(v_b_35_);
lean_dec(v_a_34_);
lean_dec(v_M_33_);
lean_inc(v_inst_31_);
return v_inst_31_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_apply_2(v_M_33_, v_a_34_, v_b_35_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___redArg___boxed(lean_object* v_inst_39_, lean_object* v_N_40_, lean_object* v_M_41_, lean_object* v_a_42_, lean_object* v_b_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___redArg(v_inst_39_, v_N_40_, v_M_41_, v_a_42_, v_b_43_);
lean_dec(v_N_40_);
lean_dec(v_inst_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN(lean_object* v_A_45_, lean_object* v_inst_46_, lean_object* v_N_47_, lean_object* v_M_48_, lean_object* v_a_49_, lean_object* v_b_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___redArg(v_inst_46_, v_N_47_, v_M_48_, v_a_49_, v_b_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___boxed(lean_object* v_A_52_, lean_object* v_inst_53_, lean_object* v_N_54_, lean_object* v_M_55_, lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN(v_A_52_, v_inst_53_, v_N_54_, v_M_55_, v_a_56_, v_b_57_);
lean_dec(v_N_54_);
lean_dec(v_inst_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(lean_object* v_g_59_, lean_object* v_N_60_, lean_object* v_M_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v___x_64_; lean_object* v_toSemiring_65_; lean_object* v___x_66_; lean_object* v_toZero_67_; uint8_t v___x_68_; 
v___x_64_ = lp_mathlib_ZMod_commRing(v_g_59_);
v_toSemiring_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_toSemiring_65_);
lean_dec_ref(v___x_64_);
v___x_66_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_65_);
v_toZero_67_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_toZero_67_);
lean_dec_ref(v___x_66_);
v___x_68_ = lean_nat_dec_lt(v_a_62_, v_N_60_);
if (v___x_68_ == 0)
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
lean_dec(v_M_61_);
return v_toZero_67_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_lt(v_b_63_, v_N_60_);
if (v___x_69_ == 0)
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
lean_dec(v_M_61_);
return v_toZero_67_;
}
else
{
lean_object* v___x_70_; 
lean_dec(v_toZero_67_);
v___x_70_ = lean_apply_2(v_M_61_, v_a_62_, v_b_63_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0___boxed(lean_object* v_g_71_, lean_object* v_N_72_, lean_object* v_M_73_, lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(v_g_71_, v_N_72_, v_M_73_, v_a_74_, v_b_75_);
lean_dec(v_N_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__0(lean_object* v___x_77_, lean_object* v_g_78_, lean_object* v_N_79_, lean_object* v_M_80_, lean_object* v_i_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_nat_add(v_i_81_, v___x_77_);
v___x_83_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(v_g_78_, v_N_79_, v_M_80_, v_i_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__0___boxed(lean_object* v___x_84_, lean_object* v_g_85_, lean_object* v_N_86_, lean_object* v_M_87_, lean_object* v_i_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__0(v___x_84_, v_g_85_, v_N_86_, v_M_87_, v_i_88_);
lean_dec(v_N_86_);
lean_dec(v___x_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__1(lean_object* v_s_90_, lean_object* v_kk_91_, lean_object* v___x_92_, lean_object* v_g_93_, lean_object* v_N_94_, lean_object* v_M_95_, lean_object* v_i_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_97_ = lean_nat_add(v_s_90_, v_kk_91_);
v___x_98_ = lean_nat_add(v___x_97_, v___x_92_);
v___x_99_ = lean_nat_add(v___x_98_, v_i_96_);
lean_dec(v___x_98_);
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_nat_add(v___x_97_, v___x_100_);
lean_dec(v___x_97_);
v___x_102_ = lean_nat_add(v___x_101_, v_i_96_);
lean_dec(v___x_101_);
v___x_103_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(v_g_93_, v_N_94_, v_M_95_, v___x_99_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__1___boxed(lean_object* v_s_104_, lean_object* v_kk_105_, lean_object* v___x_106_, lean_object* v_g_107_, lean_object* v_N_108_, lean_object* v_M_109_, lean_object* v_i_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__1(v_s_104_, v_kk_105_, v___x_106_, v_g_107_, v_N_108_, v_M_109_, v_i_110_);
lean_dec(v_i_110_);
lean_dec(v_N_108_);
lean_dec(v___x_106_);
lean_dec(v_kk_105_);
lean_dec(v_s_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__2(lean_object* v_s_112_, lean_object* v___x_113_, lean_object* v_g_114_, lean_object* v_N_115_, lean_object* v_M_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_nat_add(v_s_112_, v_a_117_);
v___x_119_ = lean_nat_add(v___x_118_, v___x_113_);
v___x_120_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(v_g_114_, v_N_115_, v_M_116_, v___x_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__2___boxed(lean_object* v_s_121_, lean_object* v___x_122_, lean_object* v_g_123_, lean_object* v_N_124_, lean_object* v_M_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__2(v_s_121_, v___x_122_, v_g_123_, v_N_124_, v_M_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec(v_N_124_);
lean_dec(v___x_122_);
lean_dec(v_s_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1_spec__1___lam__0(lean_object* v_toAdd_128_, lean_object* v_x1_129_, lean_object* v_x2_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_apply_2(v_toAdd_128_, v_x1_129_, v_x2_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1_spec__1(lean_object* v_g_132_, lean_object* v_s_133_){
_start:
{
lean_object* v___x_134_; lean_object* v_toSemiring_135_; lean_object* v_toAddCommMonoid_136_; lean_object* v___x_137_; lean_object* v_toZero_138_; lean_object* v_toAdd_139_; lean_object* v___f_140_; lean_object* v___x_141_; 
v___x_134_ = lp_mathlib_ZMod_commRing(v_g_132_);
v_toSemiring_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_toSemiring_135_);
lean_dec_ref(v___x_134_);
v_toAddCommMonoid_136_ = lean_ctor_get(v_toSemiring_135_, 0);
lean_inc_ref(v_toAddCommMonoid_136_);
lean_dec_ref(v_toSemiring_135_);
v___x_137_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_136_);
lean_dec_ref(v_toAddCommMonoid_136_);
v_toZero_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_toZero_138_);
v_toAdd_139_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_toAdd_139_);
lean_dec_ref(v___x_137_);
v___f_140_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1_spec__1___lam__0), 3, 1);
lean_closure_set(v___f_140_, 0, v_toAdd_139_);
v___x_141_ = l_List_foldrTR___redArg(v___f_140_, v_toZero_138_, v_s_133_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1___redArg(lean_object* v_g_142_, lean_object* v_s_143_, lean_object* v_f_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lp_mathlib_Multiset_map___redArg(v_f_144_, v_s_143_);
v___x_146_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1_spec__1(v_g_142_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ(lean_object* v_g_147_, lean_object* v_kk_148_, lean_object* v_s_149_, lean_object* v_N_150_, lean_object* v_M_151_){
_start:
{
lean_object* v___x_152_; lean_object* v_toSemiring_153_; lean_object* v___x_154_; lean_object* v_toAdd_155_; lean_object* v___x_156_; lean_object* v_toZero_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___y_167_; 
lean_inc_n(v_g_147_, 5);
v___x_152_ = lp_mathlib_ZMod_commRing(v_g_147_);
v_toSemiring_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref_n(v_toSemiring_153_, 2);
lean_dec_ref(v___x_152_);
v___x_154_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_153_);
v_toAdd_155_ = lean_ctor_get(v___x_154_, 1);
lean_inc(v_toAdd_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_153_);
v_toZero_157_ = lean_ctor_get(v___x_156_, 1);
lean_inc(v_toZero_157_);
lean_dec_ref(v___x_156_);
v___x_158_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_M_151_, 3);
lean_inc_n(v_N_150_, 3);
v___f_159_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__0___boxed), 5, 4);
lean_closure_set(v___f_159_, 0, v___x_158_);
lean_closure_set(v___f_159_, 1, v_g_147_);
lean_closure_set(v___f_159_, 2, v_N_150_);
lean_closure_set(v___f_159_, 3, v_M_151_);
lean_inc(v_kk_148_);
lean_inc_n(v_s_149_, 2);
v___f_160_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__1___boxed), 7, 6);
lean_closure_set(v___f_160_, 0, v_s_149_);
lean_closure_set(v___f_160_, 1, v_kk_148_);
lean_closure_set(v___f_160_, 2, v___x_158_);
lean_closure_set(v___f_160_, 3, v_g_147_);
lean_closure_set(v___f_160_, 4, v_N_150_);
lean_closure_set(v___f_160_, 5, v_M_151_);
v___f_161_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ArithmeticCylinders_phiJ___lam__2___boxed), 6, 5);
lean_closure_set(v___f_161_, 0, v_s_149_);
lean_closure_set(v___f_161_, 1, v___x_158_);
lean_closure_set(v___f_161_, 2, v_g_147_);
lean_closure_set(v___f_161_, 3, v_N_150_);
lean_closure_set(v___f_161_, 4, v_M_151_);
v___x_162_ = lean_nat_sub(v_s_149_, v___x_158_);
lean_inc(v___x_162_);
v___x_163_ = l_List_range(v___x_162_);
v___x_164_ = lean_nat_dec_le(v___x_158_, v_s_149_);
lean_inc(v___x_163_);
v___x_165_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1___redArg(v_g_147_, v___x_163_, v___f_159_);
if (v___x_164_ == 0)
{
lean_dec(v___x_162_);
lean_dec(v_M_151_);
lean_dec(v_N_150_);
lean_dec(v_s_149_);
v___y_167_ = v_toZero_157_;
goto v___jp_166_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_toZero_157_);
v___x_175_ = lean_nat_add(v_s_149_, v_kk_148_);
lean_dec(v_s_149_);
lean_inc(v___x_175_);
lean_inc(v_M_151_);
lean_inc_n(v_g_147_, 2);
v___x_176_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(v_g_147_, v_N_150_, v_M_151_, v___x_162_, v___x_175_);
v___x_177_ = lean_nat_add(v___x_175_, v___x_158_);
v___x_178_ = lp_tree_Formalism_MainNotions_ArithmeticCylinders_entN___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__0(v_g_147_, v_N_150_, v_M_151_, v___x_175_, v___x_177_);
lean_dec(v_N_150_);
lean_inc(v_toAdd_155_);
v___x_179_ = lean_apply_2(v_toAdd_155_, v___x_176_, v___x_178_);
v___y_167_ = v___x_179_;
goto v___jp_166_;
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_inc_n(v_toAdd_155_, 2);
v___x_168_ = lean_apply_2(v_toAdd_155_, v___x_165_, v___y_167_);
lean_inc(v_g_147_);
v___x_169_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1___redArg(v_g_147_, v___x_163_, v___f_160_);
v___x_170_ = lean_apply_2(v_toAdd_155_, v___x_168_, v___x_169_);
v___x_171_ = lean_nat_sub(v_kk_148_, v___x_158_);
lean_dec(v_kk_148_);
v___x_172_ = l_List_range(v___x_171_);
v___x_173_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1___redArg(v_g_147_, v___x_172_, v___f_161_);
v___x_174_ = lean_apply_2(v_toAdd_155_, v___x_170_, v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1(lean_object* v_g_180_, lean_object* v_00_u03b9_181_, lean_object* v_s_182_, lean_object* v_f_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_ArithmeticCylinders_phiJ_spec__1___redArg(v_g_180_, v_s_182_, v_f_183_);
return v___x_184_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_ArithmeticCylinders(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
