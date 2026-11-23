// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.CoefMod
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.GradedWeylDivisibility.FinalD public import Formalism.LocalRingCardinality.DataCoeff public import Formalism.HermitianLattices.StatementLat
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
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_inside_u2082___redArg(lean_object*);
lean_object* lp_tree_Formalism_UG_bc___redArg(lean_object*);
lean_object* lp_mathlib_MulHom_pi___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_DomWeight_detShift(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_detPow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_mfact___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_mfact___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_mfact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_detTwK___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_detTwK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_detTwK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramTw___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramTw___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramTw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_colLat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_colLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_dualFr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_dualFr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_hdualFr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_hdualFr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_tauLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_tauLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_invTrK___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_invTrK___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_invTrK___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_invTrK___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_invTrK___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_invTrK(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_invTrK___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_mfact___redArg___lam__0(lean_object* v_toFun_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_apply_1(v_toFun_1_, v_k_2_);
v___x_4_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_3_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_mfact___redArg(lean_object* v_m_5_){
_start:
{
lean_object* v_support_6_; lean_object* v_toFun_7_; lean_object* v___f_8_; lean_object* v___x_9_; 
v_support_6_ = lean_ctor_get(v_m_5_, 0);
lean_inc(v_support_6_);
v_toFun_7_ = lean_ctor_get(v_m_5_, 1);
lean_inc(v_toFun_7_);
lean_dec_ref(v_m_5_);
v___f_8_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_mfact___redArg___lam__0), 2, 1);
lean_closure_set(v___f_8_, 0, v_toFun_7_);
v___x_9_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v_support_6_, v___f_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_mfact(lean_object* v_00_u03c3_10_, lean_object* v_m_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_L2_DIV_mfact___redArg(v_m_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockS___redArg___lam__0(lean_object* v_f_13_, lean_object* v_inst_14_, lean_object* v_g_15_, lean_object* v_toMul_16_, lean_object* v_toNatCast_17_, lean_object* v_m_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc_ref_n(v_m_18_, 2);
v___x_19_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_18_, v_f_13_);
v___x_20_ = lean_apply_1(v_inst_14_, v___x_19_);
v___x_21_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_18_, v_g_15_);
lean_inc(v_toMul_16_);
v___x_22_ = lean_apply_2(v_toMul_16_, v___x_20_, v___x_21_);
v___x_23_ = lp_tree_Formalism_L2_DIV_mfact___redArg(v_m_18_);
v___x_24_ = lean_apply_1(v_toNatCast_17_, v___x_23_);
v___x_25_ = lean_apply_2(v_toMul_16_, v___x_22_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockS___redArg(lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_f_28_, lean_object* v_g_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_toSemiring_32_; lean_object* v_toAddCommMonoid_33_; lean_object* v_support_34_; lean_object* v___x_35_; lean_object* v_toMul_36_; lean_object* v___x_37_; lean_object* v_toRing_38_; lean_object* v___x_39_; lean_object* v_toAddMonoidWithOne_40_; lean_object* v_toNatCast_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v___x_30_ = lp_mathlib_Field_toSemifield___redArg(v_inst_26_);
v___x_31_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_30_);
v_toSemiring_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref(v_toSemiring_32_);
lean_dec_ref(v___x_31_);
v_toAddCommMonoid_33_ = lean_ctor_get(v_toSemiring_32_, 0);
lean_inc_ref(v_toAddCommMonoid_33_);
v_support_34_ = lean_ctor_get(v_f_28_, 0);
lean_inc(v_support_34_);
v___x_35_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_32_);
v_toMul_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_toMul_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_26_);
v_toRing_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc_ref(v_toRing_38_);
lean_dec_ref(v___x_37_);
v___x_39_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_38_);
v_toAddMonoidWithOne_40_ = lean_ctor_get(v___x_39_, 1);
lean_inc_ref(v_toAddMonoidWithOne_40_);
lean_dec_ref(v___x_39_);
v_toNatCast_41_ = lean_ctor_get(v_toAddMonoidWithOne_40_, 0);
lean_inc(v_toNatCast_41_);
lean_dec_ref(v_toAddMonoidWithOne_40_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_fockS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_42_, 0, v_f_28_);
lean_closure_set(v___f_42_, 1, v_inst_27_);
lean_closure_set(v___f_42_, 2, v_g_29_);
lean_closure_set(v___f_42_, 3, v_toMul_36_);
lean_closure_set(v___f_42_, 4, v_toNatCast_41_);
v___x_43_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_33_, v_support_34_, v___f_42_);
lean_dec_ref(v_toAddCommMonoid_33_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_fockS(lean_object* v_K_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_00_u03c3_47_, lean_object* v_f_48_, lean_object* v_g_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_tree_Formalism_L2_DIV_fockS___redArg(v_inst_45_, v_inst_46_, v_f_48_, v_g_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_detTwK___redArg___lam__0(lean_object* v_g_51_, lean_object* v_lam_52_, lean_object* v_n_53_, lean_object* v_toCommRing_54_, lean_object* v_00_u03c4_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc(v_00_u03c4_55_);
v___x_56_ = lean_apply_1(v_g_51_, v_00_u03c4_55_);
v___x_57_ = lean_apply_1(v_lam_52_, v_00_u03c4_55_);
v___x_58_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v_n_53_, v___x_57_);
v___x_59_ = lp_tree_Formalism_BasicNotions_detPow___redArg(v_toCommRing_54_, v_n_53_, v___x_56_, v___x_58_);
lean_dec(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_detTwK___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_n_62_, lean_object* v_lam_63_, lean_object* v_g_64_){
_start:
{
lean_object* v_toCommRing_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_toCommRing_65_ = lean_ctor_get(v_inst_60_, 0);
lean_inc_ref_n(v_toCommRing_65_, 2);
lean_dec_ref(v_inst_60_);
v___f_66_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_detTwK___redArg___lam__0), 5, 4);
lean_closure_set(v___f_66_, 0, v_g_64_);
lean_closure_set(v___f_66_, 1, v_lam_63_);
lean_closure_set(v___f_66_, 2, v_n_62_);
lean_closure_set(v___f_66_, 3, v_toCommRing_65_);
v___x_67_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_65_);
lean_dec_ref(v_toCommRing_65_);
v___x_68_ = lp_mathlib_Finset_prod___redArg(v___x_67_, v_inst_61_, v___f_66_);
lean_dec_ref(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_detTwK(lean_object* v_K_69_, lean_object* v_inst_70_, lean_object* v_00_u03b9_71_, lean_object* v_inst_72_, lean_object* v_n_73_, lean_object* v_lam_74_, lean_object* v_g_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_tree_Formalism_L2_DIV_detTwK___redArg(v_inst_70_, v_inst_72_, v_n_73_, v_lam_74_, v_g_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramTw___redArg___lam__0(lean_object* v_n_77_, lean_object* v_G_78_, lean_object* v___x_79_, lean_object* v_toCommRing_80_, lean_object* v_lam_81_, lean_object* v_toZPow_82_, lean_object* v_00_u03c4_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_113__overap_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
lean_inc(v_n_77_);
v___x_84_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_84_, 0, v_n_77_);
lean_inc(v_00_u03c4_83_);
v___x_85_ = lean_apply_1(v_G_78_, v_00_u03c4_83_);
v___x_113__overap_86_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___x_84_, v___x_79_, v_toCommRing_80_);
v___x_87_ = lean_apply_1(v___x_113__overap_86_, v___x_85_);
v___x_88_ = lean_apply_1(v_lam_81_, v_00_u03c4_83_);
v___x_89_ = lp_tree_Formalism_BasicNotions_DomWeight_detShift(v_n_77_, v___x_88_);
lean_dec(v_n_77_);
v___x_90_ = lean_apply_2(v_toZPow_82_, v___x_89_, v___x_87_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramTw___redArg(lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_n_93_, lean_object* v_lam_94_, lean_object* v_G_95_){
_start:
{
lean_object* v_toCommRing_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_toZPow_100_; lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___x_103_; 
v_toCommRing_96_ = lean_ctor_get(v_inst_91_, 0);
lean_inc_ref(v_toCommRing_96_);
v___x_97_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_toCommRing_96_);
v___x_98_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_91_);
v___x_99_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_98_);
lean_dec_ref(v___x_98_);
v_toZPow_100_ = lean_ctor_get(v___x_99_, 3);
lean_inc(v_toZPow_100_);
lean_dec_ref(v___x_99_);
lean_inc(v_n_93_);
v___x_101_ = l_List_finRange(v_n_93_);
v___f_102_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_gramTw___redArg___lam__0), 7, 6);
lean_closure_set(v___f_102_, 0, v_n_93_);
lean_closure_set(v___f_102_, 1, v_G_95_);
lean_closure_set(v___f_102_, 2, v___x_101_);
lean_closure_set(v___f_102_, 3, v_toCommRing_96_);
lean_closure_set(v___f_102_, 4, v_lam_94_);
lean_closure_set(v___f_102_, 5, v_toZPow_100_);
v___x_103_ = lp_mathlib_Finset_prod___redArg(v___x_97_, v_inst_92_, v___f_102_);
lean_dec_ref(v___x_97_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramTw(lean_object* v_K_104_, lean_object* v_inst_105_, lean_object* v_00_u03b9_106_, lean_object* v_inst_107_, lean_object* v_n_108_, lean_object* v_lam_109_, lean_object* v_G_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lp_tree_Formalism_L2_DIV_gramTw___redArg(v_inst_105_, v_inst_107_, v_n_108_, v_lam_109_, v_G_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_colLat(lean_object* v_K_112_, lean_object* v_inst_113_, lean_object* v_n_114_, lean_object* v_B_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_colLat___boxed(lean_object* v_K_117_, lean_object* v_inst_118_, lean_object* v_n_119_, lean_object* v_B_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_Formalism_L2_DIV_colLat(v_K_117_, v_inst_118_, v_n_119_, v_B_120_);
lean_dec_ref(v_B_120_);
lean_dec(v_n_119_);
lean_dec_ref(v_inst_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_dualFr(lean_object* v_K_122_, lean_object* v_inst_123_, lean_object* v_n_124_, lean_object* v_M_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_dualFr___boxed(lean_object* v_K_127_, lean_object* v_inst_128_, lean_object* v_n_129_, lean_object* v_M_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Formalism_L2_DIV_dualFr(v_K_127_, v_inst_128_, v_n_129_, v_M_130_);
lean_dec(v_n_129_);
lean_dec_ref(v_inst_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_hdualFr(lean_object* v_K_132_, lean_object* v_inst_133_, lean_object* v_n_134_, lean_object* v_inst_135_, lean_object* v_G_136_, lean_object* v_M_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_hdualFr___boxed(lean_object* v_K_139_, lean_object* v_inst_140_, lean_object* v_n_141_, lean_object* v_inst_142_, lean_object* v_G_143_, lean_object* v_M_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = lp_tree_Formalism_L2_DIV_hdualFr(v_K_139_, v_inst_140_, v_n_141_, v_inst_142_, v_G_143_, v_M_144_);
lean_dec(v_G_143_);
lean_dec(v_inst_142_);
lean_dec(v_n_141_);
lean_dec_ref(v_inst_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gLat(lean_object* v_K_146_, lean_object* v_inst_147_, lean_object* v_n_148_, lean_object* v_g_149_, lean_object* v_M_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gLat___boxed(lean_object* v_K_152_, lean_object* v_inst_153_, lean_object* v_n_154_, lean_object* v_g_155_, lean_object* v_M_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_tree_Formalism_L2_DIV_gLat(v_K_152_, v_inst_153_, v_n_154_, v_g_155_, v_M_156_);
lean_dec_ref(v_g_155_);
lean_dec(v_n_154_);
lean_dec_ref(v_inst_153_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_tauLat(lean_object* v_E_158_, lean_object* v_K_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_00_u03b9_162_, lean_object* v_n_163_, lean_object* v_emb_164_, lean_object* v_00_u03c4_165_, lean_object* v_L_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_tauLat___boxed(lean_object* v_E_168_, lean_object* v_K_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_00_u03b9_172_, lean_object* v_n_173_, lean_object* v_emb_174_, lean_object* v_00_u03c4_175_, lean_object* v_L_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = lp_tree_Formalism_L2_DIV_tauLat(v_E_168_, v_K_169_, v_inst_170_, v_inst_171_, v_00_u03b9_172_, v_n_173_, v_emb_174_, v_00_u03c4_175_, v_L_176_);
lean_dec(v_00_u03c4_175_);
lean_dec(v_emb_174_);
lean_dec(v_n_173_);
lean_dec_ref(v_inst_171_);
lean_dec_ref(v_inst_170_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL___redArg___lam__0(lean_object* v_emb_178_, lean_object* v_00_u03c4_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_36__overap_182_; lean_object* v___x_183_; 
v___x_181_ = lean_apply_1(v_emb_178_, v_00_u03c4_179_);
v___x_36__overap_182_ = lp_tree_Formalism_UG_bc___redArg(v___x_181_);
v___x_183_ = lean_apply_1(v___x_36__overap_182_, v___y_180_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL___redArg(lean_object* v_emb_184_){
_start:
{
lean_object* v___f_185_; lean_object* v___f_186_; 
v___f_185_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_embGL___redArg___lam__0), 3, 1);
lean_closure_set(v___f_185_, 0, v_emb_184_);
v___f_186_ = lean_alloc_closure((void*)(lp_mathlib_MulHom_pi___redArg___lam__0), 3, 1);
lean_closure_set(v___f_186_, 0, v___f_185_);
return v___f_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL(lean_object* v_E_187_, lean_object* v_K_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_00_u03b9_191_, lean_object* v_n_192_, lean_object* v_emb_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_tree_Formalism_L2_DIV_embGL___redArg(v_emb_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_embGL___boxed(lean_object* v_E_195_, lean_object* v_K_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_00_u03b9_199_, lean_object* v_n_200_, lean_object* v_emb_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lp_tree_Formalism_L2_DIV_embGL(v_E_195_, v_K_196_, v_inst_197_, v_inst_198_, v_00_u03b9_199_, v_n_200_, v_emb_201_);
lean_dec(v_n_200_);
lean_dec_ref(v_inst_198_);
lean_dec_ref(v_inst_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_invTrK___lam__0(lean_object* v_g_203_, lean_object* v_00_u03c4_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_apply_1(v_g_203_, v_00_u03c4_204_);
v___x_206_ = lp_tree_Formalism_BasicNotions_inside_u2082___redArg(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_invTrK(lean_object* v_K_208_, lean_object* v_inst_209_, lean_object* v_00_u03b9_210_, lean_object* v_n_211_){
_start:
{
lean_object* v___f_212_; 
v___f_212_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_invTrK___closed__0));
return v___f_212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_invTrK___boxed(lean_object* v_K_213_, lean_object* v_inst_214_, lean_object* v_00_u03b9_215_, lean_object* v_n_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = lp_tree_Formalism_L2_DIV_invTrK(v_K_213_, v_inst_214_, v_00_u03b9_215_, v_n_216_);
lean_dec(v_n_216_);
lean_dec_ref(v_inst_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK___redArg___lam__0(lean_object* v_emb_218_, lean_object* v_00_u03c4_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_apply_2(v_emb_218_, v_00_u03c4_219_, v___y_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK___redArg(lean_object* v_emb_222_, lean_object* v_J_223_, lean_object* v_00_u03c4_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; 
v___f_227_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_gramK___redArg___lam__0), 3, 2);
lean_closure_set(v___f_227_, 0, v_emb_222_);
lean_closure_set(v___f_227_, 1, v_00_u03c4_224_);
v___x_228_ = lp_mathlib_Matrix_map___redArg(v_J_223_, v___f_227_, v_a_225_, v_a_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK(lean_object* v_E_229_, lean_object* v_K_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_00_u03b9_233_, lean_object* v_n_234_, lean_object* v_emb_235_, lean_object* v_J_236_, lean_object* v_00_u03c4_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_tree_Formalism_L2_DIV_gramK___redArg(v_emb_235_, v_J_236_, v_00_u03c4_237_, v_a_238_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_gramK___boxed(lean_object* v_E_241_, lean_object* v_K_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_00_u03b9_245_, lean_object* v_n_246_, lean_object* v_emb_247_, lean_object* v_J_248_, lean_object* v_00_u03c4_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_tree_Formalism_L2_DIV_gramK(v_E_241_, v_K_242_, v_inst_243_, v_inst_244_, v_00_u03b9_245_, v_n_246_, v_emb_247_, v_J_248_, v_00_u03c4_249_, v_a_250_, v_a_251_);
lean_dec(v_n_246_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
return v_res_252_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalD(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataCoeff(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefMod(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataCoeff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_StatementLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
