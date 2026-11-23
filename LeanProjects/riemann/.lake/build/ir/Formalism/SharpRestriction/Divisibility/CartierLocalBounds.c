// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.CartierLocalBounds
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataDIV public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant
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
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
uint8_t lp_mathlib_Nat_instDecidablePredEven(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_MvPolynomial_coeff___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_Finsupp_prod___at___00Nat_floorRoot_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dR___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___lam__0(lean_object* v_l_1_, lean_object* v___x_2_, lean_object* v_t_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_nat_pow(v_l_1_, v___x_2_);
v___x_5_ = lean_nat_pow(v___x_4_, v_t_3_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___lam__0___boxed(lean_object* v_l_6_, lean_object* v___x_7_, lean_object* v_t_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___lam__0(v_l_6_, v___x_7_, v_t_8_);
lean_dec(v_t_8_);
lean_dec(v___x_7_);
lean_dec(v_l_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE(lean_object* v_l_10_, lean_object* v_i_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_sub(v_i_11_, v___x_12_);
v___x_14_ = lean_unsigned_to_nat(2u);
lean_inc(v_l_10_);
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___lam__0___boxed), 3, 2);
lean_closure_set(v___f_15_, 0, v_l_10_);
lean_closure_set(v___f_15_, 1, v___x_14_);
v___x_16_ = lean_nat_shiftr(v___x_13_, v___x_12_);
lean_dec(v___x_13_);
v___x_17_ = l_List_range(v___x_16_);
v___x_18_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_17_, v___f_15_);
v___x_19_ = lean_nat_mul(v_l_10_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v_l_10_);
v___x_20_ = lean_nat_add(v___x_12_, v___x_19_);
lean_dec(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_expE___boxed(lean_object* v_l_21_, lean_object* v_i_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_expE(v_l_21_, v_i_22_);
lean_dec(v_i_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___lam__0(lean_object* v_x_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_mathlib_Nat_factorialBinarySplitting(v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___lam__0___boxed(lean_object* v_x_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___lam__0(v_x_27_, v_k_28_);
lean_dec(v_k_28_);
lean_dec(v_x_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg(lean_object* v_m_31_){
_start:
{
lean_object* v___f_32_; lean_object* v___x_33_; 
v___f_32_ = ((lean_object*)(lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg___closed__0));
v___x_33_ = lp_mathlib_Finsupp_prod___at___00Nat_floorRoot_spec__0___redArg(v_m_31_, v___f_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact(lean_object* v_00_u03c3_34_, lean_object* v_m_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg(v_m_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0___redArg___lam__0(lean_object* v_P_37_, lean_object* v_toNatCast_38_, lean_object* v_toMul_39_, lean_object* v_g_40_, lean_object* v_m_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_inc_ref_n(v_m_41_, 2);
v___x_42_ = lp_mathlib_MvPolynomial_coeff___redArg(v_m_41_, v_P_37_);
v___x_43_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_mfact___redArg(v_m_41_);
v___x_44_ = lean_apply_1(v_toNatCast_38_, v___x_43_);
lean_inc(v_toMul_39_);
v___x_45_ = lean_apply_2(v_toMul_39_, v___x_42_, v___x_44_);
v___x_46_ = lean_apply_1(v_g_40_, v_m_41_);
v___x_47_ = lean_apply_2(v_toMul_39_, v___x_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0___redArg(lean_object* v_inst_48_, lean_object* v_P_49_, lean_object* v_g_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v_toSemiring_53_; lean_object* v_toAddCommMonoid_54_; lean_object* v_support_55_; lean_object* v___x_56_; lean_object* v_toMul_57_; lean_object* v___x_58_; lean_object* v_toRing_59_; lean_object* v___x_60_; lean_object* v_toAddMonoidWithOne_61_; lean_object* v_toNatCast_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
v___x_51_ = lp_mathlib_Field_toSemifield___redArg(v_inst_48_);
v___x_52_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_51_);
v_toSemiring_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc_ref(v_toSemiring_53_);
lean_dec_ref(v___x_52_);
v_toAddCommMonoid_54_ = lean_ctor_get(v_toSemiring_53_, 0);
lean_inc_ref(v_toAddCommMonoid_54_);
v_support_55_ = lean_ctor_get(v_P_49_, 0);
lean_inc(v_support_55_);
v___x_56_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_53_);
v_toMul_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_toMul_57_);
lean_dec_ref(v___x_56_);
v___x_58_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_48_);
v_toRing_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc_ref(v_toRing_59_);
lean_dec_ref(v___x_58_);
v___x_60_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_59_);
v_toAddMonoidWithOne_61_ = lean_ctor_get(v___x_60_, 1);
lean_inc_ref(v_toAddMonoidWithOne_61_);
lean_dec_ref(v___x_60_);
v_toNatCast_62_ = lean_ctor_get(v_toAddMonoidWithOne_61_, 0);
lean_inc(v_toNatCast_62_);
lean_dec_ref(v_toAddMonoidWithOne_61_);
v___f_63_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0___redArg___lam__0), 5, 4);
lean_closure_set(v___f_63_, 0, v_P_49_);
lean_closure_set(v___f_63_, 1, v_toNatCast_62_);
lean_closure_set(v___f_63_, 2, v_toMul_57_);
lean_closure_set(v___f_63_, 3, v_g_50_);
v___x_64_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_54_, v_support_55_, v___f_63_);
lean_dec_ref(v_toAddCommMonoid_54_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0(lean_object* v_C_65_, lean_object* v_inst_66_, lean_object* v_00_u03c3_67_, lean_object* v_P_68_, lean_object* v_g_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_jetAt0___redArg(v_inst_66_, v_P_68_, v_g_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dL___redArg___lam__0(lean_object* v_00_u03bc_71_, lean_object* v_c_72_){
_start:
{
lean_object* v_toFun_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_toFun_73_ = lean_ctor_get(v_00_u03bc_71_, 1);
lean_inc(v_toFun_73_);
lean_dec_ref(v_00_u03bc_71_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v_c_72_);
v___x_75_ = lean_apply_1(v_toFun_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dL___redArg(lean_object* v_inst_76_, lean_object* v_00_u03bc_77_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___f_78_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_CartierLocalBounds_dL___redArg___lam__0), 2, 1);
lean_closure_set(v___f_78_, 0, v_00_u03bc_77_);
v___x_79_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_80_ = lp_mathlib_Finset_sum___redArg(v___x_79_, v_inst_76_, v___f_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dL(lean_object* v_00_u03b9_81_, lean_object* v_00_u03b9_x27_82_, lean_object* v_inst_83_, lean_object* v_00_u03bc_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_dL___redArg(v_inst_83_, v_00_u03bc_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dR___redArg___lam__0(lean_object* v_00_u03bc_86_, lean_object* v_b_87_){
_start:
{
lean_object* v_toFun_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_toFun_88_ = lean_ctor_get(v_00_u03bc_86_, 1);
lean_inc(v_toFun_88_);
lean_dec_ref(v_00_u03bc_86_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_b_87_);
v___x_90_ = lean_apply_1(v_toFun_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dR___redArg(lean_object* v_inst_91_, lean_object* v_00_u03bc_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_CartierLocalBounds_dR___redArg___lam__0), 2, 1);
lean_closure_set(v___f_93_, 0, v_00_u03bc_92_);
v___x_94_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_95_ = lp_mathlib_Finset_sum___redArg(v___x_94_, v_inst_91_, v___f_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_dR(lean_object* v_00_u03b9_96_, lean_object* v_00_u03b9_x27_97_, lean_object* v_inst_98_, lean_object* v_00_u03bc_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_dR___redArg(v_inst_98_, v_00_u03bc_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___redArg(lean_object* v_00_u039b_101_){
_start:
{
lean_object* v_r_102_; lean_object* v_j_103_; lean_object* v_j_x27_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_r_102_ = lean_ctor_get(v_00_u039b_101_, 0);
v_j_103_ = lean_ctor_get(v_00_u039b_101_, 1);
v_j_x27_104_ = lean_ctor_get(v_00_u039b_101_, 2);
v___x_105_ = lean_nat_sub(v_r_102_, v_j_x27_104_);
v___x_106_ = lean_nat_sub(v___x_105_, v_j_103_);
lean_dec(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___redArg___boxed(lean_object* v_00_u039b_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___redArg(v_00_u039b_107_);
lean_dec_ref(v_00_u039b_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn(lean_object* v_l_109_, lean_object* v_d_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_00_u039b_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___redArg(v_00_u039b_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn___boxed(lean_object* v_l_115_, lean_object* v_d_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_00_u039b_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_nn(v_l_115_, v_d_116_, v_inst_117_, v_inst_118_, v_00_u039b_119_);
lean_dec_ref(v_00_u039b_119_);
lean_dec(v_d_116_);
lean_dec(v_l_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___redArg(lean_object* v_00_u039b_121_){
_start:
{
lean_object* v_j_122_; lean_object* v_j_x27_123_; lean_object* v___x_124_; 
v_j_122_ = lean_ctor_get(v_00_u039b_121_, 1);
v_j_x27_123_ = lean_ctor_get(v_00_u039b_121_, 2);
v___x_124_ = lean_nat_add(v_j_122_, v_j_x27_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___redArg___boxed(lean_object* v_00_u039b_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___redArg(v_00_u039b_125_);
lean_dec_ref(v_00_u039b_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm(lean_object* v_l_127_, lean_object* v_d_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_00_u039b_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___redArg(v_00_u039b_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm___boxed(lean_object* v_l_133_, lean_object* v_d_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_00_u039b_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_mm(v_l_133_, v_d_134_, v_inst_135_, v_inst_136_, v_00_u039b_137_);
lean_dec_ref(v_00_u039b_137_);
lean_dec(v_d_134_);
lean_dec(v_l_133_);
return v_res_138_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_mod(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_unsigned_to_nat(2u);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_nat_mod(v___x_143_, v___x_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg(lean_object* v_d_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lp_mathlib_ZMod_val(v_d_145_, v_a_146_);
v___x_148_ = lp_mathlib_Nat_instDecidablePredEven(v___x_147_);
lean_dec(v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__0, &lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__0);
return v___x_149_;
}
else
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__1, &lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__1_once, _init_lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___closed__1);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg___boxed(lean_object* v_d_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg(v_d_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec(v_d_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg(lean_object* v_l_154_, lean_object* v_d_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_00___u039b_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___redArg(v_d_155_, v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg___boxed(lean_object* v_l_161_, lean_object* v_d_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_00___u039b_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lp_tree_Formalism_MainNotions_CartierLocalBounds_LocD_bg(v_l_161_, v_d_162_, v_inst_163_, v_inst_164_, v_00___u039b_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_00___u039b_165_);
lean_dec(v_d_162_);
lean_dec(v_l_161_);
return v_res_167_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_CartierLocalBounds(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
