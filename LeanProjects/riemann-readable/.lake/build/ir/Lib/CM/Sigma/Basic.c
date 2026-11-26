// Lean compiler output
// Module: Lib.CM.Sigma.Basic
// Imports: public import Init public meta import Init public import Lib.General.NumberTheory.ImaginaryQuadraticField public import Lib.Shimura.ComplexTheta.DimensionFormula
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_starRingEnd___at___00Complex_conjAe_spec__0___lam__0(lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_abs___at___00BoundingSieve_errSum_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_PeriodPair_area(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_PeriodPair_area(lean_object* v_L_1_){
_start:
{
lean_object* v_00_u03c9_u2081_2_; lean_object* v_00_u03c9_u2082_3_; lean_object* v___x_4_; lean_object* v_re_5_; lean_object* v_im_6_; lean_object* v___x_7_; lean_object* v_im_8_; lean_object* v___x_9_; 
v_00_u03c9_u2081_2_ = lean_ctor_get(v_L_1_, 0);
lean_inc_ref(v_00_u03c9_u2081_2_);
v_00_u03c9_u2082_3_ = lean_ctor_get(v_L_1_, 1);
lean_inc_ref(v_00_u03c9_u2082_3_);
lean_dec_ref(v_L_1_);
v___x_4_ = lp_mathlib_starRingEnd___at___00Complex_conjAe_spec__0___lam__0(v_00_u03c9_u2081_2_);
v_re_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_re_5_);
v_im_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_im_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_5_, v_im_6_, v_00_u03c9_u2082_3_);
v_im_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_im_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = lp_mathlib_abs___at___00BoundingSieve_errSum_spec__0(v_im_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_GRH_New_CMLattice_00_u039b___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b(lean_object* v_d_14_, lean_object* v_C_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CMLattice_00_u039b___boxed(lean_object* v_d_17_, lean_object* v_C_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_GRH_New_CMLattice_00_u039b(v_d_17_, v_C_18_);
lean_dec_ref(v_C_18_);
lean_dec(v_d_17_);
return v_res_19_;
}
}
static lean_object* _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_20_; lean_object* v_intZero_21_; 
v_natZero_20_ = lean_unsigned_to_nat(0u);
v_intZero_21_ = lean_nat_to_int(v_natZero_20_);
return v_intZero_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg(lean_object* v_n_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
lean_object* v_intZero_25_; uint8_t v_isNeg_26_; 
v_intZero_25_ = lean_obj_once(&lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0, &lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_26_ = lean_int_dec_lt(v_n_22_, v_intZero_25_);
if (v_isNeg_26_ == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
lean_dec(v_h__2_24_);
v_a_27_ = lean_nat_abs(v_n_22_);
v___x_28_ = lean_apply_1(v_h__1_23_, v_a_27_);
return v___x_28_;
}
else
{
lean_object* v_abs_29_; lean_object* v_one_30_; lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_23_);
v_abs_29_ = lean_nat_abs(v_n_22_);
v_one_30_ = lean_unsigned_to_nat(1u);
v_a_31_ = lean_nat_sub(v_abs_29_, v_one_30_);
lean_dec(v_abs_29_);
v___x_32_ = lean_apply_1(v_h__2_24_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___boxed(lean_object* v_n_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg(v_n_33_, v_h__1_34_, v_h__2_35_);
lean_dec(v_n_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter(lean_object* v_motive_37_, lean_object* v_n_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v_intZero_41_; uint8_t v_isNeg_42_; 
v_intZero_41_ = lean_obj_once(&lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0, &lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_42_ = lean_int_dec_lt(v_n_38_, v_intZero_41_);
if (v_isNeg_42_ == 0)
{
lean_object* v_a_43_; lean_object* v___x_44_; 
lean_dec(v_h__2_40_);
v_a_43_ = lean_nat_abs(v_n_38_);
v___x_44_ = lean_apply_1(v_h__1_39_, v_a_43_);
return v___x_44_;
}
else
{
lean_object* v_abs_45_; lean_object* v_one_46_; lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_39_);
v_abs_45_ = lean_nat_abs(v_n_38_);
v_one_46_ = lean_unsigned_to_nat(1u);
v_a_47_ = lean_nat_sub(v_abs_45_, v_one_46_);
lean_dec(v_abs_45_);
v___x_48_ = lean_apply_1(v_h__2_40_, v_a_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter___boxed(lean_object* v_motive_49_, lean_object* v_n_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_neg_match__1_splitter(v_motive_49_, v_n_50_, v_h__1_51_, v_h__2_52_);
lean_dec(v_n_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
lean_object* v_zero_57_; uint8_t v_isZero_58_; 
v_zero_57_ = lean_unsigned_to_nat(0u);
v_isZero_58_ = lean_nat_dec_eq(v_x_54_, v_zero_57_);
if (v_isZero_58_ == 1)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__2_56_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_55_, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_one_61_; lean_object* v_n_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_55_);
v_one_61_ = lean_unsigned_to_nat(1u);
v_n_62_ = lean_nat_sub(v_x_54_, v_one_61_);
v___x_63_ = lean_apply_1(v_h__2_56_, v_n_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___redArg___boxed(lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___redArg(v_x_64_, v_h__1_65_, v_h__2_66_);
lean_dec(v_x_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter(lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_x_69_, v_zero_72_);
if (v_isZero_73_ == 1)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__2_71_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__1_70_, v___x_74_);
return v___x_75_;
}
else
{
lean_object* v_one_76_; lean_object* v_n_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_70_);
v_one_76_ = lean_unsigned_to_nat(1u);
v_n_77_ = lean_nat_sub(v_x_69_, v_one_76_);
v___x_78_ = lean_apply_1(v_h__2_71_, v_n_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter___boxed(lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_negOfNat_match__1_splitter(v_motive_79_, v_x_80_, v_h__1_81_, v_h__2_82_);
lean_dec(v_x_80_);
return v_res_83_;
}
}
static lean_object* _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_84_; lean_object* v_intZero_85_; 
v_natZero_84_ = lean_unsigned_to_nat(0u);
v_intZero_85_ = lean_nat_to_int(v_natZero_84_);
return v_intZero_85_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg(lean_object* v_m_86_, lean_object* v_n_87_, lean_object* v_h__1_88_, lean_object* v_h__2_89_, lean_object* v_h__3_90_, lean_object* v_h__4_91_){
_start:
{
lean_object* v_intZero_92_; uint8_t v_isNeg_93_; 
v_intZero_92_ = lean_obj_once(&lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0, &lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0_once, _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0);
v_isNeg_93_ = lean_int_dec_lt(v_m_86_, v_intZero_92_);
if (v_isNeg_93_ == 0)
{
lean_object* v_a_94_; uint8_t v_isNeg_95_; 
lean_dec(v_h__4_91_);
lean_dec(v_h__3_90_);
v_a_94_ = lean_nat_abs(v_m_86_);
v_isNeg_95_ = lean_int_dec_lt(v_n_87_, v_intZero_92_);
if (v_isNeg_95_ == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
lean_dec(v_h__2_89_);
v_a_96_ = lean_nat_abs(v_n_87_);
v___x_97_ = lean_apply_2(v_h__1_88_, v_a_94_, v_a_96_);
return v___x_97_;
}
else
{
lean_object* v_abs_98_; lean_object* v_one_99_; lean_object* v_a_100_; lean_object* v___x_101_; 
lean_dec(v_h__1_88_);
v_abs_98_ = lean_nat_abs(v_n_87_);
v_one_99_ = lean_unsigned_to_nat(1u);
v_a_100_ = lean_nat_sub(v_abs_98_, v_one_99_);
lean_dec(v_abs_98_);
v___x_101_ = lean_apply_2(v_h__2_89_, v_a_94_, v_a_100_);
return v___x_101_;
}
}
else
{
lean_object* v_abs_102_; lean_object* v_one_103_; lean_object* v_a_104_; uint8_t v_isNeg_105_; 
lean_dec(v_h__2_89_);
lean_dec(v_h__1_88_);
v_abs_102_ = lean_nat_abs(v_m_86_);
v_one_103_ = lean_unsigned_to_nat(1u);
v_a_104_ = lean_nat_sub(v_abs_102_, v_one_103_);
lean_dec(v_abs_102_);
v_isNeg_105_ = lean_int_dec_lt(v_n_87_, v_intZero_92_);
if (v_isNeg_105_ == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__4_91_);
v_a_106_ = lean_nat_abs(v_n_87_);
v___x_107_ = lean_apply_2(v_h__3_90_, v_a_104_, v_a_106_);
return v___x_107_;
}
else
{
lean_object* v_abs_108_; lean_object* v_a_109_; lean_object* v___x_110_; 
lean_dec(v_h__3_90_);
v_abs_108_ = lean_nat_abs(v_n_87_);
v_a_109_ = lean_nat_sub(v_abs_108_, v_one_103_);
lean_dec(v_abs_108_);
v___x_110_ = lean_apply_2(v_h__4_91_, v_a_104_, v_a_109_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___boxed(lean_object* v_m_111_, lean_object* v_n_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_, lean_object* v_h__3_115_, lean_object* v_h__4_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg(v_m_111_, v_n_112_, v_h__1_113_, v_h__2_114_, v_h__3_115_, v_h__4_116_);
lean_dec(v_n_112_);
lean_dec(v_m_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter(lean_object* v_motive_118_, lean_object* v_m_119_, lean_object* v_n_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_, lean_object* v_h__3_123_, lean_object* v_h__4_124_){
_start:
{
lean_object* v_intZero_125_; uint8_t v_isNeg_126_; 
v_intZero_125_ = lean_obj_once(&lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0, &lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0_once, _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___redArg___closed__0);
v_isNeg_126_ = lean_int_dec_lt(v_m_119_, v_intZero_125_);
if (v_isNeg_126_ == 0)
{
lean_object* v_a_127_; uint8_t v_isNeg_128_; 
lean_dec(v_h__4_124_);
lean_dec(v_h__3_123_);
v_a_127_ = lean_nat_abs(v_m_119_);
v_isNeg_128_ = lean_int_dec_lt(v_n_120_, v_intZero_125_);
if (v_isNeg_128_ == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_122_);
v_a_129_ = lean_nat_abs(v_n_120_);
v___x_130_ = lean_apply_2(v_h__1_121_, v_a_127_, v_a_129_);
return v___x_130_;
}
else
{
lean_object* v_abs_131_; lean_object* v_one_132_; lean_object* v_a_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_121_);
v_abs_131_ = lean_nat_abs(v_n_120_);
v_one_132_ = lean_unsigned_to_nat(1u);
v_a_133_ = lean_nat_sub(v_abs_131_, v_one_132_);
lean_dec(v_abs_131_);
v___x_134_ = lean_apply_2(v_h__2_122_, v_a_127_, v_a_133_);
return v___x_134_;
}
}
else
{
lean_object* v_abs_135_; lean_object* v_one_136_; lean_object* v_a_137_; uint8_t v_isNeg_138_; 
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v_abs_135_ = lean_nat_abs(v_m_119_);
v_one_136_ = lean_unsigned_to_nat(1u);
v_a_137_ = lean_nat_sub(v_abs_135_, v_one_136_);
lean_dec(v_abs_135_);
v_isNeg_138_ = lean_int_dec_lt(v_n_120_, v_intZero_125_);
if (v_isNeg_138_ == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
lean_dec(v_h__4_124_);
v_a_139_ = lean_nat_abs(v_n_120_);
v___x_140_ = lean_apply_2(v_h__3_123_, v_a_137_, v_a_139_);
return v___x_140_;
}
else
{
lean_object* v_abs_141_; lean_object* v_a_142_; lean_object* v___x_143_; 
lean_dec(v_h__3_123_);
v_abs_141_ = lean_nat_abs(v_n_120_);
v_a_142_ = lean_nat_sub(v_abs_141_, v_one_136_);
lean_dec(v_abs_141_);
v___x_143_ = lean_apply_2(v_h__4_124_, v_a_137_, v_a_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter___boxed(lean_object* v_motive_144_, lean_object* v_m_145_, lean_object* v_n_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_, lean_object* v_h__3_149_, lean_object* v_h__4_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_add_match__1_splitter(v_motive_144_, v_m_145_, v_n_146_, v_h__1_147_, v_h__2_148_, v_h__3_149_, v_h__4_150_);
lean_dec(v_n_146_);
lean_dec(v_m_145_);
return v_res_151_;
}
}
static lean_object* _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_152_; lean_object* v_intZero_153_; 
v_natZero_152_ = lean_unsigned_to_nat(0u);
v_intZero_153_ = lean_nat_to_int(v_natZero_152_);
return v_intZero_153_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg(lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_, lean_object* v_h__3_158_, lean_object* v_h__4_159_, lean_object* v_h__5_160_){
_start:
{
lean_object* v_natZero_161_; lean_object* v_intZero_162_; uint8_t v_isNeg_163_; 
v_natZero_161_ = lean_unsigned_to_nat(0u);
v_intZero_162_ = lean_obj_once(&lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0, &lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0_once, _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0);
v_isNeg_163_ = lean_int_dec_lt(v_x_154_, v_intZero_162_);
if (v_isNeg_163_ == 0)
{
lean_object* v_a_164_; uint8_t v_isNeg_165_; 
lean_dec(v_h__5_160_);
lean_dec(v_h__4_159_);
lean_dec(v_h__3_158_);
v_a_164_ = lean_nat_abs(v_x_154_);
v_isNeg_165_ = lean_int_dec_lt(v_x_155_, v_intZero_162_);
if (v_isNeg_165_ == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_157_);
v_a_166_ = lean_nat_abs(v_x_155_);
v___x_167_ = lean_apply_2(v_h__1_156_, v_a_164_, v_a_166_);
return v___x_167_;
}
else
{
lean_object* v_abs_168_; lean_object* v_one_169_; lean_object* v_a_170_; lean_object* v___x_171_; 
lean_dec(v_h__1_156_);
v_abs_168_ = lean_nat_abs(v_x_155_);
v_one_169_ = lean_unsigned_to_nat(1u);
v_a_170_ = lean_nat_sub(v_abs_168_, v_one_169_);
lean_dec(v_abs_168_);
v___x_171_ = lean_apply_2(v_h__2_157_, v_a_164_, v_a_170_);
return v___x_171_;
}
}
else
{
lean_object* v_abs_172_; lean_object* v_one_173_; lean_object* v_a_174_; uint8_t v_isNeg_175_; 
lean_dec(v_h__2_157_);
lean_dec(v_h__1_156_);
v_abs_172_ = lean_nat_abs(v_x_154_);
v_one_173_ = lean_unsigned_to_nat(1u);
v_a_174_ = lean_nat_sub(v_abs_172_, v_one_173_);
lean_dec(v_abs_172_);
v_isNeg_175_ = lean_int_dec_lt(v_x_155_, v_intZero_162_);
if (v_isNeg_175_ == 0)
{
lean_object* v_a_176_; uint8_t v_isZero_177_; 
lean_dec(v_h__5_160_);
v_a_176_ = lean_nat_abs(v_x_155_);
v_isZero_177_ = lean_nat_dec_eq(v_a_176_, v_natZero_161_);
if (v_isZero_177_ == 1)
{
lean_object* v___x_178_; 
lean_dec(v_a_176_);
lean_dec(v_h__4_159_);
v___x_178_ = lean_apply_1(v_h__3_158_, v_a_174_);
return v___x_178_;
}
else
{
lean_object* v_n_179_; lean_object* v___x_180_; 
lean_dec(v_h__3_158_);
v_n_179_ = lean_nat_sub(v_a_176_, v_one_173_);
lean_dec(v_a_176_);
v___x_180_ = lean_apply_2(v_h__4_159_, v_a_174_, v_n_179_);
return v___x_180_;
}
}
else
{
lean_object* v_abs_181_; lean_object* v_a_182_; lean_object* v___x_183_; 
lean_dec(v_h__4_159_);
lean_dec(v_h__3_158_);
v_abs_181_ = lean_nat_abs(v_x_155_);
v_a_182_ = lean_nat_sub(v_abs_181_, v_one_173_);
lean_dec(v_abs_181_);
v___x_183_ = lean_apply_2(v_h__5_160_, v_a_174_, v_a_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_, lean_object* v_h__3_188_, lean_object* v_h__4_189_, lean_object* v_h__5_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg(v_x_184_, v_x_185_, v_h__1_186_, v_h__2_187_, v_h__3_188_, v_h__4_189_, v_h__5_190_);
lean_dec(v_x_185_);
lean_dec(v_x_184_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter(lean_object* v_motive_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_h__1_195_, lean_object* v_h__2_196_, lean_object* v_h__3_197_, lean_object* v_h__4_198_, lean_object* v_h__5_199_){
_start:
{
lean_object* v_natZero_200_; lean_object* v_intZero_201_; uint8_t v_isNeg_202_; 
v_natZero_200_ = lean_unsigned_to_nat(0u);
v_intZero_201_ = lean_obj_once(&lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0, &lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0_once, _init_lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___redArg___closed__0);
v_isNeg_202_ = lean_int_dec_lt(v_x_193_, v_intZero_201_);
if (v_isNeg_202_ == 0)
{
lean_object* v_a_203_; uint8_t v_isNeg_204_; 
lean_dec(v_h__5_199_);
lean_dec(v_h__4_198_);
lean_dec(v_h__3_197_);
v_a_203_ = lean_nat_abs(v_x_193_);
v_isNeg_204_ = lean_int_dec_lt(v_x_194_, v_intZero_201_);
if (v_isNeg_204_ == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; 
lean_dec(v_h__2_196_);
v_a_205_ = lean_nat_abs(v_x_194_);
v___x_206_ = lean_apply_2(v_h__1_195_, v_a_203_, v_a_205_);
return v___x_206_;
}
else
{
lean_object* v_abs_207_; lean_object* v_one_208_; lean_object* v_a_209_; lean_object* v___x_210_; 
lean_dec(v_h__1_195_);
v_abs_207_ = lean_nat_abs(v_x_194_);
v_one_208_ = lean_unsigned_to_nat(1u);
v_a_209_ = lean_nat_sub(v_abs_207_, v_one_208_);
lean_dec(v_abs_207_);
v___x_210_ = lean_apply_2(v_h__2_196_, v_a_203_, v_a_209_);
return v___x_210_;
}
}
else
{
lean_object* v_abs_211_; lean_object* v_one_212_; lean_object* v_a_213_; uint8_t v_isNeg_214_; 
lean_dec(v_h__2_196_);
lean_dec(v_h__1_195_);
v_abs_211_ = lean_nat_abs(v_x_193_);
v_one_212_ = lean_unsigned_to_nat(1u);
v_a_213_ = lean_nat_sub(v_abs_211_, v_one_212_);
lean_dec(v_abs_211_);
v_isNeg_214_ = lean_int_dec_lt(v_x_194_, v_intZero_201_);
if (v_isNeg_214_ == 0)
{
lean_object* v_a_215_; uint8_t v_isZero_216_; 
lean_dec(v_h__5_199_);
v_a_215_ = lean_nat_abs(v_x_194_);
v_isZero_216_ = lean_nat_dec_eq(v_a_215_, v_natZero_200_);
if (v_isZero_216_ == 1)
{
lean_object* v___x_217_; 
lean_dec(v_a_215_);
lean_dec(v_h__4_198_);
v___x_217_ = lean_apply_1(v_h__3_197_, v_a_213_);
return v___x_217_;
}
else
{
lean_object* v_n_218_; lean_object* v___x_219_; 
lean_dec(v_h__3_197_);
v_n_218_ = lean_nat_sub(v_a_215_, v_one_212_);
lean_dec(v_a_215_);
v___x_219_ = lean_apply_2(v_h__4_198_, v_a_213_, v_n_218_);
return v___x_219_;
}
}
else
{
lean_object* v_abs_220_; lean_object* v_a_221_; lean_object* v___x_222_; 
lean_dec(v_h__4_198_);
lean_dec(v_h__3_197_);
v_abs_220_ = lean_nat_abs(v_x_194_);
v_a_221_ = lean_nat_sub(v_abs_220_, v_one_212_);
lean_dec(v_abs_220_);
v___x_222_ = lean_apply_2(v_h__5_199_, v_a_213_, v_a_221_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter___boxed(lean_object* v_motive_223_, lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_, lean_object* v_h__4_229_, lean_object* v_h__5_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = lp_GRH___private_Lib_CM_Sigma_Basic_0__Int_ediv_match__1_splitter(v_motive_223_, v_x_224_, v_x_225_, v_h__1_226_, v_h__2_227_, v_h__3_228_, v_h__4_229_, v_h__5_230_);
lean_dec(v_x_225_);
lean_dec(v_x_224_);
return v_res_231_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ComplexTheta_DimensionFormula(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_CM_Sigma_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ComplexTheta_DimensionFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
