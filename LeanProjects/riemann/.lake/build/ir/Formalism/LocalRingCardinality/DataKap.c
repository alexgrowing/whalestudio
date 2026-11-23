// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataKap
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataDIV public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
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
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
lean_object* lp_tree_Finset_prod___at___00Formalism_G0_esymmR_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_eQ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_eQ___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_eQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_eQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_sigPar(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aPlusQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinusQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinusQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aPlus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_lamProd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_lamProd___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_lamProd(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_eQ___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_eQ(lean_object* v_D_3_, lean_object* v_j_4_, lean_object* v_00_u03c4_5_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_dec_le(v___x_8_, v_j_4_);
if (v___x_9_ == 0)
{
lean_dec(v_00_u03c4_5_);
lean_dec_ref(v_D_3_);
goto v___jp_6_;
}
else
{
lean_object* v_R_10_; lean_object* v_hc_11_; lean_object* v_m_12_; uint8_t v___x_13_; 
v_R_10_ = lean_ctor_get(v_D_3_, 0);
lean_inc_ref(v_R_10_);
v_hc_11_ = lean_ctor_get(v_D_3_, 6);
lean_inc_ref(v_hc_11_);
lean_dec_ref(v_D_3_);
v_m_12_ = lean_ctor_get(v_R_10_, 2);
lean_inc(v_m_12_);
lean_dec_ref(v_R_10_);
v___x_13_ = lean_nat_dec_le(v_j_4_, v_m_12_);
lean_dec(v_m_12_);
if (v___x_13_ == 0)
{
lean_dec_ref(v_hc_11_);
lean_dec(v_00_u03c4_5_);
goto v___jp_6_;
}
else
{
lean_object* v___x_14_; lean_object* v_e_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_14_ = lean_apply_1(v_hc_11_, v_00_u03c4_5_);
v_e_15_ = lean_ctor_get(v___x_14_, 3);
lean_inc_ref(v_e_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lean_nat_sub(v_j_4_, v___x_8_);
v___x_17_ = lean_apply_1(v_e_15_, v___x_16_);
return v___x_17_;
}
}
v___jp_6_:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_eQ___closed__0, &lp_tree_Formalism_BasicNotions_DV_eQ___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_eQ___closed__0);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_eQ___boxed(lean_object* v_D_18_, lean_object* v_j_19_, lean_object* v_00_u03c4_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_BasicNotions_DV_eQ(v_D_18_, v_j_19_, v_00_u03c4_20_);
lean_dec(v_j_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_sigPar(lean_object* v_D_22_, lean_object* v_00_u03c4_23_, lean_object* v_i_24_){
_start:
{
lean_object* v_R_25_; lean_object* v_hc_26_; lean_object* v_k_27_; lean_object* v_m_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_R_25_ = lean_ctor_get(v_D_22_, 0);
lean_inc_ref(v_R_25_);
v_hc_26_ = lean_ctor_get(v_D_22_, 6);
lean_inc_ref(v_hc_26_);
lean_dec_ref(v_D_22_);
v_k_27_ = lean_ctor_get(v_R_25_, 1);
lean_inc(v_k_27_);
v_m_28_ = lean_ctor_get(v_R_25_, 2);
lean_inc(v_m_28_);
lean_dec_ref(v_R_25_);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_sub(v_k_27_, v___x_29_);
lean_dec(v_k_27_);
v___x_31_ = lean_nat_dec_lt(v_i_24_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_nat_sub(v_i_24_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v_i_24_);
v___x_33_ = lean_nat_dec_lt(v___x_32_, v_m_28_);
lean_dec(v_m_28_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec(v___x_32_);
lean_dec_ref(v_hc_26_);
lean_dec(v_00_u03c4_23_);
v___x_34_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_eQ___closed__0, &lp_tree_Formalism_BasicNotions_DV_eQ___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_eQ___closed__0);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v_b_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_apply_1(v_hc_26_, v_00_u03c4_23_);
v_b_36_ = lean_ctor_get(v___x_35_, 2);
lean_inc_ref(v_b_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lean_apply_1(v_b_36_, v___x_32_);
v___x_38_ = l_Rat_neg(v___x_37_);
return v___x_38_;
}
}
else
{
lean_object* v___x_39_; lean_object* v_v_40_; lean_object* v___x_41_; 
lean_dec(v___x_30_);
lean_dec(v_m_28_);
v___x_39_ = lean_apply_1(v_hc_26_, v_00_u03c4_23_);
v_v_40_ = lean_ctor_get(v___x_39_, 1);
lean_inc_ref(v_v_40_);
lean_dec_ref(v___x_39_);
v___x_41_ = lean_apply_1(v_v_40_, v_i_24_);
return v___x_41_;
}
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aPlusQ(lean_object* v_D_46_, lean_object* v_j_47_, lean_object* v_00_u03c4_48_, lean_object* v_i_49_){
_start:
{
lean_object* v_R_50_; lean_object* v___x_51_; lean_object* v_k_52_; lean_object* v_m_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_R_50_ = lean_ctor_get(v_D_46_, 0);
lean_inc_ref(v_R_50_);
lean_inc(v_i_49_);
lean_inc(v_00_u03c4_48_);
lean_inc_ref(v_D_46_);
v___x_51_ = lp_tree_Formalism_BasicNotions_DV_sigPar(v_D_46_, v_00_u03c4_48_, v_i_49_);
v_k_52_ = lean_ctor_get(v_R_50_, 1);
lean_inc(v_k_52_);
v_m_53_ = lean_ctor_get(v_R_50_, 2);
lean_inc(v_m_53_);
v___x_54_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0, &lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0);
v___x_55_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_49_);
v___x_56_ = l_Rat_mul(v___x_54_, v___x_55_);
v___x_57_ = lp_tree_Formalism_BasicNotions_DV_eQ(v_D_46_, v_j_47_, v_00_u03c4_48_);
v___x_58_ = l_Rat_add(v___x_51_, v___x_57_);
v___x_59_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_50_);
lean_dec_ref(v_R_50_);
v___x_60_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_59_);
v___x_61_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1, &lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1_once, _init_lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1);
v___x_62_ = l_Rat_sub(v___x_60_, v___x_61_);
v___x_63_ = l_Rat_sub(v___x_62_, v___x_56_);
v___x_64_ = l_Rat_div(v___x_63_, v___x_54_);
lean_dec_ref(v___x_63_);
v___x_65_ = l_Rat_sub(v___x_58_, v___x_64_);
v___x_66_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_k_52_);
v___x_67_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_j_47_);
lean_inc_ref(v___x_67_);
v___x_68_ = l_Rat_add(v___x_66_, v___x_67_);
v___x_69_ = l_Rat_sub(v___x_68_, v___x_61_);
v___x_70_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_m_53_);
v___x_71_ = l_Rat_sub(v___x_70_, v___x_67_);
v___x_72_ = l_Rat_sub(v___x_69_, v___x_71_);
v___x_73_ = l_Rat_div(v___x_72_, v___x_54_);
lean_dec_ref(v___x_72_);
v___x_74_ = l_Rat_sub(v___x_65_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinusQ(lean_object* v_D_75_, lean_object* v_j_76_, lean_object* v_00_u03c4_77_, lean_object* v_c_78_){
_start:
{
lean_object* v_R_79_; lean_object* v_hc_80_; lean_object* v_m_81_; lean_object* v_t_82_; lean_object* v___y_84_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_R_79_ = lean_ctor_get(v_D_75_, 0);
v_hc_80_ = lean_ctor_get(v_D_75_, 6);
v_m_81_ = lean_ctor_get(v_R_79_, 2);
v_t_82_ = lean_ctor_get(v_R_79_, 3);
lean_inc(v_t_82_);
v___x_96_ = lean_nat_add(v_j_76_, v_c_78_);
v___x_97_ = lean_nat_dec_lt(v___x_96_, v_m_81_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v___x_96_);
v___x_98_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_eQ___closed__0, &lp_tree_Formalism_BasicNotions_DV_eQ___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_eQ___closed__0);
v___y_84_ = v___x_98_;
goto v___jp_83_;
}
else
{
lean_object* v___x_99_; lean_object* v_b_100_; lean_object* v___x_101_; 
lean_inc_ref(v_hc_80_);
lean_inc(v_00_u03c4_77_);
v___x_99_ = lean_apply_1(v_hc_80_, v_00_u03c4_77_);
v_b_100_ = lean_ctor_get(v___x_99_, 2);
lean_inc_ref(v_b_100_);
lean_dec_ref(v___x_99_);
v___x_101_ = lean_apply_1(v_b_100_, v___x_96_);
v___y_84_ = v___x_101_;
goto v___jp_83_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_85_ = lp_tree_Formalism_BasicNotions_DV_eQ(v_D_75_, v_j_76_, v_00_u03c4_77_);
v___x_86_ = l_Rat_sub(v___y_84_, v___x_85_);
v___x_87_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_82_);
v___x_88_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1, &lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1_once, _init_lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__1);
v___x_89_ = l_Rat_add(v___x_87_, v___x_88_);
v___x_90_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0, &lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_aPlusQ___closed__0);
v___x_91_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_c_78_);
v___x_92_ = l_Rat_mul(v___x_90_, v___x_91_);
v___x_93_ = l_Rat_add(v___x_89_, v___x_92_);
v___x_94_ = l_Rat_div(v___x_93_, v___x_90_);
lean_dec_ref(v___x_93_);
v___x_95_ = l_Rat_sub(v___x_86_, v___x_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinusQ___boxed(lean_object* v_D_102_, lean_object* v_j_103_, lean_object* v_00_u03c4_104_, lean_object* v_c_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_Formalism_BasicNotions_DV_aMinusQ(v_D_102_, v_j_103_, v_00_u03c4_104_, v_c_105_);
lean_dec(v_j_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aPlus(lean_object* v_D_107_, lean_object* v_j_108_, lean_object* v_00_u03c4_109_, lean_object* v_i_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = lp_tree_Formalism_BasicNotions_DV_aPlusQ(v_D_107_, v_j_108_, v_00_u03c4_109_, v_i_110_);
v___f_112_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinus(lean_object* v_D_113_, lean_object* v_j_114_, lean_object* v_00_u03c4_115_, lean_object* v_c_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___f_118_; 
v___x_117_ = lp_tree_Formalism_BasicNotions_DV_aMinusQ(v_D_113_, v_j_114_, v_00_u03c4_115_, v_c_116_);
v___f_118_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_118_, 0, v___x_117_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_aMinus___boxed(lean_object* v_D_119_, lean_object* v_j_120_, lean_object* v_00_u03c4_121_, lean_object* v_c_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lp_tree_Formalism_BasicNotions_DV_aMinus(v_D_119_, v_j_120_, v_00_u03c4_121_, v_c_122_);
lean_dec(v_j_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_lamProd___lam__0(lean_object* v_what_u2082_124_, lean_object* v_ty_125_, lean_object* v_00_u03c3_126_, lean_object* v_j_127_){
_start:
{
lean_object* v_mu0_128_; lean_object* v_lamP_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_mu0_128_ = lean_ctor_get(v_what_u2082_124_, 6);
lean_inc(v_mu0_128_);
v_lamP_129_ = lean_ctor_get(v_what_u2082_124_, 55);
lean_inc(v_lamP_129_);
lean_dec_ref(v_what_u2082_124_);
v___x_130_ = lean_apply_1(v_ty_125_, v_00_u03c3_126_);
v___x_131_ = lean_apply_3(v_lamP_129_, v_mu0_128_, v_j_127_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_lamProd___lam__1(lean_object* v_D_132_, lean_object* v_ty_133_, lean_object* v_00_u03c3_134_){
_start:
{
lean_object* v_R_135_; lean_object* v_what_u2082_136_; lean_object* v_m_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_R_135_ = lean_ctor_get(v_D_132_, 0);
lean_inc_ref(v_R_135_);
v_what_u2082_136_ = lean_ctor_get(v_D_132_, 4);
lean_inc_ref(v_what_u2082_136_);
lean_dec_ref(v_D_132_);
v_m_137_ = lean_ctor_get(v_R_135_, 2);
lean_inc(v_m_137_);
lean_dec_ref(v_R_135_);
v___f_138_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_DV_lamProd___lam__0), 4, 3);
lean_closure_set(v___f_138_, 0, v_what_u2082_136_);
lean_closure_set(v___f_138_, 1, v_ty_133_);
lean_closure_set(v___f_138_, 2, v_00_u03c3_134_);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_139_, v_m_137_);
lean_dec(v_m_137_);
v___x_141_ = lp_tree_Finset_prod___at___00Formalism_G0_esymmR_spec__0___redArg(v___x_140_, v___f_138_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_lamProd(lean_object* v_D_142_, lean_object* v_n_143_, lean_object* v_ty_144_){
_start:
{
lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___f_145_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_DV_lamProd___lam__1), 3, 2);
lean_closure_set(v___f_145_, 0, v_D_142_);
lean_closure_set(v___f_145_, 1, v_ty_144_);
v___x_146_ = l_List_finRange(v_n_143_);
v___x_147_ = lp_tree_Finset_prod___at___00Formalism_G0_esymmR_spec__0___redArg(v___x_146_, v___f_145_);
return v___x_147_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
