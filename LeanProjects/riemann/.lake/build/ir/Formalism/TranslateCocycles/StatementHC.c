// Lean compiler output
// Module: Formalism.TranslateCocycles.StatementHC
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCrank(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCrank___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_CG_HCparam___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_CG_HCparam___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCparam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCparam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_CG_HCnu___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_CG_HCnu___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCnu(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCnu___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HClam0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCwG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCdeg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCdeg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCdeg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCblockSum___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCblockSum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCsparam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCsparam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCkap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDplus___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDplus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDminus___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDminus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCrank(lean_object* v_k_1_, lean_object* v_t_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_t_2_, v___x_4_);
v___x_6_ = lean_nat_mul(v_j_3_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_nat_add(v_k_1_, v___x_6_);
lean_dec(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCrank___boxed(lean_object* v_k_8_, lean_object* v_t_9_, lean_object* v_j_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_CG_HCrank(v_k_8_, v_t_9_, v_j_10_);
lean_dec(v_j_10_);
lean_dec(v_t_9_);
lean_dec(v_k_8_);
return v_res_11_;
}
}
static lean_object* _init_lp_tree_Formalism_CG_HCparam___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCparam(lean_object* v_k_14_, lean_object* v_t_15_, lean_object* v_u_16_, lean_object* v_e_17_, lean_object* v_l_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_le(v_l_18_, v_k_14_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec_ref(v_u_16_);
v___x_20_ = lean_nat_sub(v_l_18_, v_k_14_);
lean_dec(v_l_18_);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_sub(v___x_20_, v___x_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_nat_add(v_t_15_, v___x_21_);
v___x_24_ = lean_nat_div(v___x_22_, v___x_23_);
v___x_25_ = lean_nat_add(v___x_24_, v___x_21_);
lean_dec(v___x_24_);
v___x_26_ = lean_apply_1(v_e_17_, v___x_25_);
v___x_27_ = l_Rat_neg(v___x_26_);
v___x_28_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_15_);
v___x_29_ = lean_obj_once(&lp_tree_Formalism_CG_HCparam___closed__0, &lp_tree_Formalism_CG_HCparam___closed__0_once, _init_lp_tree_Formalism_CG_HCparam___closed__0);
v___x_30_ = l_Rat_div(v___x_28_, v___x_29_);
lean_dec_ref(v___x_28_);
v___x_31_ = l_Rat_add(v___x_27_, v___x_30_);
v___x_32_ = lean_nat_mod(v___x_22_, v___x_23_);
lean_dec(v___x_23_);
lean_dec(v___x_22_);
v___x_33_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_32_);
v___x_34_ = l_Rat_sub(v___x_31_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
lean_dec_ref(v_e_17_);
lean_dec(v_t_15_);
v___x_35_ = lean_apply_1(v_u_16_, v_l_18_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCparam___boxed(lean_object* v_k_36_, lean_object* v_t_37_, lean_object* v_u_38_, lean_object* v_e_39_, lean_object* v_l_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_CG_HCparam(v_k_36_, v_t_37_, v_u_38_, v_e_39_, v_l_40_);
lean_dec(v_k_36_);
return v_res_41_;
}
}
static lean_object* _init_lp_tree_Formalism_CG_HCnu___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCnu(lean_object* v_k_44_, lean_object* v_t_45_, lean_object* v_u_46_, lean_object* v_e_47_, lean_object* v_j_48_, lean_object* v_l_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_inc(v_l_49_);
lean_inc_ref(v_e_47_);
lean_inc(v_t_45_);
v___x_50_ = lp_tree_Formalism_CG_HCparam(v_k_44_, v_t_45_, v_u_46_, v_e_47_, v_l_49_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_sub(v_j_48_, v___x_51_);
v___x_53_ = lp_tree_Formalism_CG_HCrank(v_k_44_, v_t_45_, v___x_52_);
lean_dec(v___x_52_);
v___x_54_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_53_);
v___x_55_ = lean_obj_once(&lp_tree_Formalism_CG_HCnu___closed__0, &lp_tree_Formalism_CG_HCnu___closed__0_once, _init_lp_tree_Formalism_CG_HCnu___closed__0);
v___x_56_ = l_Rat_add(v___x_54_, v___x_55_);
v___x_57_ = lean_obj_once(&lp_tree_Formalism_CG_HCparam___closed__0, &lp_tree_Formalism_CG_HCparam___closed__0_once, _init_lp_tree_Formalism_CG_HCparam___closed__0);
v___x_58_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_l_49_);
v___x_59_ = l_Rat_mul(v___x_57_, v___x_58_);
v___x_60_ = l_Rat_sub(v___x_56_, v___x_59_);
v___x_61_ = l_Rat_div(v___x_60_, v___x_57_);
lean_dec_ref(v___x_60_);
v___x_62_ = l_Rat_sub(v___x_50_, v___x_61_);
lean_inc(v_j_48_);
v___x_63_ = lean_apply_1(v_e_47_, v_j_48_);
v___x_64_ = l_Rat_add(v___x_62_, v___x_63_);
v___x_65_ = lp_tree_Formalism_CG_HCrank(v_k_44_, v_t_45_, v_j_48_);
lean_dec(v_j_48_);
lean_dec(v_t_45_);
v___x_66_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_65_);
v___x_67_ = l_Rat_div(v___x_66_, v___x_57_);
lean_dec_ref(v___x_66_);
v___x_68_ = l_Rat_sub(v___x_64_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCnu___boxed(lean_object* v_k_69_, lean_object* v_t_70_, lean_object* v_u_71_, lean_object* v_e_72_, lean_object* v_j_73_, lean_object* v_l_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_tree_Formalism_CG_HCnu(v_k_69_, v_t_70_, v_u_71_, v_e_72_, v_j_73_, v_l_74_);
lean_dec(v_k_69_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HClam0(lean_object* v_k_76_, lean_object* v_u_77_, lean_object* v_i_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_inc(v_i_78_);
v___x_79_ = lean_apply_1(v_u_77_, v_i_78_);
v___x_80_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_k_76_);
v___x_81_ = lean_obj_once(&lp_tree_Formalism_CG_HCnu___closed__0, &lp_tree_Formalism_CG_HCnu___closed__0_once, _init_lp_tree_Formalism_CG_HCnu___closed__0);
v___x_82_ = l_Rat_add(v___x_80_, v___x_81_);
v___x_83_ = lean_obj_once(&lp_tree_Formalism_CG_HCparam___closed__0, &lp_tree_Formalism_CG_HCparam___closed__0_once, _init_lp_tree_Formalism_CG_HCparam___closed__0);
v___x_84_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_78_);
v___x_85_ = l_Rat_mul(v___x_83_, v___x_84_);
v___x_86_ = l_Rat_sub(v___x_82_, v___x_85_);
v___x_87_ = l_Rat_div(v___x_86_, v___x_83_);
lean_dec_ref(v___x_86_);
v___x_88_ = l_Rat_sub(v___x_79_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCwG(lean_object* v_k_89_, lean_object* v_t_90_, lean_object* v_e_91_, lean_object* v_j_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
lean_inc(v_j_92_);
v___x_93_ = lean_apply_1(v_e_91_, v_j_92_);
v___x_94_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_k_89_);
v___x_95_ = lean_obj_once(&lp_tree_Formalism_CG_HCparam___closed__0, &lp_tree_Formalism_CG_HCparam___closed__0_once, _init_lp_tree_Formalism_CG_HCparam___closed__0);
v___x_96_ = l_Rat_div(v___x_94_, v___x_95_);
lean_dec_ref(v___x_94_);
v___x_97_ = l_Rat_sub(v___x_93_, v___x_96_);
v___x_98_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_j_92_);
v___x_99_ = l_Rat_mul(v___x_95_, v___x_98_);
v___x_100_ = lean_obj_once(&lp_tree_Formalism_CG_HCnu___closed__0, &lp_tree_Formalism_CG_HCnu___closed__0_once, _init_lp_tree_Formalism_CG_HCnu___closed__0);
v___x_101_ = l_Rat_sub(v___x_99_, v___x_100_);
v___x_102_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_90_);
v___x_103_ = l_Rat_add(v___x_102_, v___x_100_);
v___x_104_ = l_Rat_mul(v___x_101_, v___x_103_);
lean_dec_ref(v___x_101_);
v___x_105_ = l_Rat_div(v___x_104_, v___x_95_);
lean_dec_ref(v___x_104_);
v___x_106_ = l_Rat_sub(v___x_97_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCdeg___lam__0(lean_object* v_k_107_, lean_object* v_t_108_, lean_object* v_u_109_, lean_object* v_e_110_, lean_object* v_j_111_, lean_object* v_l_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lp_tree_Formalism_CG_HCnu(v_k_107_, v_t_108_, v_u_109_, v_e_110_, v_j_111_, v_l_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCdeg___lam__0___boxed(lean_object* v_k_114_, lean_object* v_t_115_, lean_object* v_u_116_, lean_object* v_e_117_, lean_object* v_j_118_, lean_object* v_l_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_tree_Formalism_CG_HCdeg___lam__0(v_k_114_, v_t_115_, v_u_116_, v_e_117_, v_j_118_, v_l_119_);
lean_dec(v_k_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCdeg(lean_object* v_k_121_, lean_object* v_t_122_, lean_object* v_u_123_, lean_object* v_e_124_, lean_object* v_j_125_){
_start:
{
lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_inc(v_j_125_);
lean_inc(v_t_122_);
lean_inc(v_k_121_);
v___f_126_ = lean_alloc_closure((void*)(lp_tree_Formalism_CG_HCdeg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_126_, 0, v_k_121_);
lean_closure_set(v___f_126_, 1, v_t_122_);
lean_closure_set(v___f_126_, 2, v_u_123_);
lean_closure_set(v___f_126_, 3, v_e_124_);
lean_closure_set(v___f_126_, 4, v_j_125_);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_sub(v_j_125_, v___x_127_);
lean_dec(v_j_125_);
v___x_129_ = lp_tree_Formalism_CG_HCrank(v_k_121_, v_t_122_, v___x_128_);
lean_dec(v___x_128_);
lean_dec(v_t_122_);
lean_dec(v_k_121_);
v___x_130_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_127_, v___x_129_);
lean_dec(v___x_129_);
v___x_131_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_130_, v___f_126_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCblockSum___lam__0(lean_object* v_e_132_, lean_object* v_j_133_, lean_object* v___x_134_, lean_object* v_i_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_inc_ref(v_e_132_);
lean_inc(v_j_133_);
v___x_136_ = lean_apply_1(v_e_132_, v_j_133_);
lean_inc(v_i_135_);
v___x_137_ = lean_apply_1(v_e_132_, v_i_135_);
v___x_138_ = l_Rat_sub(v___x_136_, v___x_137_);
v___x_139_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_j_133_);
v___x_140_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_i_135_);
v___x_141_ = l_Rat_sub(v___x_139_, v___x_140_);
v___x_142_ = l_Rat_mul(v___x_141_, v___x_134_);
lean_dec_ref(v___x_141_);
v___x_143_ = l_Rat_sub(v___x_138_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCblockSum(lean_object* v_t_144_, lean_object* v_e_145_, lean_object* v_j_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___f_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_147_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_144_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_obj_once(&lp_tree_Formalism_CG_HCnu___closed__0, &lp_tree_Formalism_CG_HCnu___closed__0_once, _init_lp_tree_Formalism_CG_HCnu___closed__0);
v___x_150_ = l_Rat_add(v___x_147_, v___x_149_);
lean_inc_ref(v___x_150_);
lean_inc(v_j_146_);
v___f_151_ = lean_alloc_closure((void*)(lp_tree_Formalism_CG_HCblockSum___lam__0), 4, 3);
lean_closure_set(v___f_151_, 0, v_e_145_);
lean_closure_set(v___f_151_, 1, v_j_146_);
lean_closure_set(v___f_151_, 2, v___x_150_);
v___x_152_ = lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(v___x_148_, v_j_146_);
lean_dec(v_j_146_);
v___x_153_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_152_, v___f_151_);
v___x_154_ = l_Rat_mul(v___x_150_, v___x_153_);
lean_dec_ref(v___x_150_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCsparam(lean_object* v_k_155_, lean_object* v_t_156_, lean_object* v_j_157_, lean_object* v_v_158_, lean_object* v_b_159_, lean_object* v_e_160_, lean_object* v_l_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_l_161_, v___x_162_);
v___x_164_ = lean_nat_dec_le(v___x_163_, v_k_155_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
lean_dec_ref(v_v_158_);
v___x_165_ = lean_nat_add(v_k_155_, v_j_157_);
v___x_166_ = lean_nat_dec_le(v___x_163_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_nat_add(v___x_165_, v_t_156_);
v___x_168_ = lean_nat_dec_le(v___x_163_, v___x_167_);
lean_dec(v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v___x_165_);
lean_dec_ref(v_e_160_);
lean_dec(v_j_157_);
v___x_169_ = lean_nat_sub(v___x_163_, v_k_155_);
lean_dec(v___x_163_);
v___x_170_ = lean_nat_sub(v___x_169_, v_t_156_);
lean_dec(v_t_156_);
lean_dec(v___x_169_);
v___x_171_ = lean_apply_1(v_b_159_, v___x_170_);
v___x_172_ = l_Rat_neg(v___x_171_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec_ref(v_b_159_);
v___x_173_ = lean_apply_1(v_e_160_, v_j_157_);
v___x_174_ = l_Rat_neg(v___x_173_);
v___x_175_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_156_);
v___x_176_ = lean_obj_once(&lp_tree_Formalism_CG_HCnu___closed__0, &lp_tree_Formalism_CG_HCnu___closed__0_once, _init_lp_tree_Formalism_CG_HCnu___closed__0);
v___x_177_ = l_Rat_sub(v___x_175_, v___x_176_);
v___x_178_ = lean_obj_once(&lp_tree_Formalism_CG_HCparam___closed__0, &lp_tree_Formalism_CG_HCparam___closed__0_once, _init_lp_tree_Formalism_CG_HCparam___closed__0);
v___x_179_ = l_Rat_div(v___x_177_, v___x_178_);
lean_dec_ref(v___x_177_);
v___x_180_ = l_Rat_add(v___x_174_, v___x_179_);
v___x_181_ = lean_nat_sub(v___x_163_, v___x_165_);
lean_dec(v___x_165_);
lean_dec(v___x_163_);
v___x_182_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_181_);
v___x_183_ = l_Rat_sub(v___x_182_, v___x_176_);
v___x_184_ = l_Rat_sub(v___x_180_, v___x_183_);
return v___x_184_;
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v___x_165_);
lean_dec_ref(v_e_160_);
lean_dec(v_j_157_);
lean_dec(v_t_156_);
v___x_185_ = lean_nat_sub(v___x_163_, v_k_155_);
lean_dec(v___x_163_);
v___x_186_ = lean_apply_1(v_b_159_, v___x_185_);
v___x_187_ = l_Rat_neg(v___x_186_);
return v___x_187_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref(v_e_160_);
lean_dec_ref(v_b_159_);
lean_dec(v_j_157_);
lean_dec(v_t_156_);
v___x_188_ = lean_apply_1(v_v_158_, v___x_163_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCsparam___boxed(lean_object* v_k_189_, lean_object* v_t_190_, lean_object* v_j_191_, lean_object* v_v_192_, lean_object* v_b_193_, lean_object* v_e_194_, lean_object* v_l_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = lp_tree_Formalism_CG_HCsparam(v_k_189_, v_t_190_, v_j_191_, v_v_192_, v_b_193_, v_e_194_, v_l_195_);
lean_dec(v_l_195_);
lean_dec(v_k_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCkap(lean_object* v_k_197_, lean_object* v_t_198_, lean_object* v_m_199_, lean_object* v_j_200_, lean_object* v_v_201_, lean_object* v_b_202_, lean_object* v_e_203_, lean_object* v_l_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_inc_ref(v_e_203_);
lean_inc_n(v_j_200_, 2);
lean_inc(v_t_198_);
v___x_205_ = lp_tree_Formalism_CG_HCsparam(v_k_197_, v_t_198_, v_j_200_, v_v_201_, v_b_202_, v_e_203_, v_l_204_);
v___x_206_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_k_197_);
v___x_207_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_m_199_);
lean_inc_ref(v___x_206_);
v___x_208_ = l_Rat_add(v___x_206_, v___x_207_);
v___x_209_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_198_);
lean_inc_ref(v___x_209_);
v___x_210_ = l_Rat_add(v___x_208_, v___x_209_);
v___x_211_ = lean_obj_once(&lp_tree_Formalism_CG_HCnu___closed__0, &lp_tree_Formalism_CG_HCnu___closed__0_once, _init_lp_tree_Formalism_CG_HCnu___closed__0);
v___x_212_ = l_Rat_sub(v___x_210_, v___x_211_);
lean_inc_ref(v___x_212_);
v___x_213_ = l_Rat_add(v___x_212_, v___x_211_);
v___x_214_ = lean_obj_once(&lp_tree_Formalism_CG_HCparam___closed__0, &lp_tree_Formalism_CG_HCparam___closed__0_once, _init_lp_tree_Formalism_CG_HCparam___closed__0);
v___x_215_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_l_204_);
v___x_216_ = l_Rat_mul(v___x_214_, v___x_215_);
v___x_217_ = l_Rat_sub(v___x_213_, v___x_216_);
v___x_218_ = l_Rat_div(v___x_217_, v___x_214_);
lean_dec_ref(v___x_217_);
v___x_219_ = l_Rat_sub(v___x_205_, v___x_218_);
v___x_220_ = lean_apply_1(v_e_203_, v_j_200_);
v___x_221_ = l_Rat_div(v___x_209_, v___x_214_);
lean_dec_ref(v___x_209_);
v___x_222_ = l_Rat_sub(v___x_220_, v___x_221_);
v___x_223_ = l_Rat_div(v___x_212_, v___x_214_);
lean_dec_ref(v___x_212_);
v___x_224_ = l_Rat_add(v___x_222_, v___x_223_);
v___x_225_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_j_200_);
v___x_226_ = l_Rat_add(v___x_206_, v___x_225_);
v___x_227_ = l_Rat_sub(v___x_226_, v___x_211_);
v___x_228_ = l_Rat_sub(v___x_224_, v___x_227_);
v___x_229_ = l_Rat_add(v___x_219_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDplus___lam__0(lean_object* v_k_230_, lean_object* v_t_231_, lean_object* v_m_232_, lean_object* v_j_233_, lean_object* v_v_234_, lean_object* v_b_235_, lean_object* v_e_236_, lean_object* v_l_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lp_tree_Formalism_CG_HCkap(v_k_230_, v_t_231_, v_m_232_, v_j_233_, v_v_234_, v_b_235_, v_e_236_, v_l_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDplus(lean_object* v_k_239_, lean_object* v_t_240_, lean_object* v_m_241_, lean_object* v_j_242_, lean_object* v_v_243_, lean_object* v_b_244_, lean_object* v_e_245_){
_start:
{
lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_inc(v_j_242_);
lean_inc(v_k_239_);
v___f_246_ = lean_alloc_closure((void*)(lp_tree_Formalism_CG_HCDplus___lam__0), 8, 7);
lean_closure_set(v___f_246_, 0, v_k_239_);
lean_closure_set(v___f_246_, 1, v_t_240_);
lean_closure_set(v___f_246_, 2, v_m_241_);
lean_closure_set(v___f_246_, 3, v_j_242_);
lean_closure_set(v___f_246_, 4, v_v_243_);
lean_closure_set(v___f_246_, 5, v_b_244_);
lean_closure_set(v___f_246_, 6, v_e_245_);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_add(v_k_239_, v_j_242_);
lean_dec(v_j_242_);
lean_dec(v_k_239_);
v___x_249_ = lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(v___x_247_, v___x_248_);
lean_dec(v___x_248_);
v___x_250_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_249_, v___f_246_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDminus___lam__0(lean_object* v_k_251_, lean_object* v_t_252_, lean_object* v_m_253_, lean_object* v_j_254_, lean_object* v_v_255_, lean_object* v_b_256_, lean_object* v_e_257_, lean_object* v_l_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lp_tree_Formalism_CG_HCkap(v_k_251_, v_t_252_, v_m_253_, v_j_254_, v_v_255_, v_b_256_, v_e_257_, v_l_258_);
v___x_260_ = l_Rat_neg(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CG_HCDminus(lean_object* v_k_261_, lean_object* v_t_262_, lean_object* v_m_263_, lean_object* v_j_264_, lean_object* v_v_265_, lean_object* v_b_266_, lean_object* v_e_267_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_inc(v_j_264_);
lean_inc(v_m_263_);
lean_inc(v_t_262_);
lean_inc(v_k_261_);
v___f_268_ = lean_alloc_closure((void*)(lp_tree_Formalism_CG_HCDminus___lam__0), 8, 7);
lean_closure_set(v___f_268_, 0, v_k_261_);
lean_closure_set(v___f_268_, 1, v_t_262_);
lean_closure_set(v___f_268_, 2, v_m_263_);
lean_closure_set(v___f_268_, 3, v_j_264_);
lean_closure_set(v___f_268_, 4, v_v_265_);
lean_closure_set(v___f_268_, 5, v_b_266_);
lean_closure_set(v___f_268_, 6, v_e_267_);
v___x_269_ = lean_nat_add(v_k_261_, v_j_264_);
lean_dec(v_j_264_);
v___x_270_ = lean_nat_add(v___x_269_, v_t_262_);
lean_dec(v___x_269_);
v___x_271_ = lean_nat_add(v_k_261_, v_m_263_);
lean_dec(v_m_263_);
lean_dec(v_k_261_);
v___x_272_ = lean_nat_add(v___x_271_, v_t_262_);
lean_dec(v_t_262_);
lean_dec(v___x_271_);
v___x_273_ = lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(v___x_270_, v___x_272_);
lean_dec(v___x_272_);
lean_dec(v___x_270_);
v___x_274_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_273_, v___f_268_);
return v___x_274_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_TranslateCocycles_StatementHC(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
