// Lean compiler output
// Module: Lib.DiscreteSeries.FlenstedJensen.Defs
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Haar.CayleyChart
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
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Prop_decidableRelTop___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Subtype_fintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_twoRho___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoRho___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_twoRho___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoRho___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoRho___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoRho(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_paramAddRho___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Prop_decidableRelTop___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_paramAddRho___redArg___closed__0 = (const lean_object*)&lp_GRH_New_paramAddRho___redArg___closed__0_value;
static lean_once_cell_t lp_GRH_New_paramAddRho___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_paramAddRho___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_paramAddRho___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_paramAddRho(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_toHCParam___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_toHCParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_toHCParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_compactForm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_compactForm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_compactForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_HCParam_lowestKType___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowestKType___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowestKType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowestKType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__1;
static lean_once_cell_t lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__2;
LEAN_EXPORT uint8_t lp_GRH_New_Exchange_negCount___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_negCount___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_negCount___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_negCount(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_unitaryLie___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie(lean_object* v_n_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_J_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLie___boxed(lean_object* v_n_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_J_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_unitaryLie(v_n_10_, v_inst_11_, v_inst_12_, v_J_13_);
lean_dec_ref(v_J_13_);
lean_dec_ref(v_inst_12_);
lean_dec(v_inst_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold___redArg(lean_object* v_inst_15_, lean_object* v_A_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = lean_unsigned_to_nat(500u);
v___x_18_ = l_List_lengthTR___redArg(v_inst_15_);
v___x_19_ = lean_unsigned_to_nat(3u);
v___x_20_ = lean_nat_pow(v___x_18_, v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_nat_mul(v___x_17_, v___x_20_);
lean_dec(v___x_20_);
v___x_22_ = lean_nat_add(v___x_21_, v_A_16_);
lean_dec(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold___redArg___boxed(lean_object* v_inst_23_, lean_object* v_A_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_gapThreshold___redArg(v_inst_23_, v_A_24_);
lean_dec(v_A_24_);
lean_dec(v_inst_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold(lean_object* v_n_26_, lean_object* v_inst_27_, lean_object* v_A_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_29_ = lean_unsigned_to_nat(500u);
v___x_30_ = l_List_lengthTR___redArg(v_inst_27_);
v___x_31_ = lean_unsigned_to_nat(3u);
v___x_32_ = lean_nat_pow(v___x_30_, v___x_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_nat_mul(v___x_29_, v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = lean_nat_add(v___x_33_, v_A_28_);
lean_dec(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gapThreshold___boxed(lean_object* v_n_35_, lean_object* v_inst_36_, lean_object* v_A_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_gapThreshold(v_n_35_, v_inst_36_, v_A_37_);
lean_dec(v_A_37_);
lean_dec(v_inst_36_);
return v_res_38_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_twoRho___redArg___lam__0(lean_object* v_inst_39_, lean_object* v_i_40_, lean_object* v_l_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
lean_inc(v_a_42_);
lean_inc(v_i_40_);
v___x_43_ = lean_apply_2(v_inst_39_, v_i_40_, v_a_42_);
v___x_44_ = lean_unbox(v___x_43_);
if (v___x_44_ == 0)
{
uint8_t v___x_45_; 
lean_dec(v_a_42_);
lean_dec_ref(v_l_41_);
lean_dec(v_i_40_);
v___x_45_ = lean_unbox(v___x_43_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
lean_inc_ref(v_l_41_);
v___x_46_ = lean_apply_1(v_l_41_, v_a_42_);
v___x_47_ = lean_apply_1(v_l_41_, v_i_40_);
v___x_48_ = lean_int_dec_lt(v___x_46_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_46_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoRho___redArg___lam__0___boxed(lean_object* v_inst_49_, lean_object* v_i_50_, lean_object* v_l_51_, lean_object* v_a_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = lp_GRH_New_twoRho___redArg___lam__0(v_inst_49_, v_i_50_, v_l_51_, v_a_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_twoRho___redArg___lam__1(lean_object* v_inst_55_, lean_object* v_i_56_, lean_object* v_l_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
lean_inc(v_a_58_);
lean_inc(v_i_56_);
v___x_59_ = lean_apply_2(v_inst_55_, v_i_56_, v_a_58_);
v___x_60_ = lean_unbox(v___x_59_);
if (v___x_60_ == 0)
{
uint8_t v___x_61_; 
lean_dec(v_a_58_);
lean_dec_ref(v_l_57_);
lean_dec(v_i_56_);
v___x_61_ = lean_unbox(v___x_59_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
lean_inc_ref(v_l_57_);
v___x_62_ = lean_apply_1(v_l_57_, v_i_56_);
v___x_63_ = lean_apply_1(v_l_57_, v_a_58_);
v___x_64_ = lean_int_dec_lt(v___x_62_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_62_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoRho___redArg___lam__1___boxed(lean_object* v_inst_65_, lean_object* v_i_66_, lean_object* v_l_67_, lean_object* v_a_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = lp_GRH_New_twoRho___redArg___lam__1(v_inst_65_, v_i_66_, v_l_67_, v_a_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoRho___redArg(lean_object* v_inst_71_, lean_object* v_l_72_, lean_object* v_inst_73_, lean_object* v_i_74_){
_start:
{
lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc_ref(v_l_72_);
lean_inc(v_i_74_);
lean_inc_ref(v_inst_73_);
v___f_75_ = lean_alloc_closure((void*)(lp_GRH_New_twoRho___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_75_, 0, v_inst_73_);
lean_closure_set(v___f_75_, 1, v_i_74_);
lean_closure_set(v___f_75_, 2, v_l_72_);
v___f_76_ = lean_alloc_closure((void*)(lp_GRH_New_twoRho___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_76_, 0, v_inst_73_);
lean_closure_set(v___f_76_, 1, v_i_74_);
lean_closure_set(v___f_76_, 2, v_l_72_);
lean_inc(v_inst_71_);
v___x_77_ = lp_mathlib_Multiset_filter___redArg(v___f_75_, v_inst_71_);
v___x_78_ = l_List_lengthTR___redArg(v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_nat_to_int(v___x_78_);
v___x_80_ = lp_mathlib_Multiset_filter___redArg(v___f_76_, v_inst_71_);
v___x_81_ = l_List_lengthTR___redArg(v___x_80_);
lean_dec(v___x_80_);
v___x_82_ = lean_nat_to_int(v___x_81_);
v___x_83_ = lean_int_sub(v___x_79_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_79_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoRho(lean_object* v_n_84_, lean_object* v_inst_85_, lean_object* v_l_86_, lean_object* v_r_87_, lean_object* v_inst_88_, lean_object* v_i_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lp_GRH_New_twoRho___redArg(v_inst_85_, v_l_86_, v_inst_88_, v_i_89_);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_New_paramAddRho___redArg___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(2u);
v___x_93_ = lean_nat_to_int(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_paramAddRho___redArg(lean_object* v_inst_94_, lean_object* v_l_95_, lean_object* v_i_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc_ref(v_l_95_);
lean_inc(v_i_96_);
v___x_97_ = lean_apply_1(v_l_95_, v_i_96_);
v___x_98_ = ((lean_object*)(lp_GRH_New_paramAddRho___redArg___closed__0));
v___x_99_ = lp_GRH_New_twoRho___redArg(v_inst_94_, v_l_95_, v___x_98_, v_i_96_);
v___x_100_ = lean_int_add(v___x_97_, v___x_99_);
lean_dec(v___x_99_);
lean_dec(v___x_97_);
v___x_101_ = lean_obj_once(&lp_GRH_New_paramAddRho___redArg___closed__1, &lp_GRH_New_paramAddRho___redArg___closed__1_once, _init_lp_GRH_New_paramAddRho___redArg___closed__1);
v___x_102_ = lean_int_ediv(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_paramAddRho(lean_object* v_n_103_, lean_object* v_inst_104_, lean_object* v_l_105_, lean_object* v_i_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lp_GRH_New_paramAddRho___redArg(v_inst_104_, v_l_105_, v_i_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU___redArg(){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU___redArg___boxed(lean_object* v___dummy_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_GRH_New_maxCompactU___redArg();
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU(lean_object* v_n_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_00_u03b5_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_maxCompactU___boxed(lean_object* v_n_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_00_u03b5_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_GRH_New_maxCompactU(v_n_117_, v_inst_118_, v_inst_119_, v_00_u03b5_120_);
lean_dec_ref(v_00_u03b5_120_);
lean_dec_ref(v_inst_119_);
lean_dec(v_inst_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toHCParam___redArg(lean_object* v_l_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_1(v_l_122_, v_a_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toHCParam(lean_object* v_n_125_, lean_object* v_00_u03b5_126_, lean_object* v_l_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_apply_1(v_l_127_, v_a_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_toHCParam___boxed(lean_object* v_n_130_, lean_object* v_00_u03b5_131_, lean_object* v_l_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_GRH_New_toHCParam(v_n_130_, v_00_u03b5_131_, v_l_132_, v_a_133_);
lean_dec_ref(v_00_u03b5_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_compactForm___redArg(lean_object* v_l_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_apply_1(v_l_135_, v_a_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_compactForm(lean_object* v_n_138_, lean_object* v_00_u03b5_139_, lean_object* v_l_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_1(v_l_140_, v_a_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_compactForm___boxed(lean_object* v_n_143_, lean_object* v_00_u03b5_144_, lean_object* v_l_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_GRH_New_HCParam_compactForm(v_n_143_, v_00_u03b5_144_, v_l_145_, v_a_146_);
lean_dec_ref(v_00_u03b5_144_);
return v_res_147_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_HCParam_lowestKType___redArg___lam__0(lean_object* v_00_u03b5_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_151_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
lean_inc_ref(v_00_u03b5_148_);
v___x_152_ = lean_apply_1(v_00_u03b5_148_, v_a_149_);
v___x_153_ = lean_apply_1(v_00_u03b5_148_, v_b_150_);
v___x_154_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_151_, v___x_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowestKType___redArg___lam__0___boxed(lean_object* v_00_u03b5_155_, lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = lp_GRH_New_HCParam_lowestKType___redArg___lam__0(v_00_u03b5_155_, v_a_156_, v_b_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowestKType___redArg(lean_object* v_inst_160_, lean_object* v_00_u03b5_161_, lean_object* v_l_162_, lean_object* v_i_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___f_164_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_lowestKType___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_164_, 0, v_00_u03b5_161_);
lean_inc(v_i_163_);
lean_inc_ref(v_l_162_);
lean_inc(v_inst_160_);
v___x_165_ = lp_GRH_New_paramAddRho___redArg(v_inst_160_, v_l_162_, v_i_163_);
v___x_166_ = lp_GRH_New_twoRho___redArg(v_inst_160_, v_l_162_, v___f_164_, v_i_163_);
v___x_167_ = lean_int_sub(v___x_165_, v___x_166_);
lean_dec(v___x_166_);
lean_dec(v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowestKType(lean_object* v_n_168_, lean_object* v_inst_169_, lean_object* v_00_u03b5_170_, lean_object* v_l_171_, lean_object* v_i_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lp_GRH_New_HCParam_lowestKType___redArg(v_inst_169_, v_00_u03b5_170_, v_l_171_, v_i_172_);
return v___x_173_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_obj_once(&lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__0, &lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__0);
v___x_177_ = lean_int_neg(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__1, &lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__1);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Exchange_negCount___redArg___lam__0(lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_183_ = lean_apply_1(v_a_180_, v_a_181_);
v___x_184_ = lean_obj_once(&lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__2, &lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__2_once, _init_lp_GRH_New_Exchange_negCount___redArg___lam__0___closed__2);
v___x_185_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_182_, v___x_183_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_negCount___redArg___lam__0___boxed(lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = lp_GRH_New_Exchange_negCount___redArg___lam__0(v_a_186_, v_a_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_negCount___redArg(lean_object* v_inst_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_192_ = lean_alloc_closure((void*)(lp_GRH_New_Exchange_negCount___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_192_, 0, v_a_191_);
v___x_193_ = lp_mathlib_Subtype_fintype___redArg(v___f_192_, v_inst_190_);
v___x_194_ = l_List_lengthTR___redArg(v___x_193_);
lean_dec(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_negCount(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lp_GRH_New_Exchange_negCount___redArg(v_inst_196_, v_a_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg___redArg(){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg___redArg___boxed(lean_object* v___dummy_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lp_GRH_New_blockDiagAlg___redArg();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg(lean_object* v_n_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_00_u03b5_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagAlg___boxed(lean_object* v_n_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_00_u03b5_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = lp_GRH_New_blockDiagAlg(v_n_208_, v_inst_209_, v_inst_210_, v_00_u03b5_211_);
lean_dec_ref(v_00_u03b5_211_);
lean_dec_ref(v_inst_210_);
lean_dec(v_inst_209_);
return v_res_212_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Haar_CayleyChart(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_Defs(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Haar_CayleyChart(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
