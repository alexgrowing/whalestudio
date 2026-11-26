// Lean compiler output
// Module: Lib.Weil.Periods.StringPowers
// Imports: public import Init public meta import Init public import Lib.Weil.Periods.PointLattice
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Grading_powerCoeff___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Grading_powerCoeff___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Grading_powerCoeff___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Grading_powerCoeff___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_powerCoeff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_powerCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_powerCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_middlePower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_middlePower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_middlePower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Grading_powerCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Grading_powerCoeff___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_powerCoeff___redArg(lean_object* v_inst_5_, lean_object* v_s_6_, lean_object* v_N_7_, lean_object* v_Y_8_, lean_object* v_i_9_){
_start:
{
lean_object* v___x_10_; lean_object* v_toCommSemiring_11_; lean_object* v___x_12_; lean_object* v_toMul_13_; lean_object* v___x_14_; lean_object* v_toRing_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_toNeg_18_; lean_object* v___x_19_; lean_object* v_toZPow_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_10_ = lp_mathlib_Field_toSemifield___redArg(v_inst_5_);
v_toCommSemiring_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_ref(v_toCommSemiring_11_);
lean_dec_ref(v___x_10_);
v___x_12_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_11_);
v_toMul_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_toMul_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_5_);
v_toRing_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toRing_15_);
v___x_16_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_15_);
lean_dec_ref(v_toRing_15_);
v___x_17_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_16_);
lean_dec_ref(v___x_16_);
v_toNeg_18_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_toNeg_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_14_);
lean_dec_ref(v___x_14_);
v_toZPow_20_ = lean_ctor_get(v___x_19_, 3);
lean_inc(v_toZPow_20_);
lean_dec_ref(v___x_19_);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_nat_mul(v___x_21_, v_i_9_);
v___x_23_ = lean_nat_dec_lt(v___x_22_, v_s_6_);
lean_dec(v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v_genericConst_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_genericConst_24_ = lean_ctor_get(v_Y_8_, 1);
lean_inc(v_genericConst_24_);
lean_dec_ref(v_Y_8_);
v___x_25_ = lean_apply_1(v_toNeg_18_, v_N_7_);
v___x_26_ = lean_nat_to_int(v_i_9_);
v___x_27_ = lean_nat_to_int(v_s_6_);
v___x_28_ = lean_obj_once(&lp_GRH_New_Grading_powerCoeff___redArg___closed__0, &lp_GRH_New_Grading_powerCoeff___redArg___closed__0_once, _init_lp_GRH_New_Grading_powerCoeff___redArg___closed__0);
v___x_29_ = lean_int_sub(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_obj_once(&lp_GRH_New_Grading_powerCoeff___redArg___closed__1, &lp_GRH_New_Grading_powerCoeff___redArg___closed__1_once, _init_lp_GRH_New_Grading_powerCoeff___redArg___closed__1);
v___x_31_ = lean_int_ediv(v___x_29_, v___x_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_int_sub(v___x_26_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_26_);
v___x_33_ = lean_apply_2(v_toZPow_20_, v___x_32_, v_genericConst_24_);
v___x_34_ = lean_apply_2(v_toMul_13_, v___x_25_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_genericConst_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_toNeg_18_);
lean_dec(v_toMul_13_);
lean_dec(v_N_7_);
v_genericConst_35_ = lean_ctor_get(v_Y_8_, 1);
lean_inc(v_genericConst_35_);
lean_dec_ref(v_Y_8_);
v___x_36_ = lean_nat_to_int(v_i_9_);
v___x_37_ = lean_nat_to_int(v_s_6_);
v___x_38_ = lean_obj_once(&lp_GRH_New_Grading_powerCoeff___redArg___closed__1, &lp_GRH_New_Grading_powerCoeff___redArg___closed__1_once, _init_lp_GRH_New_Grading_powerCoeff___redArg___closed__1);
v___x_39_ = lean_int_ediv(v___x_37_, v___x_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_int_sub(v___x_36_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v___x_36_);
v___x_41_ = lean_apply_2(v_toZPow_20_, v___x_40_, v_genericConst_35_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_powerCoeff(lean_object* v_E_42_, lean_object* v_X_43_, lean_object* v_00_u03b9_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_00_u03b5_50_, lean_object* v_s_51_, lean_object* v_N_52_, lean_object* v_V_53_, lean_object* v_Y_54_, lean_object* v_i_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_GRH_New_Grading_powerCoeff___redArg(v_inst_45_, v_s_51_, v_N_52_, v_Y_54_, v_i_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_powerCoeff___boxed(lean_object* v_E_57_, lean_object* v_X_58_, lean_object* v_00_u03b9_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_00_u03b5_65_, lean_object* v_s_66_, lean_object* v_N_67_, lean_object* v_V_68_, lean_object* v_Y_69_, lean_object* v_i_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_GRH_New_Grading_powerCoeff(v_E_57_, v_X_58_, v_00_u03b9_59_, v_inst_60_, v_inst_61_, v_inst_62_, v_inst_63_, v_inst_64_, v_00_u03b5_65_, v_s_66_, v_N_67_, v_V_68_, v_Y_69_, v_i_70_);
lean_dec_ref(v_V_68_);
lean_dec_ref(v_00_u03b5_65_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
lean_dec(v_inst_62_);
lean_dec_ref(v_inst_61_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__0(lean_object* v_toZero_72_, lean_object* v_x_73_){
_start:
{
lean_inc(v_toZero_72_);
return v_toZero_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__0___boxed(lean_object* v_toZero_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_Grading_stringPower___redArg___lam__0(v_toZero_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v_toZero_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__1(lean_object* v_i_77_, lean_object* v_toZero_78_, lean_object* v_inst_79_, lean_object* v_s_80_, lean_object* v_N_81_, lean_object* v_Y_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_nat_dec_eq(v_b_83_, v_i_77_);
if (v___x_84_ == 0)
{
lean_dec_ref(v_Y_82_);
lean_dec(v_N_81_);
lean_dec(v_s_80_);
lean_dec_ref(v_inst_79_);
lean_dec(v_i_77_);
lean_inc(v_toZero_78_);
return v_toZero_78_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lp_GRH_New_Grading_powerCoeff___redArg(v_inst_79_, v_s_80_, v_N_81_, v_Y_82_, v_i_77_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg___lam__1___boxed(lean_object* v_i_86_, lean_object* v_toZero_87_, lean_object* v_inst_88_, lean_object* v_s_89_, lean_object* v_N_90_, lean_object* v_Y_91_, lean_object* v_b_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_GRH_New_Grading_stringPower___redArg___lam__1(v_i_86_, v_toZero_87_, v_inst_88_, v_s_89_, v_N_90_, v_Y_91_, v_b_92_);
lean_dec(v_b_92_);
lean_dec(v_toZero_87_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___redArg(lean_object* v_inst_94_, lean_object* v_s_95_, lean_object* v_N_96_, lean_object* v_Y_97_, lean_object* v_i_98_, lean_object* v_k_99_){
_start:
{
lean_object* v___x_100_; lean_object* v_toCommSemiring_101_; lean_object* v___x_102_; lean_object* v_toZero_103_; lean_object* v_indexEquiv_104_; lean_object* v___x_105_; lean_object* v_toFun_106_; lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_100_ = lp_mathlib_Field_toSemifield___redArg(v_inst_94_);
v_toCommSemiring_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_toCommSemiring_101_);
lean_dec_ref(v___x_100_);
v___x_102_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_101_);
v_toZero_103_ = lean_ctor_get(v___x_102_, 1);
lean_inc_n(v_toZero_103_, 2);
lean_dec_ref(v___x_102_);
v_indexEquiv_104_ = lean_ctor_get(v_Y_97_, 0);
lean_inc_ref(v_indexEquiv_104_);
v___x_105_ = lp_mathlib_Equiv_symm___redArg(v_indexEquiv_104_);
v_toFun_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_toFun_106_);
lean_dec_ref(v___x_105_);
v___f_107_ = lean_alloc_closure((void*)(lp_GRH_New_Grading_stringPower___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_107_, 0, v_toZero_103_);
v___f_108_ = lean_alloc_closure((void*)(lp_GRH_New_Grading_stringPower___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_108_, 0, v_i_98_);
lean_closure_set(v___f_108_, 1, v_toZero_103_);
lean_closure_set(v___f_108_, 2, v_inst_94_);
lean_closure_set(v___f_108_, 3, v_s_95_);
lean_closure_set(v___f_108_, 4, v_N_96_);
lean_closure_set(v___f_108_, 5, v_Y_97_);
v___x_109_ = lean_apply_1(v_toFun_106_, v_k_99_);
v___x_110_ = l_Sum_elim___redArg(v___f_107_, v___f_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower(lean_object* v_E_111_, lean_object* v_X_112_, lean_object* v_00_u03b9_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_00_u03b5_119_, lean_object* v_s_120_, lean_object* v_N_121_, lean_object* v_V_122_, lean_object* v_Y_123_, lean_object* v_i_124_, lean_object* v_k_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_GRH_New_Grading_stringPower___redArg(v_inst_114_, v_s_120_, v_N_121_, v_Y_123_, v_i_124_, v_k_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringPower___boxed(lean_object* v_E_127_, lean_object* v_X_128_, lean_object* v_00_u03b9_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_00_u03b5_135_, lean_object* v_s_136_, lean_object* v_N_137_, lean_object* v_V_138_, lean_object* v_Y_139_, lean_object* v_i_140_, lean_object* v_k_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_GRH_New_Grading_stringPower(v_E_127_, v_X_128_, v_00_u03b9_129_, v_inst_130_, v_inst_131_, v_inst_132_, v_inst_133_, v_inst_134_, v_00_u03b5_135_, v_s_136_, v_N_137_, v_V_138_, v_Y_139_, v_i_140_, v_k_141_);
lean_dec_ref(v_V_138_);
lean_dec_ref(v_00_u03b5_135_);
lean_dec_ref(v_inst_134_);
lean_dec_ref(v_inst_133_);
lean_dec(v_inst_132_);
lean_dec_ref(v_inst_131_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_middlePower___redArg(lean_object* v_inst_143_, lean_object* v_s_144_, lean_object* v_N_145_, lean_object* v_Y_146_, lean_object* v_k_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_shiftr(v_s_144_, v___x_148_);
v___x_150_ = lp_GRH_New_Grading_stringPower___redArg(v_inst_143_, v_s_144_, v_N_145_, v_Y_146_, v___x_149_, v_k_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_middlePower(lean_object* v_E_151_, lean_object* v_X_152_, lean_object* v_00_u03b9_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_00_u03b5_159_, lean_object* v_s_160_, lean_object* v_N_161_, lean_object* v_V_162_, lean_object* v_Y_163_, lean_object* v_k_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lp_GRH_New_Grading_middlePower___redArg(v_inst_154_, v_s_160_, v_N_161_, v_Y_163_, v_k_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_middlePower___boxed(lean_object* v_E_166_, lean_object* v_X_167_, lean_object* v_00_u03b9_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_00_u03b5_174_, lean_object* v_s_175_, lean_object* v_N_176_, lean_object* v_V_177_, lean_object* v_Y_178_, lean_object* v_k_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_GRH_New_Grading_middlePower(v_E_166_, v_X_167_, v_00_u03b9_168_, v_inst_169_, v_inst_170_, v_inst_171_, v_inst_172_, v_inst_173_, v_00_u03b5_174_, v_s_175_, v_N_176_, v_V_177_, v_Y_178_, v_k_179_);
lean_dec_ref(v_V_177_);
lean_dec_ref(v_00_u03b5_174_);
lean_dec_ref(v_inst_173_);
lean_dec_ref(v_inst_172_);
lean_dec(v_inst_171_);
lean_dec_ref(v_inst_170_);
return v_res_180_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Periods_PointLattice(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Periods_StringPowers(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Periods_PointLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
