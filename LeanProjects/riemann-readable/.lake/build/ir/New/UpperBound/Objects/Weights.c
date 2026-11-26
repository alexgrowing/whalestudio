// Lean compiler output
// Module: New.UpperBound.Objects.Weights
// Imports: public import Init public meta import Init public import New.Reduction.Data.LevelAndTwists
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
lean_object* lp_GRH_New_Data_k___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_t___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_liftWeight___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_targetParameter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_n___redArg(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_reducedHalfGap___redArg(lean_object*);
static lean_once_cell_t lp_GRH_New_Data_lastEntry___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_lastEntry___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Data_lastEntry___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_lastEntry___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_twiceBlockEntry___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_twiceBlockEntry___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_twiceBlockEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_sortedParamY___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_sortedParamY(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_sortedParamY___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_weightY___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_weightY(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_weightY___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Data_lastEntry___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Data_lastEntry___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry___redArg(lean_object* v_D_5_, lean_object* v_j_6_, lean_object* v_00_u03c4_7_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_nat_dec_eq(v_j_6_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_sub(v_j_6_, v___x_10_);
v___x_12_ = lp_GRH_New_Data_n___redArg(v_D_5_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_nat_to_int(v___x_12_);
v___x_14_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__0, &lp_GRH_New_Data_lastEntry___redArg___closed__0_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__0);
v___x_15_ = lean_int_ediv(v___x_13_, v___x_14_);
lean_dec(v___x_13_);
v___x_16_ = lp_GRH_New_Data_liftWeight___redArg(v_D_5_, v_j_6_, v_00_u03c4_7_);
v___x_17_ = lean_nat_to_int(v___x_16_);
v___x_18_ = lean_int_sub(v___x_15_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_15_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; 
lean_dec(v_00_u03c4_7_);
lean_dec_ref(v_D_5_);
v___x_19_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__1, &lp_GRH_New_Data_lastEntry___redArg___closed__1_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__1);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry___redArg___boxed(lean_object* v_D_20_, lean_object* v_j_21_, lean_object* v_00_u03c4_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_Data_lastEntry___redArg(v_D_20_, v_j_21_, v_00_u03c4_22_);
lean_dec(v_j_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry(lean_object* v_P_24_, lean_object* v_D_25_, lean_object* v_j_26_, lean_object* v_00_u03c4_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GRH_New_Data_lastEntry___redArg(v_D_25_, v_j_26_, v_00_u03c4_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_lastEntry___boxed(lean_object* v_P_29_, lean_object* v_D_30_, lean_object* v_j_31_, lean_object* v_00_u03c4_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_Data_lastEntry(v_P_29_, v_D_30_, v_j_31_, v_00_u03c4_32_);
lean_dec(v_j_31_);
lean_dec_ref(v_P_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns___redArg(lean_object* v_D_34_, lean_object* v_h_35_){
_start:
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = lp_GRH_New_Data_k___redArg(v_D_34_);
v___x_37_ = lean_nat_dec_le(v___x_36_, v_h_35_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec(v___x_36_);
v___x_38_ = lean_unsigned_to_nat(0u);
return v___x_38_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_39_ = lp_GRH_New_Data_t___redArg(v_D_34_);
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_add(v___x_39_, v___x_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_nat_sub(v_h_35_, v___x_36_);
lean_dec(v___x_36_);
v___x_43_ = lean_nat_mod(v___x_42_, v___x_41_);
lean_dec(v___x_41_);
lean_dec(v___x_42_);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
lean_dec(v___x_43_);
if (v___x_45_ == 0)
{
return v___x_44_;
}
else
{
lean_object* v___x_46_; 
v___x_46_ = lp_GRH_New_Data_reducedHalfGap___redArg(v_D_34_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns___redArg___boxed(lean_object* v_D_47_, lean_object* v_h_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH_New_Data_keptColumns___redArg(v_D_47_, v_h_48_);
lean_dec(v_h_48_);
lean_dec_ref(v_D_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns(lean_object* v_P_50_, lean_object* v_D_51_, lean_object* v_h_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_GRH_New_Data_keptColumns___redArg(v_D_51_, v_h_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_keptColumns___boxed(lean_object* v_P_54_, lean_object* v_D_55_, lean_object* v_h_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_GRH_New_Data_keptColumns(v_P_54_, v_D_55_, v_h_56_);
lean_dec(v_h_56_);
lean_dec_ref(v_D_55_);
lean_dec_ref(v_P_54_);
return v_res_57_;
}
}
static lean_object* _init_lp_GRH_New_twiceBlockEntry___closed__0(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twiceBlockEntry(lean_object* v_n_60_, lean_object* v_p_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_62_ = lean_nat_to_int(v_n_60_);
v___x_63_ = lean_obj_once(&lp_GRH_New_twiceBlockEntry___closed__0, &lp_GRH_New_twiceBlockEntry___closed__0_once, _init_lp_GRH_New_twiceBlockEntry___closed__0);
v___x_64_ = lean_int_sub(v___x_62_, v___x_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__0, &lp_GRH_New_Data_lastEntry___redArg___closed__0_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__0);
v___x_66_ = lean_nat_to_int(v_p_61_);
v___x_67_ = lean_int_mul(v___x_65_, v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = lean_int_sub(v___x_64_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_64_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_sortedParamY___redArg(lean_object* v_D_69_, lean_object* v_00_u03c4_70_, lean_object* v_p_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_p_71_, v___x_72_);
v___x_74_ = lp_GRH_New_Data_k___redArg(v_D_69_);
v___x_75_ = lean_nat_dec_lt(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
lean_dec(v_p_71_);
v___x_76_ = lp_GRH_New_Data_t___redArg(v_D_69_);
v___x_77_ = lean_nat_add(v___x_76_, v___x_72_);
v___x_78_ = lean_nat_sub(v___x_73_, v___x_74_);
lean_dec(v___x_73_);
v___x_79_ = lean_nat_mod(v___x_78_, v___x_77_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v___x_74_);
v___x_82_ = lean_nat_sub(v___x_79_, v___x_72_);
lean_dec(v___x_79_);
v___x_83_ = lp_GRH_New_twiceBlockEntry(v___x_76_, v___x_82_);
v___x_84_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__0, &lp_GRH_New_Data_lastEntry___redArg___closed__0_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__0);
v___x_85_ = lean_nat_div(v___x_78_, v___x_77_);
lean_dec(v___x_77_);
lean_dec(v___x_78_);
v___x_86_ = lean_nat_add(v___x_85_, v___x_72_);
lean_dec(v___x_85_);
v___x_87_ = lp_GRH_New_Data_liftWeight___redArg(v_D_69_, v___x_86_, v_00_u03c4_70_);
lean_dec(v___x_86_);
v___x_88_ = lean_nat_to_int(v___x_87_);
v___x_89_ = lean_int_mul(v___x_84_, v___x_88_);
lean_dec(v___x_88_);
v___x_90_ = lean_int_sub(v___x_83_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_83_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v___x_79_);
lean_dec(v___x_76_);
v___x_91_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__0, &lp_GRH_New_Data_lastEntry___redArg___closed__0_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__0);
v___x_92_ = lean_nat_sub(v___x_74_, v___x_72_);
lean_dec(v___x_74_);
v___x_93_ = lean_nat_div(v___x_78_, v___x_77_);
lean_dec(v___x_77_);
lean_dec(v___x_78_);
v___x_94_ = lean_nat_add(v___x_92_, v___x_93_);
lean_dec(v___x_93_);
lean_dec(v___x_92_);
v___x_95_ = lp_GRH_New_Data_targetParameter___redArg(v_D_69_, v_00_u03c4_70_, v___x_94_);
v___x_96_ = lean_int_mul(v___x_91_, v___x_95_);
lean_dec(v___x_95_);
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v___x_74_);
lean_dec(v___x_73_);
v___x_97_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__0, &lp_GRH_New_Data_lastEntry___redArg___closed__0_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__0);
v___x_98_ = lp_GRH_New_Data_targetParameter___redArg(v_D_69_, v_00_u03c4_70_, v_p_71_);
v___x_99_ = lean_int_mul(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_sortedParamY(lean_object* v_P_100_, lean_object* v_D_101_, lean_object* v_00_u03c4_102_, lean_object* v_p_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_GRH_New_Data_sortedParamY___redArg(v_D_101_, v_00_u03c4_102_, v_p_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_sortedParamY___boxed(lean_object* v_P_105_, lean_object* v_D_106_, lean_object* v_00_u03c4_107_, lean_object* v_p_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_GRH_New_Data_sortedParamY(v_P_105_, v_D_106_, v_00_u03c4_107_, v_p_108_);
lean_dec_ref(v_P_105_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_weightY___redArg(lean_object* v_D_110_, lean_object* v_00_u03c4_111_, lean_object* v_p_112_){
_start:
{
lean_object* v_m_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_m_113_ = lean_ctor_get(v_D_110_, 6);
lean_inc(v_m_113_);
lean_inc(v_p_112_);
lean_inc_ref(v_D_110_);
v___x_114_ = lp_GRH_New_Data_sortedParamY___redArg(v_D_110_, v_00_u03c4_111_, v_p_112_);
v___x_115_ = lp_GRH_New_Data_n___redArg(v_D_110_, v_m_113_);
lean_dec(v_m_113_);
lean_dec_ref(v_D_110_);
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_sub(v___x_115_, v___x_116_);
lean_dec(v___x_115_);
v___x_118_ = lp_GRH_New_twiceBlockEntry(v___x_117_, v_p_112_);
v___x_119_ = lean_int_sub(v___x_114_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_114_);
v___x_120_ = lean_obj_once(&lp_GRH_New_Data_lastEntry___redArg___closed__0, &lp_GRH_New_Data_lastEntry___redArg___closed__0_once, _init_lp_GRH_New_Data_lastEntry___redArg___closed__0);
v___x_121_ = lean_int_ediv(v___x_119_, v___x_120_);
lean_dec(v___x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_weightY(lean_object* v_P_122_, lean_object* v_D_123_, lean_object* v_00_u03c4_124_, lean_object* v_p_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_GRH_New_Data_weightY___redArg(v_D_123_, v_00_u03c4_124_, v_p_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_weightY___boxed(lean_object* v_P_127_, lean_object* v_D_128_, lean_object* v_00_u03c4_129_, lean_object* v_p_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_GRH_New_Data_weightY(v_P_127_, v_D_128_, v_00_u03c4_129_, v_p_130_);
lean_dec_ref(v_P_127_);
return v_res_131_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Data_LevelAndTwists(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_Weights(uint8_t builtin) {
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
res = initialize_GRH_New_Reduction_Data_LevelAndTwists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
