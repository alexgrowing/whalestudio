// Lean compiler output
// Module: New.Congruences.LocalLoss.Basic
// Imports: public import Init public meta import Init public import Lib.GaloisRep.Main.LocalConditions public import Lib.General.NumberTheory.PadicLimitsValuation public import New.Reduction.Data.AdmissibleData
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
extern lean_object* lp_mathlib_PUnit_fintype;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_padicValNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_Ioc___at___00New_Selmer_crystallineLoss_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_Ioc___at___00New_Selmer_crystallineLoss_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Selmer_crystallineLoss___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Selmer_crystallineLoss___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Selmer_crystallineLoss___closed__0 = (const lean_object*)&lp_GRH_New_Selmer_crystallineLoss___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_Ioc___at___00New_Selmer_crystallineLoss_spec__0(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_add(v_a_1_, v___x_3_);
v___x_5_ = lean_nat_sub(v_b_2_, v_a_1_);
v___x_6_ = lean_nat_add(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = lean_box(0);
v___x_8_ = l_List_range_x27TR_go(v___x_3_, v___x_5_, v___x_6_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_Ioc___at___00New_Selmer_crystallineLoss_spec__0___boxed(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_Finset_Ioc___at___00New_Selmer_crystallineLoss_spec__0(v_a_9_, v_b_10_);
lean_dec(v_b_10_);
lean_dec(v_a_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss___lam__0(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss___lam__0___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Selmer_crystallineLoss___lam__0(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss(lean_object* v_h_16_, lean_object* v_b_17_, lean_object* v_l_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___f_19_ = ((lean_object*)(lp_GRH_New_Selmer_crystallineLoss___closed__0));
v___x_20_ = lean_unsigned_to_nat(2u);
v___x_21_ = lean_nat_mul(v___x_20_, v_b_17_);
v___x_22_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_unsigned_to_nat(30u);
v___x_24_ = lean_unsigned_to_nat(3u);
v___x_25_ = lean_nat_pow(v_h_16_, v___x_24_);
v___x_26_ = lean_nat_mul(v___x_23_, v___x_25_);
v___x_27_ = lean_nat_sub(v_b_17_, v___x_26_);
v___x_28_ = lean_nat_add(v_b_17_, v___x_26_);
lean_dec(v___x_26_);
v___x_29_ = lp_GRH_Finset_Ioc___at___00New_Selmer_crystallineLoss_spec__0(v___x_27_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_27_);
v___x_30_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_29_, v___f_19_);
v___x_31_ = lean_nat_pow(v___x_30_, v___x_25_);
lean_dec(v___x_25_);
lean_dec(v___x_30_);
v___x_32_ = lean_nat_mul(v___x_22_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_22_);
v___x_33_ = lp_mathlib_padicValNat(v_l_18_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_crystallineLoss___boxed(lean_object* v_h_34_, lean_object* v_b_35_, lean_object* v_l_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_GRH_New_Selmer_crystallineLoss(v_h_34_, v_b_35_, v_l_36_);
lean_dec(v_l_36_);
lean_dec(v_b_35_);
lean_dec(v_h_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn___redArg(){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_GRH_New_Selmer_ribetCocyclesIn___redArg();
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn(lean_object* v_O_42_, lean_object* v_X_43_, lean_object* v_G_44_, lean_object* v_00_u03c3_45_, lean_object* v_d_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_u_53_, lean_object* v_00_u03c1_54_, lean_object* v_B_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocyclesIn___boxed(lean_object* v_O_59_, lean_object* v_X_60_, lean_object* v_G_61_, lean_object* v_00_u03c3_62_, lean_object* v_d_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_u_70_, lean_object* v_00_u03c1_71_, lean_object* v_B_72_, lean_object* v_inst_73_, lean_object* v_inst_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_GRH_New_Selmer_ribetCocyclesIn(v_O_59_, v_X_60_, v_G_61_, v_00_u03c3_62_, v_d_63_, v_inst_64_, v_inst_65_, v_inst_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_u_70_, v_00_u03c1_71_, v_B_72_, v_inst_73_, v_inst_74_);
lean_dec(v_inst_74_);
lean_dec_ref(v_inst_73_);
lean_dec(v_00_u03c1_71_);
lean_dec(v_u_70_);
lean_dec_ref(v_inst_69_);
lean_dec(v_inst_68_);
lean_dec_ref(v_inst_67_);
lean_dec(v_inst_66_);
lean_dec_ref(v_inst_65_);
lean_dec_ref(v_inst_64_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles___redArg(){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles___redArg___boxed(lean_object* v___dummy_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_GRH_New_Selmer_ribetCocycles___redArg();
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles(lean_object* v_O_80_, lean_object* v_X_81_, lean_object* v_G_82_, lean_object* v_00_u03c3_83_, lean_object* v_d_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_u_91_, lean_object* v_00_u03c1_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetCocycles___boxed(lean_object* v_O_95_, lean_object* v_X_96_, lean_object* v_G_97_, lean_object* v_00_u03c3_98_, lean_object* v_d_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_u_106_, lean_object* v_00_u03c1_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_GRH_New_Selmer_ribetCocycles(v_O_95_, v_X_96_, v_G_97_, v_00_u03c3_98_, v_d_99_, v_inst_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_u_106_, v_00_u03c1_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec(v_00_u03c1_107_);
lean_dec(v_u_106_);
lean_dec_ref(v_inst_105_);
lean_dec(v_inst_104_);
lean_dec_ref(v_inst_103_);
lean_dec(v_inst_102_);
lean_dec_ref(v_inst_101_);
lean_dec_ref(v_inst_100_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex___redArg(lean_object* v_inst_110_, lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
lean_inc(v_inst_110_);
return v_inst_110_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lp_mathlib_PUnit_fintype;
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex___redArg___boxed(lean_object* v_inst_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = lp_GRH_New_Selmer_instFintypeSummandCoordIndex___redArg(v_inst_113_, v_x_114_);
lean_dec(v_x_114_);
lean_dec(v_inst_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex(lean_object* v_r_116_, lean_object* v_inst_117_, lean_object* v_t_118_, lean_object* v_x_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lp_GRH_New_Selmer_instFintypeSummandCoordIndex___redArg(v_inst_117_, v_x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instFintypeSummandCoordIndex___boxed(lean_object* v_r_121_, lean_object* v_inst_122_, lean_object* v_t_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_GRH_New_Selmer_instFintypeSummandCoordIndex(v_r_121_, v_inst_122_, v_t_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_t_123_);
lean_dec(v_inst_122_);
return v_res_125_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___redArg(lean_object* v_inst_126_, lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_apply_2(v_inst_126_, v_a_128_, v_b_129_);
v___x_131_ = lean_unbox(v___x_130_);
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
lean_dec(v_b_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_inst_126_);
v___x_132_ = 1;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___redArg___boxed(lean_object* v_inst_133_, lean_object* v_x_134_, lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___redArg(v_inst_133_, v_x_134_, v_a_135_, v_b_136_);
lean_dec(v_x_134_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex(lean_object* v_r_139_, lean_object* v_inst_140_, lean_object* v_t_141_, lean_object* v_x_142_, lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___redArg(v_inst_140_, v_x_142_, v_a_143_, v_b_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex___boxed(lean_object* v_r_146_, lean_object* v_inst_147_, lean_object* v_t_148_, lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = lp_GRH_New_Selmer_instDecidableEqSummandCoordIndex(v_r_146_, v_inst_147_, v_t_148_, v_x_149_, v_a_150_, v_b_151_);
lean_dec(v_x_149_);
lean_dec(v_t_148_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Main_LocalConditions(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_PadicLimitsValuation(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Data_AdmissibleData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_LocalLoss_Basic(uint8_t builtin) {
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
res = initialize_GRH_Lib_GaloisRep_Main_LocalConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_PadicLimitsValuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Data_AdmissibleData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
