// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion public import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_TensorProduct_AlgebraTensorModule_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instLattice;
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sup___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_MiW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_MiW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hiW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hiW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___redArg(lean_object* v_n_1_, lean_object* v_b_2_, lean_object* v_S_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toSemilatticeSup_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = lp_mathlib_Nat_instLattice;
v_toSemilatticeSup_5_ = lean_ctor_get(v___x_4_, 0);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lp_mathlib_ZMod_fintype___redArg(v_n_1_);
lean_inc_ref(v_toSemilatticeSup_5_);
v___x_8_ = lp_mathlib_Finset_sup___redArg(v_toSemilatticeSup_5_, v___x_6_, v___x_7_, v_b_2_);
v___x_9_ = lean_nat_add(v___x_8_, v_S_3_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___redArg___boxed(lean_object* v_n_10_, lean_object* v_b_11_, lean_object* v_S_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___redArg(v_n_10_, v_b_11_, v_S_12_);
lean_dec(v_S_12_);
lean_dec(v_n_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar(lean_object* v_n_14_, lean_object* v_inst_15_, lean_object* v_b_16_, lean_object* v_S_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___redArg(v_n_14_, v_b_16_, v_S_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar___boxed(lean_object* v_n_19_, lean_object* v_inst_20_, lean_object* v_b_21_, lean_object* v_S_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hpar(v_n_19_, v_inst_20_, v_b_21_, v_S_22_);
lean_dec(v_S_22_);
lean_dec(v_n_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_MiW(lean_object* v_n_24_, lean_object* v_d_25_, lean_object* v_b_26_, lean_object* v_S_27_, lean_object* v_00_u03b7_28_, lean_object* v_i_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_30_ = lp_mathlib_ZMod_val(v_n_24_, v_i_29_);
v___x_31_ = lean_nat_add(v___x_30_, v_d_25_);
lean_dec(v___x_30_);
v___x_32_ = lean_unsigned_to_nat(2u);
v___x_33_ = lean_nat_mod(v___x_31_, v___x_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_nat_dec_eq(v___x_33_, v___x_34_);
lean_dec(v___x_33_);
if (v___x_35_ == 0)
{
lean_dec(v_i_29_);
lean_dec_ref(v_b_26_);
lean_inc(v_00_u03b7_28_);
return v_00_u03b7_28_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_apply_1(v_b_26_, v_i_29_);
v___x_37_ = lean_nat_add(v___x_36_, v_S_27_);
lean_dec(v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_MiW___boxed(lean_object* v_n_38_, lean_object* v_d_39_, lean_object* v_b_40_, lean_object* v_S_41_, lean_object* v_00_u03b7_42_, lean_object* v_i_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_MiW(v_n_38_, v_d_39_, v_b_40_, v_S_41_, v_00_u03b7_42_, v_i_43_);
lean_dec(v_00_u03b7_42_);
lean_dec(v_S_41_);
lean_dec(v_d_39_);
lean_dec(v_n_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hiW(lean_object* v_n_45_, lean_object* v_d_46_, lean_object* v_b_47_, lean_object* v_S_48_, lean_object* v_00_u03b7_49_, lean_object* v_i_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_51_ = lp_mathlib_ZMod_val(v_n_45_, v_i_50_);
v___x_52_ = lean_nat_add(v___x_51_, v_d_46_);
lean_dec(v___x_51_);
v___x_53_ = lean_unsigned_to_nat(2u);
v___x_54_ = lean_nat_mod(v___x_52_, v___x_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_nat_dec_eq(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_apply_1(v_b_47_, v_i_50_);
v___x_58_ = lean_nat_add(v___x_57_, v_S_48_);
lean_dec(v___x_57_);
return v___x_58_;
}
else
{
lean_dec(v_i_50_);
lean_dec_ref(v_b_47_);
lean_inc(v_00_u03b7_49_);
return v_00_u03b7_49_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hiW___boxed(lean_object* v_n_59_, lean_object* v_d_60_, lean_object* v_b_61_, lean_object* v_S_62_, lean_object* v_00_u03b7_63_, lean_object* v_i_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_hiW(v_n_59_, v_d_60_, v_b_61_, v_S_62_, v_00_u03b7_63_, v_i_64_);
lean_dec(v_00_u03b7_63_);
lean_dec(v_S_62_);
lean_dec(v_d_60_);
lean_dec(v_n_59_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_f_72_){
_start:
{
lean_object* v___x_73_; lean_object* v_toSemiring_74_; lean_object* v_toCommSemiring_75_; lean_object* v_toAddCommMonoid_76_; lean_object* v_toSMul_77_; lean_object* v_toAddMonoid_78_; lean_object* v___f_79_; lean_object* v___x_80_; 
v___x_73_ = lp_mathlib_Field_toSemifield___redArg(v_inst_67_);
v_toSemiring_74_ = lean_ctor_get(v_inst_68_, 0);
lean_inc_ref(v_toSemiring_74_);
lean_dec_ref(v_inst_68_);
v_toCommSemiring_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_toCommSemiring_75_);
lean_dec_ref(v___x_73_);
v_toAddCommMonoid_76_ = lean_ctor_get(v_toSemiring_74_, 0);
lean_inc_ref_n(v_toAddCommMonoid_76_, 2);
lean_dec_ref(v_toSemiring_74_);
v_toSMul_77_ = lean_ctor_get(v_inst_69_, 0);
lean_inc_n(v_toSMul_77_, 2);
lean_dec_ref(v_inst_69_);
v_toAddMonoid_78_ = lean_ctor_get(v_inst_70_, 0);
lean_inc_ref(v_toAddMonoid_78_);
lean_dec_ref(v_inst_70_);
v___f_79_ = ((lean_object*)(lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg___closed__0));
v___x_80_ = lp_mathlib_TensorProduct_AlgebraTensorModule_map___redArg(v_toCommSemiring_75_, v_toAddCommMonoid_76_, v_toSMul_77_, v_toAddMonoid_78_, v_inst_71_, v_toAddCommMonoid_76_, v_toSMul_77_, v_f_72_, v___f_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg___boxed(lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_f_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg(v_inst_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_inst_85_, v_f_86_);
lean_dec_ref(v_inst_81_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB(lean_object* v_Qp_88_, lean_object* v_inst_89_, lean_object* v_B_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_LL_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_V_96_, lean_object* v_V_x27_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_f_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___redArg(v_inst_89_, v_inst_91_, v_inst_92_, v_inst_102_, v_inst_104_, v_f_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB___boxed(lean_object** _args){
lean_object* v_Qp_108_ = _args[0];
lean_object* v_inst_109_ = _args[1];
lean_object* v_B_110_ = _args[2];
lean_object* v_inst_111_ = _args[3];
lean_object* v_inst_112_ = _args[4];
lean_object* v_LL_113_ = _args[5];
lean_object* v_inst_114_ = _args[6];
lean_object* v_inst_115_ = _args[7];
lean_object* v_V_116_ = _args[8];
lean_object* v_V_x27_117_ = _args[9];
lean_object* v_inst_118_ = _args[10];
lean_object* v_inst_119_ = _args[11];
lean_object* v_inst_120_ = _args[12];
lean_object* v_inst_121_ = _args[13];
lean_object* v_inst_122_ = _args[14];
lean_object* v_inst_123_ = _args[15];
lean_object* v_inst_124_ = _args[16];
lean_object* v_inst_125_ = _args[17];
lean_object* v_f_126_ = _args[18];
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_mapVB(v_Qp_108_, v_inst_109_, v_B_110_, v_inst_111_, v_inst_112_, v_LL_113_, v_inst_114_, v_inst_115_, v_V_116_, v_V_x27_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_inst_123_, v_inst_124_, v_inst_125_, v_f_126_);
lean_dec(v_inst_123_);
lean_dec(v_inst_120_);
lean_dec(v_inst_119_);
lean_dec_ref(v_inst_118_);
lean_dec_ref(v_inst_115_);
lean_dec_ref(v_inst_114_);
lean_dec_ref(v_inst_109_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___redArg(lean_object* v_00_u03ba_128_){
_start:
{
lean_inc(v_00_u03ba_128_);
return v_00_u03ba_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___redArg___boxed(lean_object* v_00_u03ba_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___redArg(v_00_u03ba_129_);
lean_dec(v_00_u03ba_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK(lean_object* v_G_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_Qp_134_, lean_object* v_inst_135_, lean_object* v_LL_136_, lean_object* v_O_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_T_143_, lean_object* v_00_u03ba_144_, lean_object* v_h_u03ba_145_){
_start:
{
lean_inc(v_00_u03ba_144_);
return v_00_u03ba_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK___boxed(lean_object* v_G_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_Qp_149_, lean_object* v_inst_150_, lean_object* v_LL_151_, lean_object* v_O_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_T_158_, lean_object* v_00_u03ba_159_, lean_object* v_h_u03ba_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_tree_Formalism_MainNotions_RamifiedCoefficientChains_clsK(v_G_146_, v_inst_147_, v_inst_148_, v_Qp_149_, v_inst_150_, v_LL_151_, v_O_152_, v_inst_153_, v_inst_154_, v_inst_155_, v_inst_156_, v_inst_157_, v_T_158_, v_00_u03ba_159_, v_h_u03ba_160_);
lean_dec(v_00_u03ba_159_);
lean_dec_ref(v_T_158_);
lean_dec_ref(v_inst_157_);
lean_dec_ref(v_inst_156_);
lean_dec_ref(v_inst_154_);
lean_dec_ref(v_inst_153_);
lean_dec_ref(v_inst_150_);
lean_dec_ref(v_inst_147_);
return v_res_161_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_UsedLocalConclusion(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_GammaSemisimpleLocalOfConsequences(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_LiftingTheory(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DeltaInvariantLattices(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_RamifiedCoefficientChains(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_UsedLocalConclusion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_GammaSemisimpleLocalOfConsequences(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_LiftingTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_DeltaInvariantLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
