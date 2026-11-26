// Lean compiler output
// Module: New.UpperBound.Objects.LiftChains
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.BlockEmbeddings public import Lib.Shimura.HeckeTower.HeckeData public import Lib.Weil.CompactLift.ThetaKernelDefs public import New.Reduction.Data.Sizes public import New.UpperBound.Objects.LabelsAndIndexTypes public import New.UpperBound.Objects.LiftLawsModuloN
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
extern lean_object* lp_mathlib_Complex_instCommSemiring;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_TensorProduct_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_compUpTo___redArg(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_twoKernelAction___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_twoKernelAction___redArg___closed__0 = (const lean_object*)&lp_GRH_New_twoKernelAction___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction___redArg(lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_k_4_, lean_object* v_a_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toAddMonoid_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_toAddMonoid_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_00_u03c9_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_44_; 
v___x_7_ = lp_mathlib_Complex_instCommSemiring;
v___x_8_ = lean_unsigned_to_nat(2u);
v___x_9_ = lean_nat_mul(v___x_8_, v_i_6_);
lean_inc_ref(v_inst_2_);
lean_inc_n(v___x_9_, 3);
v___x_10_ = lean_apply_1(v_inst_2_, v___x_9_);
v_toAddMonoid_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_ref(v_toAddMonoid_11_);
lean_dec_ref(v___x_10_);
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_add(v___x_9_, v___x_12_);
lean_inc(v___x_13_);
v___x_14_ = lean_apply_1(v_inst_2_, v___x_13_);
v_toAddMonoid_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toAddMonoid_15_);
lean_dec_ref(v___x_14_);
lean_inc(v_inst_3_);
v___x_16_ = lean_apply_1(v_inst_3_, v___x_9_);
lean_inc_ref(v_k_4_);
v___x_17_ = lean_apply_1(v_k_4_, v___x_9_);
v_00_u03c9_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v___x_17_, 1);
lean_dec(v_unused_45_);
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_44_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_00_u03c9_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_44_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_00_u03c9_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_42_; 
lean_inc_n(v___x_13_, 3);
v___x_22_ = lean_apply_1(v_inst_3_, v___x_13_);
lean_inc_ref_n(v_a_5_, 2);
v___x_23_ = lean_apply_1(v_a_5_, v___x_9_);
v___x_24_ = lean_apply_1(v_a_5_, v___x_13_);
v___x_25_ = lean_apply_1(v_k_4_, v___x_13_);
v_00_u03c9_26_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_25_, 1);
lean_dec(v_unused_43_);
v___x_28_ = v___x_25_;
v_isShared_29_ = v_isSharedCheck_42_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_00_u03c9_26_);
lean_dec(v___x_25_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_42_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___f_30_; lean_object* v___x_32_; 
v___f_30_ = ((lean_object*)(lp_GRH_New_twoKernelAction___redArg___closed__0));
lean_inc_ref(v___x_24_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v___x_24_);
lean_ctor_set(v___x_28_, 0, v___x_23_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_24_);
v___x_32_ = v_reuseFailAlloc_41_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_33_ = lean_apply_1(v_00_u03c9_18_, v___x_32_);
v___x_34_ = lean_nat_add(v___x_13_, v___x_12_);
lean_dec(v___x_13_);
v___x_35_ = lean_apply_1(v_a_5_, v___x_34_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___x_35_);
lean_ctor_set(v___x_20_, 0, v___x_24_);
v___x_37_ = v___x_20_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_40_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_apply_1(v_00_u03c9_26_, v___x_37_);
lean_inc(v___x_22_);
lean_inc_ref(v_toAddMonoid_15_);
v___x_39_ = lp_mathlib_TensorProduct_map___redArg(v___x_7_, v___x_7_, v___f_30_, v_toAddMonoid_15_, v_toAddMonoid_11_, v_toAddMonoid_15_, v___x_22_, v___x_16_, v___x_22_, v___x_33_, v___x_38_);
return v___x_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction___redArg___boxed(lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_k_48_, lean_object* v_a_49_, lean_object* v_i_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_GRH_New_twoKernelAction___redArg(v_inst_46_, v_inst_47_, v_k_48_, v_a_49_, v_i_50_);
lean_dec(v_i_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction(lean_object* v_E_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_n_55_, lean_object* v_S_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_00_u03ba_61_, lean_object* v_e_62_, lean_object* v_K_63_, lean_object* v_k_64_, lean_object* v_a_65_, lean_object* v_i_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_GRH_New_twoKernelAction___redArg(v_inst_59_, v_inst_60_, v_k_64_, v_a_65_, v_i_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoKernelAction___boxed(lean_object* v_E_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_n_71_, lean_object* v_S_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_00_u03ba_77_, lean_object* v_e_78_, lean_object* v_K_79_, lean_object* v_k_80_, lean_object* v_a_81_, lean_object* v_i_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_GRH_New_twoKernelAction(v_E_68_, v_inst_69_, v_inst_70_, v_n_71_, v_S_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_00_u03ba_77_, v_e_78_, v_K_79_, v_k_80_, v_a_81_, v_i_82_);
lean_dec(v_i_82_);
lean_dec_ref(v_K_79_);
lean_dec_ref(v_e_78_);
lean_dec_ref(v_00_u03ba_77_);
lean_dec_ref(v_inst_74_);
lean_dec(v_inst_73_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_69_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___redArg___lam__0(lean_object* v_k_84_, lean_object* v_g_85_, lean_object* v_00_u03a6_86_, lean_object* v_j_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_90_; lean_object* v_00_u03c9_91_; lean_object* v_jetMap_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_106_; 
lean_inc(v_j_87_);
v___x_90_ = lean_apply_1(v_k_84_, v_j_87_);
v_00_u03c9_91_ = lean_ctor_get(v___x_90_, 0);
v_jetMap_92_ = lean_ctor_get(v___x_90_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_106_ == 0)
{
v___x_94_ = v___x_90_;
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_jetMap_92_);
lean_inc(v_00_u03c9_91_);
lean_dec(v___x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
lean_inc_ref(v_g_85_);
lean_inc(v_j_87_);
v___x_96_ = lean_apply_1(v_g_85_, v_j_87_);
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_j_87_, v___x_97_);
v___x_99_ = lean_apply_1(v_g_85_, v___x_98_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v___x_99_);
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_101_ = v___x_94_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_105_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_apply_1(v_00_u03a6_86_, v_j_87_);
v___x_103_ = lean_apply_2(v_00_u03c9_91_, v___x_101_, v___x_102_);
v___x_104_ = lean_apply_3(v_jetMap_92_, v___x_103_, v___y_88_, v___y_89_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___redArg(lean_object* v_k_107_, lean_object* v_00_u03a6_108_, lean_object* v_00_u03c6_109_, lean_object* v_g_110_, lean_object* v_m_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_95__overap_117_; lean_object* v___x_118_; 
lean_inc_ref(v_g_110_);
v___f_113_ = lean_alloc_closure((void*)(lp_GRH_New_kernelProduct___redArg___lam__0), 6, 3);
lean_closure_set(v___f_113_, 0, v_k_107_);
lean_closure_set(v___f_113_, 1, v_g_110_);
lean_closure_set(v___f_113_, 2, v_00_u03a6_108_);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_apply_1(v_g_110_, v___x_114_);
v___x_116_ = lean_apply_1(v_00_u03c6_109_, v___x_115_);
v___x_95__overap_117_ = lp_GRH_New_compUpTo___redArg(v___f_113_, v_m_111_);
v___x_118_ = lean_apply_2(v___x_95__overap_117_, v___x_116_, v_a_112_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___redArg___boxed(lean_object* v_k_119_, lean_object* v_00_u03a6_120_, lean_object* v_00_u03c6_121_, lean_object* v_g_122_, lean_object* v_m_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_GRH_New_kernelProduct___redArg(v_k_119_, v_00_u03a6_120_, v_00_u03c6_121_, v_g_122_, v_m_123_, v_a_124_);
lean_dec(v_m_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct(lean_object* v_E_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_n_129_, lean_object* v_S_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_00_u03ba_135_, lean_object* v_e_136_, lean_object* v_K_137_, lean_object* v_k_138_, lean_object* v_00_u03a6_139_, lean_object* v_00_u03c6_140_, lean_object* v_g_141_, lean_object* v_m_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lp_GRH_New_kernelProduct___redArg(v_k_138_, v_00_u03a6_139_, v_00_u03c6_140_, v_g_141_, v_m_142_, v_a_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_kernelProduct___boxed(lean_object** _args){
lean_object* v_E_145_ = _args[0];
lean_object* v_inst_146_ = _args[1];
lean_object* v_inst_147_ = _args[2];
lean_object* v_n_148_ = _args[3];
lean_object* v_S_149_ = _args[4];
lean_object* v_inst_150_ = _args[5];
lean_object* v_inst_151_ = _args[6];
lean_object* v_inst_152_ = _args[7];
lean_object* v_inst_153_ = _args[8];
lean_object* v_00_u03ba_154_ = _args[9];
lean_object* v_e_155_ = _args[10];
lean_object* v_K_156_ = _args[11];
lean_object* v_k_157_ = _args[12];
lean_object* v_00_u03a6_158_ = _args[13];
lean_object* v_00_u03c6_159_ = _args[14];
lean_object* v_g_160_ = _args[15];
lean_object* v_m_161_ = _args[16];
lean_object* v_a_162_ = _args[17];
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_GRH_New_kernelProduct(v_E_145_, v_inst_146_, v_inst_147_, v_n_148_, v_S_149_, v_inst_150_, v_inst_151_, v_inst_152_, v_inst_153_, v_00_u03ba_154_, v_e_155_, v_K_156_, v_k_157_, v_00_u03a6_158_, v_00_u03c6_159_, v_g_160_, v_m_161_, v_a_162_);
lean_dec(v_m_161_);
lean_dec_ref(v_K_156_);
lean_dec_ref(v_e_155_);
lean_dec_ref(v_00_u03ba_154_);
lean_dec(v_inst_153_);
lean_dec_ref(v_inst_152_);
lean_dec_ref(v_inst_151_);
lean_dec(v_inst_150_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
return v_res_163_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_HeckeTower_HeckeData(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_CompactLift_ThetaKernelDefs(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Data_Sizes(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_LabelsAndIndexTypes(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_LiftLawsModuloN(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_LiftChains(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_HeckeTower_HeckeData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_CompactLift_ThetaKernelDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Data_Sizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_LabelsAndIndexTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_LiftLawsModuloN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
