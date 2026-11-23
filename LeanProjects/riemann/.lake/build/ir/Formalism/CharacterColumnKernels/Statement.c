// Lean compiler output
// Module: Formalism.CharacterColumnKernels.Statement
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
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OreLocalization_oreSetComm(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_OreLocalization_instAddGroupOreLocalization___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_OreLocalization_instModuleOfIsScalarTower___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_Quotient_addCommGroup___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_Quotient_instSMul_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_matQ___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_matQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_congIdeal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_congIdeal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___redArg___lam__0(lean_object* v_r_1_, lean_object* v___x_2_, lean_object* v_toSub_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_r_1_);
v___x_5_ = lean_apply_1(v_r_1_, v___x_2_);
v___x_6_ = lean_apply_1(v_r_1_, v_i_4_);
v___x_7_ = lean_apply_2(v_toSub_3_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___redArg(lean_object* v_inst_8_, lean_object* v_t_9_, lean_object* v_r_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v_toSub_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___x_23_; 
v___x_11_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_8_);
v___x_12_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_8_);
v___x_13_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_12_);
lean_dec_ref(v___x_12_);
v_toSub_14_ = lean_ctor_get(v___x_13_, 2);
lean_inc(v_toSub_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_t_9_, v___x_15_);
lean_inc_n(v___x_16_, 2);
v___x_17_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_17_, 0, v___x_16_);
v___x_18_ = l_List_finRange(v___x_16_);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_nat_mod(v___x_19_, v___x_16_);
lean_dec(v___x_16_);
lean_inc(v___x_20_);
v___x_21_ = lp_mathlib_Multiset_erase___redArg(v___x_17_, v___x_18_, v___x_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_delta___redArg___lam__0), 4, 3);
lean_closure_set(v___f_22_, 0, v_r_10_);
lean_closure_set(v___f_22_, 1, v___x_20_);
lean_closure_set(v___f_22_, 2, v_toSub_14_);
v___x_23_ = lp_mathlib_Finset_prod___redArg(v___x_11_, v___x_21_, v___f_22_);
lean_dec_ref(v___x_11_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___redArg___boxed(lean_object* v_inst_24_, lean_object* v_t_25_, lean_object* v_r_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_NG_delta___redArg(v_inst_24_, v_t_25_, v_r_26_);
lean_dec(v_t_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta(lean_object* v_T_28_, lean_object* v_inst_29_, lean_object* v_t_30_, lean_object* v_r_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_tree_Formalism_NG_delta___redArg(v_inst_29_, v_t_30_, v_r_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_delta___boxed(lean_object* v_T_33_, lean_object* v_inst_34_, lean_object* v_t_35_, lean_object* v_r_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_NG_delta(v_T_33_, v_inst_34_, v_t_35_, v_r_36_);
lean_dec(v_t_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relSpan(lean_object* v_R_38_, lean_object* v_inst_39_, lean_object* v_m_40_, lean_object* v_g_41_, lean_object* v_00_u0398_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relSpan___boxed(lean_object* v_R_44_, lean_object* v_inst_45_, lean_object* v_m_46_, lean_object* v_g_47_, lean_object* v_00_u0398_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_NG_relSpan(v_R_44_, v_inst_45_, v_m_46_, v_g_47_, v_00_u0398_48_);
lean_dec(v_00_u0398_48_);
lean_dec_ref(v_inst_45_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg___lam__0(lean_object* v_00_u0398_50_, lean_object* v_i_51_, lean_object* v_v_52_, lean_object* v_inst_53_, lean_object* v_j_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_inc(v_j_54_);
v___x_55_ = lean_apply_2(v_00_u0398_50_, v_i_51_, v_j_54_);
v___x_56_ = lean_apply_1(v_v_52_, v_j_54_);
v___x_57_ = lean_apply_2(v_inst_53_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg___lam__1(lean_object* v_00_u0398_58_, lean_object* v_inst_59_, lean_object* v_toAddMonoid_60_, lean_object* v_inst_61_, lean_object* v_v_62_, lean_object* v_i_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; 
v___f_64_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_relMap___redArg___lam__0), 5, 4);
lean_closure_set(v___f_64_, 0, v_00_u0398_58_);
lean_closure_set(v___f_64_, 1, v_i_63_);
lean_closure_set(v___f_64_, 2, v_v_62_);
lean_closure_set(v___f_64_, 3, v_inst_59_);
v___x_65_ = lp_mathlib_Finset_sum___redArg(v_toAddMonoid_60_, v_inst_61_, v___f_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg___lam__1___boxed(lean_object* v_00_u0398_66_, lean_object* v_inst_67_, lean_object* v_toAddMonoid_68_, lean_object* v_inst_69_, lean_object* v_v_70_, lean_object* v_i_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_Formalism_NG_relMap___redArg___lam__1(v_00_u0398_66_, v_inst_67_, v_toAddMonoid_68_, v_inst_69_, v_v_70_, v_i_71_);
lean_dec_ref(v_toAddMonoid_68_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___redArg(lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_00_u0398_76_){
_start:
{
lean_object* v_toAddMonoid_77_; lean_object* v___f_78_; 
v_toAddMonoid_77_ = lean_ctor_get(v_inst_74_, 0);
lean_inc_ref(v_toAddMonoid_77_);
lean_dec_ref(v_inst_74_);
v___f_78_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_relMap___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_78_, 0, v_00_u0398_76_);
lean_closure_set(v___f_78_, 1, v_inst_75_);
lean_closure_set(v___f_78_, 2, v_toAddMonoid_77_);
lean_closure_set(v___f_78_, 3, v_inst_73_);
return v___f_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap(lean_object* v_R_79_, lean_object* v_inst_80_, lean_object* v_m_81_, lean_object* v_g_82_, lean_object* v_inst_83_, lean_object* v_O_84_, lean_object* v_inst_85_, lean_object* v_M_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_00_u0398_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_tree_Formalism_NG_relMap___redArg(v_inst_83_, v_inst_87_, v_inst_88_, v_00_u0398_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_relMap___boxed(lean_object* v_R_93_, lean_object* v_inst_94_, lean_object* v_m_95_, lean_object* v_g_96_, lean_object* v_inst_97_, lean_object* v_O_98_, lean_object* v_inst_99_, lean_object* v_M_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_00_u0398_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_Formalism_NG_relMap(v_R_93_, v_inst_94_, v_m_95_, v_g_96_, v_inst_97_, v_O_98_, v_inst_99_, v_M_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_00_u0398_105_);
lean_dec(v_inst_103_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_94_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_matQ___redArg(lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_A_109_){
_start:
{
lean_object* v___x_110_; lean_object* v_toSemiring_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v___x_110_ = lp_mathlib_CommRing_toCommMonoid___redArg(v_inst_107_);
v_toSemiring_111_ = lean_ctor_get(v_inst_107_, 0);
v___x_112_ = lean_box(0);
v___x_113_ = lp_mathlib_OreLocalization_oreSetComm(lean_box(0), v___x_110_, v___x_112_);
v___x_114_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_107_);
v___x_115_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_111_);
lean_inc_n(v___x_115_, 2);
lean_inc_ref(v___x_113_);
v___x_116_ = lp_mathlib_OreLocalization_instAddGroupOreLocalization___redArg(v___x_110_, v___x_112_, v___x_113_, v___x_114_, v___x_115_);
lean_inc_ref(v_toSemiring_111_);
v___x_117_ = lp_mathlib_OreLocalization_instModuleOfIsScalarTower___redArg(v_toSemiring_111_, v___x_112_, v___x_113_, v___x_115_, v___x_115_);
v___x_118_ = lean_box(0);
lean_inc(v___x_117_);
v___x_119_ = lp_mathlib_Submodule_Quotient_addCommGroup___redArg(v_inst_107_, v___x_116_, v___x_117_, v___x_118_);
v___f_120_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_Quotient_instSMul_x27___redArg___lam__0), 3, 1);
lean_closure_set(v___f_120_, 0, v___x_117_);
v___x_121_ = lp_tree_Formalism_NG_relMap___redArg(v_inst_108_, v___x_119_, v___f_120_, v_A_109_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_matQ(lean_object* v_O_122_, lean_object* v_inst_123_, lean_object* v_00_u03b9_124_, lean_object* v_inst_125_, lean_object* v_A_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lp_tree_Formalism_NG_matQ___redArg(v_inst_123_, v_inst_125_, v_A_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigMat___redArg(lean_object* v_00_u03c1_128_, lean_object* v_00_u0398_129_, lean_object* v_p_130_, lean_object* v_q_131_){
_start:
{
lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v_fst_134_; lean_object* v_snd_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_fst_132_ = lean_ctor_get(v_p_130_, 0);
lean_inc(v_fst_132_);
v_snd_133_ = lean_ctor_get(v_p_130_, 1);
lean_inc(v_snd_133_);
lean_dec_ref(v_p_130_);
v_fst_134_ = lean_ctor_get(v_q_131_, 0);
lean_inc(v_fst_134_);
v_snd_135_ = lean_ctor_get(v_q_131_, 1);
lean_inc(v_snd_135_);
lean_dec_ref(v_q_131_);
v___x_136_ = lean_apply_2(v_00_u0398_129_, v_fst_132_, v_fst_134_);
v___x_137_ = lean_apply_3(v_00_u03c1_128_, v___x_136_, v_snd_133_, v_snd_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigMat(lean_object* v_R_138_, lean_object* v_O_139_, lean_object* v_inst_140_, lean_object* v_g_141_, lean_object* v_d_142_, lean_object* v_00_u03c1_143_, lean_object* v_00_u0398_144_, lean_object* v_p_145_, lean_object* v_q_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lp_tree_Formalism_NG_bigMat___redArg(v_00_u03c1_143_, v_00_u0398_144_, v_p_145_, v_q_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_bigMat___boxed(lean_object* v_R_148_, lean_object* v_O_149_, lean_object* v_inst_150_, lean_object* v_g_151_, lean_object* v_d_152_, lean_object* v_00_u03c1_153_, lean_object* v_00_u0398_154_, lean_object* v_p_155_, lean_object* v_q_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_tree_Formalism_NG_bigMat(v_R_148_, v_O_149_, v_inst_150_, v_g_151_, v_d_152_, v_00_u03c1_153_, v_00_u0398_154_, v_p_155_, v_q_156_);
lean_dec_ref(v_inst_150_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_congIdeal(lean_object* v_T_158_, lean_object* v_O_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_J_162_, lean_object* v_00_u03c0_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_congIdeal___boxed(lean_object* v_T_165_, lean_object* v_O_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_J_169_, lean_object* v_00_u03c0_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = lp_tree_Formalism_NG_congIdeal(v_T_165_, v_O_166_, v_inst_167_, v_inst_168_, v_J_169_, v_00_u03c0_170_);
lean_dec(v_00_u03c0_170_);
lean_dec_ref(v_inst_168_);
lean_dec_ref(v_inst_167_);
return v_res_171_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CharacterColumnKernels_Statement(uint8_t builtin) {
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
