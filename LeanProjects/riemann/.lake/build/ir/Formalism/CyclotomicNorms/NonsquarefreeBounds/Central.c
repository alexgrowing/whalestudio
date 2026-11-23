// Lean compiler output
// Module: Formalism.CyclotomicNorms.NonsquarefreeBounds.Central
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.StatementA
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Fin_insertNth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___redArg(lean_object* v_i_1_, lean_object* v_a_2_, lean_object* v_y_3_, lean_object* v_k_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_k_4_, v_i_1_);
if (v___x_5_ == 0)
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_eq(v_k_4_, v_i_1_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_sub(v_k_4_, v___x_7_);
lean_dec(v_k_4_);
v___x_9_ = lean_apply_1(v_y_3_, v___x_8_);
return v___x_9_;
}
else
{
lean_dec(v_k_4_);
lean_dec(v_y_3_);
lean_inc(v_a_2_);
return v_a_2_;
}
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_1(v_y_3_, v_k_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___redArg___boxed(lean_object* v_i_11_, lean_object* v_a_12_, lean_object* v_y_13_, lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___redArg(v_i_11_, v_a_12_, v_y_13_, v_k_14_);
lean_dec(v_a_12_);
lean_dec(v_i_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN(lean_object* v_G_16_, lean_object* v_i_17_, lean_object* v_a_18_, lean_object* v_y_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___redArg(v_i_17_, v_a_18_, v_y_19_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN___boxed(lean_object* v_G_22_, lean_object* v_i_23_, lean_object* v_a_24_, lean_object* v_y_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_insN(v_G_22_, v_i_23_, v_a_24_, v_y_25_, v_k_26_);
lean_dec(v_a_24_);
lean_dec(v_i_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___redArg(lean_object* v_inst_28_, lean_object* v_j_29_, lean_object* v_y_30_, lean_object* v_k_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = lean_nat_dec_lt(v_k_31_, v_j_29_);
if (v___x_32_ == 0)
{
uint8_t v___x_33_; 
v___x_33_ = lean_nat_dec_eq(v_k_31_, v_j_29_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = lean_nat_add(v_k_31_, v___x_34_);
lean_dec(v_k_31_);
v___x_36_ = lean_apply_1(v_y_30_, v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_toMonoid_37_; lean_object* v___x_38_; lean_object* v_toMul_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_toMonoid_37_ = lean_ctor_get(v_inst_28_, 0);
v___x_38_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_37_);
v_toMul_39_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_toMul_39_);
lean_dec_ref(v___x_38_);
lean_inc(v_y_30_);
lean_inc(v_k_31_);
v___x_40_ = lean_apply_1(v_y_30_, v_k_31_);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_k_31_, v___x_41_);
lean_dec(v_k_31_);
v___x_43_ = lean_apply_1(v_y_30_, v___x_42_);
v___x_44_ = lean_apply_2(v_toMul_39_, v___x_40_, v___x_43_);
return v___x_44_;
}
}
else
{
lean_object* v___x_45_; 
v___x_45_ = lean_apply_1(v_y_30_, v_k_31_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___redArg___boxed(lean_object* v_inst_46_, lean_object* v_j_47_, lean_object* v_y_48_, lean_object* v_k_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___redArg(v_inst_46_, v_j_47_, v_y_48_, v_k_49_);
lean_dec(v_j_47_);
lean_dec_ref(v_inst_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN(lean_object* v_G_51_, lean_object* v_inst_52_, lean_object* v_j_53_, lean_object* v_y_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___redArg(v_inst_52_, v_j_53_, v_y_54_, v_k_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN___boxed(lean_object* v_G_57_, lean_object* v_inst_58_, lean_object* v_j_59_, lean_object* v_y_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_contrN(v_G_57_, v_inst_58_, v_j_59_, v_y_60_, v_k_61_);
lean_dec(v_j_59_);
lean_dec_ref(v_inst_58_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___redArg(lean_object* v_inst_63_, lean_object* v_m_64_, lean_object* v_x_65_, lean_object* v_k_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_nat_dec_lt(v_k_66_, v_m_64_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v_toOne_69_; 
lean_dec(v_k_66_);
lean_dec(v_x_65_);
v___x_68_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_63_);
v_toOne_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_toOne_69_);
lean_dec_ref(v___x_68_);
return v_toOne_69_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = lean_apply_1(v_x_65_, v_k_66_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___redArg___boxed(lean_object* v_inst_71_, lean_object* v_m_72_, lean_object* v_x_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___redArg(v_inst_71_, v_m_72_, v_x_73_, v_k_74_);
lean_dec(v_m_72_);
lean_dec_ref(v_inst_71_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN(lean_object* v_G_76_, lean_object* v_inst_77_, lean_object* v_m_78_, lean_object* v_x_79_, lean_object* v_k_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___redArg(v_inst_77_, v_m_78_, v_x_79_, v_k_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN___boxed(lean_object* v_G_82_, lean_object* v_inst_83_, lean_object* v_m_84_, lean_object* v_x_85_, lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_extN(v_G_82_, v_inst_83_, v_m_84_, v_x_85_, v_k_86_);
lean_dec(v_m_84_);
lean_dec_ref(v_inst_83_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg___lam__0(lean_object* v_toNeg_88_, lean_object* v_toOne_89_, lean_object* v_toNPow_90_, lean_object* v_n_91_, lean_object* v_z_92_, lean_object* v_x_93_, lean_object* v_f_94_, lean_object* v_inst_95_, lean_object* v_i_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = lean_apply_1(v_toNeg_88_, v_toOne_89_);
lean_inc(v_i_96_);
v___x_98_ = lean_apply_2(v_toNPow_90_, v_i_96_, v___x_97_);
v___x_99_ = lean_alloc_closure((void*)(lp_mathlib_Fin_insertNth___boxed), 6, 5);
lean_closure_set(v___x_99_, 0, v_n_91_);
lean_closure_set(v___x_99_, 1, lean_box(0));
lean_closure_set(v___x_99_, 2, v_i_96_);
lean_closure_set(v___x_99_, 3, v_z_92_);
lean_closure_set(v___x_99_, 4, v_x_93_);
v___x_100_ = lean_apply_1(v_f_94_, v___x_99_);
v___x_101_ = lean_apply_2(v_inst_95_, v___x_98_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg(lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_n_105_, lean_object* v_z_106_, lean_object* v_f_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_toSemiring_109_; lean_object* v_toMonoid_110_; lean_object* v_toAddMonoid_111_; lean_object* v_toNPow_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_toNeg_115_; lean_object* v___x_116_; lean_object* v_toAddMonoidWithOne_117_; lean_object* v_toOne_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___f_122_; lean_object* v___x_123_; 
v_toSemiring_109_ = lean_ctor_get(v_inst_103_, 0);
v_toMonoid_110_ = lean_ctor_get(v_toSemiring_109_, 1);
v_toAddMonoid_111_ = lean_ctor_get(v_inst_102_, 0);
v_toNPow_112_ = lean_ctor_get(v_toMonoid_110_, 2);
lean_inc(v_toNPow_112_);
v___x_113_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_103_);
v___x_114_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_113_);
lean_dec_ref(v___x_113_);
v_toNeg_115_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_toNeg_115_);
lean_dec_ref(v___x_114_);
v___x_116_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_103_);
v_toAddMonoidWithOne_117_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_toAddMonoidWithOne_117_);
lean_dec_ref(v___x_116_);
v_toOne_118_ = lean_ctor_get(v_toAddMonoidWithOne_117_, 2);
lean_inc(v_toOne_118_);
lean_dec_ref(v_toAddMonoidWithOne_117_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_n_105_, v___x_119_);
v___x_121_ = l_List_finRange(v___x_120_);
v___f_122_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg___lam__0), 9, 8);
lean_closure_set(v___f_122_, 0, v_toNeg_115_);
lean_closure_set(v___f_122_, 1, v_toOne_118_);
lean_closure_set(v___f_122_, 2, v_toNPow_112_);
lean_closure_set(v___f_122_, 3, v_n_105_);
lean_closure_set(v___f_122_, 4, v_z_106_);
lean_closure_set(v___f_122_, 5, v_x_108_);
lean_closure_set(v___f_122_, 6, v_f_107_);
lean_closure_set(v___f_122_, 7, v_inst_104_);
v___x_123_ = lp_mathlib_Finset_sum___redArg(v_toAddMonoid_111_, v___x_121_, v___f_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg___boxed(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_n_127_, lean_object* v_z_128_, lean_object* v_f_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg(v_inst_124_, v_inst_125_, v_inst_126_, v_n_127_, v_z_128_, v_f_129_, v_x_130_);
lean_dec_ref(v_inst_124_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism(lean_object* v_G_132_, lean_object* v_W_133_, lean_object* v_inst_134_, lean_object* v_R_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_n_138_, lean_object* v_z_139_, lean_object* v_f_140_, lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___redArg(v_inst_134_, v_inst_136_, v_inst_137_, v_n_138_, v_z_139_, v_f_140_, v_x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism___boxed(lean_object* v_G_143_, lean_object* v_W_144_, lean_object* v_inst_145_, lean_object* v_R_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_n_149_, lean_object* v_z_150_, lean_object* v_f_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_tree_Formalism_CyclotomicNorms_CentralScalarSequence_prism(v_G_143_, v_W_144_, v_inst_145_, v_R_146_, v_inst_147_, v_inst_148_, v_n_149_, v_z_150_, v_f_151_, v_x_152_);
lean_dec_ref(v_inst_145_);
return v_res_153_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
