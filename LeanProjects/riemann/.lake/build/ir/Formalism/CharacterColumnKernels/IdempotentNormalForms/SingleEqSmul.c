// Lean compiler output
// Module: Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
// Imports: public import Init public meta import Init public import Formalism.CharacterColumnKernels.Statement
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
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Submodule_liftQ___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Pi_single___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_ofVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_ofVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_ofVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg___lam__0(lean_object* v_w_1_, lean_object* v_v_2_, lean_object* v_inst_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_j_4_);
v___x_5_ = lean_apply_1(v_w_1_, v_j_4_);
v___x_6_ = lean_apply_1(v_v_2_, v_j_4_);
v___x_7_ = lean_apply_2(v_inst_3_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg___lam__1(lean_object* v_v_8_, lean_object* v_inst_9_, lean_object* v_toAddMonoid_10_, lean_object* v_inst_11_, lean_object* v_w_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; 
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_combo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_13_, 0, v_w_12_);
lean_closure_set(v___f_13_, 1, v_v_8_);
lean_closure_set(v___f_13_, 2, v_inst_9_);
v___x_14_ = lp_mathlib_Finset_sum___redArg(v_toAddMonoid_10_, v_inst_11_, v___f_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg___lam__1___boxed(lean_object* v_v_15_, lean_object* v_inst_16_, lean_object* v_toAddMonoid_17_, lean_object* v_inst_18_, lean_object* v_w_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_NG_combo___redArg___lam__1(v_v_15_, v_inst_16_, v_toAddMonoid_17_, v_inst_18_, v_w_19_);
lean_dec_ref(v_toAddMonoid_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___redArg(lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_v_24_){
_start:
{
lean_object* v_toAddMonoid_25_; lean_object* v___f_26_; 
v_toAddMonoid_25_ = lean_ctor_get(v_inst_21_, 0);
lean_inc_ref(v_toAddMonoid_25_);
lean_dec_ref(v_inst_21_);
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_combo___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_26_, 0, v_v_24_);
lean_closure_set(v___f_26_, 1, v_inst_22_);
lean_closure_set(v___f_26_, 2, v_toAddMonoid_25_);
lean_closure_set(v___f_26_, 3, v_inst_23_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo(lean_object* v_R_27_, lean_object* v_M_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_g_32_, lean_object* v_inst_33_, lean_object* v_v_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_tree_Formalism_NG_combo___redArg(v_inst_30_, v_inst_31_, v_inst_33_, v_v_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_combo___boxed(lean_object* v_R_36_, lean_object* v_M_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_g_41_, lean_object* v_inst_42_, lean_object* v_v_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_NG_combo(v_R_36_, v_M_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_g_41_, v_inst_42_, v_v_43_);
lean_dec_ref(v_inst_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___redArg___lam__0(lean_object* v_toZero_45_, lean_object* v_i_46_){
_start:
{
lean_inc(v_toZero_45_);
return v_toZero_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___redArg___lam__0___boxed(lean_object* v_toZero_47_, lean_object* v_i_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_NG_toVec___redArg___lam__0(v_toZero_47_, v_i_48_);
lean_dec(v_i_48_);
lean_dec(v_toZero_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_00_u03c6_52_, lean_object* v_j_53_){
_start:
{
lean_object* v_toSemiring_54_; lean_object* v___x_55_; lean_object* v_toZero_56_; lean_object* v___x_57_; lean_object* v_toAddMonoidWithOne_58_; lean_object* v_toOne_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_toSemiring_54_ = lean_ctor_get(v_inst_50_, 0);
lean_inc_ref(v_toSemiring_54_);
v___x_55_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_54_);
v_toZero_56_ = lean_ctor_get(v___x_55_, 1);
lean_inc(v_toZero_56_);
lean_dec_ref(v___x_55_);
v___x_57_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_50_);
v_toAddMonoidWithOne_58_ = lean_ctor_get(v___x_57_, 1);
lean_inc_ref(v_toAddMonoidWithOne_58_);
lean_dec_ref(v___x_57_);
v_toOne_59_ = lean_ctor_get(v_toAddMonoidWithOne_58_, 2);
lean_inc(v_toOne_59_);
lean_dec_ref(v_toAddMonoidWithOne_58_);
v___f_60_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_toVec___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_60_, 0, v_toZero_56_);
v___x_61_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_61_, 0, lean_box(0));
lean_closure_set(v___x_61_, 1, lean_box(0));
lean_closure_set(v___x_61_, 2, v___f_60_);
lean_closure_set(v___x_61_, 3, v_inst_51_);
lean_closure_set(v___x_61_, 4, v_j_53_);
lean_closure_set(v___x_61_, 5, v_toOne_59_);
v___x_62_ = lean_apply_1(v_00_u03c6_52_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec(lean_object* v_R_63_, lean_object* v_M_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_m_68_, lean_object* v_g_69_, lean_object* v_inst_70_, lean_object* v_00_u0398_71_, lean_object* v_00_u03c6_72_, lean_object* v_j_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_NG_toVec___redArg(v_inst_65_, v_inst_70_, v_00_u03c6_72_, v_j_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_toVec___boxed(lean_object* v_R_75_, lean_object* v_M_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_m_80_, lean_object* v_g_81_, lean_object* v_inst_82_, lean_object* v_00_u0398_83_, lean_object* v_00_u03c6_84_, lean_object* v_j_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_NG_toVec(v_R_75_, v_M_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_m_80_, v_g_81_, v_inst_82_, v_00_u0398_83_, v_00_u03c6_84_, v_j_85_);
lean_dec(v_00_u0398_83_);
lean_dec(v_inst_79_);
lean_dec_ref(v_inst_78_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_ofVec___redArg(lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_v_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lp_tree_Formalism_NG_combo___redArg(v_inst_87_, v_inst_88_, v_inst_89_, v_v_90_);
v___x_92_ = lp_mathlib_Submodule_liftQ___redArg(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_ofVec(lean_object* v_R_93_, lean_object* v_O_94_, lean_object* v_M_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_m_102_, lean_object* v_g_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_00_u0398_107_, lean_object* v_v_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lp_tree_Formalism_NG_ofVec___redArg(v_inst_98_, v_inst_99_, v_inst_105_, v_v_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_ofVec___boxed(lean_object* v_R_110_, lean_object* v_O_111_, lean_object* v_M_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_m_119_, lean_object* v_g_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_00_u0398_124_, lean_object* v_v_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_tree_Formalism_NG_ofVec(v_R_110_, v_O_111_, v_M_112_, v_inst_113_, v_inst_114_, v_inst_115_, v_inst_116_, v_inst_117_, v_inst_118_, v_m_119_, v_g_120_, v_inst_121_, v_inst_122_, v_inst_123_, v_00_u0398_124_, v_v_125_);
lean_dec(v_00_u0398_124_);
lean_dec_ref(v_inst_123_);
lean_dec(v_inst_121_);
lean_dec(v_inst_117_);
lean_dec_ref(v_inst_114_);
lean_dec_ref(v_inst_113_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___redArg___lam__0(lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_00_u03c6_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lp_tree_Formalism_NG_toVec___redArg(v_inst_127_, v_inst_128_, v_00_u03c6_129_, v___y_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___redArg___lam__1(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_v_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_87__overap_137_; lean_object* v___x_138_; 
v___x_87__overap_137_ = lp_tree_Formalism_NG_ofVec___redArg(v_inst_132_, v_inst_133_, v_inst_134_, v_v_135_);
v___x_138_ = lean_apply_1(v___x_87__overap_137_, v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___redArg(lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v___f_144_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_homEquiv___redArg___lam__0), 4, 2);
lean_closure_set(v___f_144_, 0, v_inst_139_);
lean_closure_set(v___f_144_, 1, v_inst_143_);
v___f_145_ = lean_alloc_closure((void*)(lp_tree_Formalism_NG_homEquiv___redArg___lam__1), 5, 3);
lean_closure_set(v___f_145_, 0, v_inst_140_);
lean_closure_set(v___f_145_, 1, v_inst_141_);
lean_closure_set(v___f_145_, 2, v_inst_142_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___f_144_);
lean_ctor_set(v___x_146_, 1, v___f_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv(lean_object* v_R_147_, lean_object* v_O_148_, lean_object* v_M_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_m_156_, lean_object* v_g_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_00_u0398_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lp_tree_Formalism_NG_homEquiv___redArg(v_inst_150_, v_inst_152_, v_inst_153_, v_inst_159_, v_inst_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_NG_homEquiv___boxed(lean_object* v_R_163_, lean_object* v_O_164_, lean_object* v_M_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_m_172_, lean_object* v_g_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_00_u0398_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_tree_Formalism_NG_homEquiv(v_R_163_, v_O_164_, v_M_165_, v_inst_166_, v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_inst_171_, v_m_172_, v_g_173_, v_inst_174_, v_inst_175_, v_inst_176_, v_00_u0398_177_);
lean_dec(v_00_u0398_177_);
lean_dec(v_inst_174_);
lean_dec(v_inst_170_);
lean_dec_ref(v_inst_167_);
return v_res_178_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CharacterColumnKernels_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CharacterColumnKernels_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
