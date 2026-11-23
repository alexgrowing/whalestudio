// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.RatHermLcvTwist
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.ProdFormula
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
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_mulVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cmMax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cmMax___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_DivisionValues_twist___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DivisionValues_twist___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_DivisionValues_twist___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_twist___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_twist(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_twist___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_embSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_embSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_DivisionValues_gramMat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cmMax(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_cmMax___boxed(lean_object* v_K_5_, lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_DivisionValues_cmMax(v_K_5_, v_inst_6_, v_inst_7_);
lean_dec(v_inst_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_twist___redArg(lean_object* v_inst_10_, lean_object* v_00_u03c3_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; 
v___f_12_ = ((lean_object*)(lp_tree_Formalism_DivisionValues_twist___redArg___closed__0));
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v_inst_10_);
lean_closure_set(v___f_13_, 1, v_00_u03c3_11_);
v___f_14_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_14_, 0, v___f_13_);
lean_closure_set(v___f_14_, 1, v___f_12_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_twist(lean_object* v_K_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_00_u03c3_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_DivisionValues_twist___redArg(v_inst_17_, v_00_u03c3_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_twist___boxed(lean_object* v_K_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_00_u03c3_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_DivisionValues_twist(v_K_20_, v_inst_21_, v_inst_22_, v_00_u03c3_23_);
lean_dec_ref(v_inst_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_embSpan(lean_object* v_K_25_, lean_object* v_inst_26_, lean_object* v_n_27_, lean_object* v_00_u03c3_28_, lean_object* v_Z_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_embSpan___boxed(lean_object* v_K_31_, lean_object* v_inst_32_, lean_object* v_n_33_, lean_object* v_00_u03c3_34_, lean_object* v_Z_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_DivisionValues_embSpan(v_K_31_, v_inst_32_, v_n_33_, v_00_u03c3_34_, v_Z_35_);
lean_dec_ref(v_00_u03c3_34_);
lean_dec(v_n_33_);
lean_dec_ref(v_inst_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___lam__0(lean_object* v_toAddCommMonoid_37_, lean_object* v_i_38_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_37_);
return v_toAddCommMonoid_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_39_, lean_object* v_i_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_DivisionValues_comb___redArg___lam__0(v_toAddCommMonoid_39_, v_i_40_);
lean_dec(v_i_40_);
lean_dec_ref(v_toAddCommMonoid_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___lam__1(lean_object* v_x_42_, lean_object* v_z_43_, lean_object* v_toMul_44_, lean_object* v_a_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_inc(v_a_45_);
v___x_47_ = lean_apply_1(v_x_42_, v_a_45_);
v___x_48_ = lean_apply_2(v_z_43_, v_a_45_, v___y_46_);
v___x_49_ = lean_apply_2(v_toMul_44_, v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg(lean_object* v_inst_50_, lean_object* v_d_51_, lean_object* v_z_52_, lean_object* v_x_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_toSemiring_57_; lean_object* v_toAddCommMonoid_58_; lean_object* v___x_59_; lean_object* v_toMul_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_24__overap_65_; lean_object* v___x_66_; 
v___x_55_ = lp_mathlib_Field_toSemifield___redArg(v_inst_50_);
v___x_56_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_55_);
v_toSemiring_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc_ref(v_toSemiring_57_);
lean_dec_ref(v___x_56_);
v_toAddCommMonoid_58_ = lean_ctor_get(v_toSemiring_57_, 0);
lean_inc_ref(v_toAddCommMonoid_58_);
v___x_59_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_57_);
v_toMul_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_toMul_60_);
lean_dec_ref(v___x_59_);
v___f_61_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_comb___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_61_, 0, v_toAddCommMonoid_58_);
v___f_62_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_comb___redArg___lam__1), 5, 3);
lean_closure_set(v___f_62_, 0, v_x_53_);
lean_closure_set(v___f_62_, 1, v_z_52_);
lean_closure_set(v___f_62_, 2, v_toMul_60_);
v___x_63_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_61_);
v___x_64_ = l_List_finRange(v_d_51_);
v___x_24__overap_65_ = lp_mathlib_Finset_sum___redArg(v___x_63_, v___x_64_, v___f_62_);
lean_dec_ref(v___x_63_);
v___x_66_ = lean_apply_1(v___x_24__overap_65_, v_a_54_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___redArg___boxed(lean_object* v_inst_67_, lean_object* v_d_68_, lean_object* v_z_69_, lean_object* v_x_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_Formalism_DivisionValues_comb___redArg(v_inst_67_, v_d_68_, v_z_69_, v_x_70_, v_a_71_);
lean_dec_ref(v_inst_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb(lean_object* v_K_73_, lean_object* v_inst_74_, lean_object* v_n_75_, lean_object* v_d_76_, lean_object* v_z_77_, lean_object* v_x_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_tree_Formalism_DivisionValues_comb___redArg(v_inst_74_, v_d_76_, v_z_77_, v_x_78_, v_a_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_comb___boxed(lean_object* v_K_81_, lean_object* v_inst_82_, lean_object* v_n_83_, lean_object* v_d_84_, lean_object* v_z_85_, lean_object* v_x_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_tree_Formalism_DivisionValues_comb(v_K_81_, v_inst_82_, v_n_83_, v_d_84_, v_z_85_, v_x_86_, v_a_87_);
lean_dec(v_n_83_);
lean_dec_ref(v_inst_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__0(lean_object* v_z_89_, lean_object* v_a_90_, lean_object* v_inst_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_apply_2(v_z_89_, v_a_90_, v___y_92_);
v___x_94_ = lean_apply_1(v_inst_91_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__1(lean_object* v_z_95_, lean_object* v_inst_96_, lean_object* v___x_97_, lean_object* v___x_98_, lean_object* v_H_99_, lean_object* v_toMul_100_, lean_object* v_toAddCommMonoid_101_, lean_object* v_a_102_, lean_object* v_b_103_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc(v_z_95_);
v___f_104_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__0), 4, 3);
lean_closure_set(v___f_104_, 0, v_z_95_);
lean_closure_set(v___f_104_, 1, v_a_102_);
lean_closure_set(v___f_104_, 2, v_inst_96_);
v___x_105_ = lean_apply_1(v_z_95_, v_b_103_);
lean_inc(v___x_98_);
v___x_106_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_mulVec), 8, 7);
lean_closure_set(v___x_106_, 0, lean_box(0));
lean_closure_set(v___x_106_, 1, lean_box(0));
lean_closure_set(v___x_106_, 2, lean_box(0));
lean_closure_set(v___x_106_, 3, v___x_97_);
lean_closure_set(v___x_106_, 4, v___x_98_);
lean_closure_set(v___x_106_, 5, v_H_99_);
lean_closure_set(v___x_106_, 6, v___x_105_);
v___x_107_ = lp_mathlib_dotProduct___redArg(v___x_98_, v_toMul_100_, v_toAddCommMonoid_101_, v___f_104_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__1___boxed(lean_object* v_z_108_, lean_object* v_inst_109_, lean_object* v___x_110_, lean_object* v___x_111_, lean_object* v_H_112_, lean_object* v_toMul_113_, lean_object* v_toAddCommMonoid_114_, lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__1(v_z_108_, v_inst_109_, v___x_110_, v___x_111_, v_H_112_, v_toMul_113_, v_toAddCommMonoid_114_, v_a_115_, v_b_116_);
lean_dec_ref(v_toAddCommMonoid_114_);
return v_res_117_;
}
}
static lean_object* _init_lp_tree_Formalism_DivisionValues_gramMat___redArg___closed__0(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg(lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_n_121_, lean_object* v_H_122_, lean_object* v_z_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v_toSemiring_128_; lean_object* v___x_129_; lean_object* v_toMul_130_; lean_object* v_toAddCommMonoid_131_; lean_object* v_toCommRing_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_toFun_136_; lean_object* v___x_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v___x_126_ = lp_mathlib_Field_toSemifield___redArg(v_inst_119_);
v___x_127_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_126_);
v_toSemiring_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc_ref_n(v_toSemiring_128_, 2);
lean_dec_ref(v___x_127_);
v___x_129_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_128_);
v_toMul_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_toMul_130_);
lean_dec_ref(v___x_129_);
v_toAddCommMonoid_131_ = lean_ctor_get(v_toSemiring_128_, 0);
lean_inc_ref(v_toAddCommMonoid_131_);
lean_dec_ref(v_toSemiring_128_);
v_toCommRing_132_ = lean_ctor_get(v_inst_119_, 0);
v___x_133_ = lean_obj_once(&lp_tree_Formalism_DivisionValues_gramMat___redArg___closed__0, &lp_tree_Formalism_DivisionValues_gramMat___redArg___closed__0_once, _init_lp_tree_Formalism_DivisionValues_gramMat___redArg___closed__0);
v___x_134_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_132_);
v___x_135_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_134_);
v_toFun_136_ = lean_ctor_get(v___x_133_, 0);
v___x_137_ = l_List_finRange(v_n_121_);
v___f_138_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_gramMat___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_138_, 0, v_z_123_);
lean_closure_set(v___f_138_, 1, v_inst_120_);
lean_closure_set(v___f_138_, 2, v___x_135_);
lean_closure_set(v___f_138_, 3, v___x_137_);
lean_closure_set(v___f_138_, 4, v_H_122_);
lean_closure_set(v___f_138_, 5, v_toMul_130_);
lean_closure_set(v___f_138_, 6, v_toAddCommMonoid_131_);
lean_inc(v_toFun_136_);
v___x_139_ = lean_apply_3(v_toFun_136_, v___f_138_, v_a_124_, v_a_125_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___redArg___boxed(lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_n_142_, lean_object* v_H_143_, lean_object* v_z_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_tree_Formalism_DivisionValues_gramMat___redArg(v_inst_140_, v_inst_141_, v_n_142_, v_H_143_, v_z_144_, v_a_145_, v_a_146_);
lean_dec_ref(v_inst_140_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat(lean_object* v_K_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_n_151_, lean_object* v_d_152_, lean_object* v_H_153_, lean_object* v_z_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lp_tree_Formalism_DivisionValues_gramMat___redArg(v_inst_149_, v_inst_150_, v_n_151_, v_H_153_, v_z_154_, v_a_155_, v_a_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_gramMat___boxed(lean_object* v_K_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_n_161_, lean_object* v_d_162_, lean_object* v_H_163_, lean_object* v_z_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lp_tree_Formalism_DivisionValues_gramMat(v_K_158_, v_inst_159_, v_inst_160_, v_n_161_, v_d_162_, v_H_163_, v_z_164_, v_a_165_, v_a_166_);
lean_dec(v_d_162_);
lean_dec_ref(v_inst_159_);
return v_res_167_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_RatHermLcvTwist(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
