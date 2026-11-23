// Lean compiler output
// Module: Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HyperbolicPlaceProducts.Statement public import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_conjTranspose___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoidHom_mulLeft___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_conjTranspose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoidHom_mulRight___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_succAbove___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_hermSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_hermSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_Y_2_, lean_object* v_a_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lp_mathlib_Matrix_conjTranspose___redArg(v_inst_1_, v_Y_2_, v_a_3_, v_j_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__1(lean_object* v_Y_6_, lean_object* v_a_7_, lean_object* v_j_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_Y_6_, v_j_8_, v_a_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__2(lean_object* v_S_10_, lean_object* v_j_11_, lean_object* v_j_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_2(v_S_10_, v_j_12_, v_j_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__3(lean_object* v_S_14_, lean_object* v_inst_15_, lean_object* v_toMul_16_, lean_object* v_toAddCommMonoid_17_, lean_object* v___f_18_, lean_object* v_j_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; 
v___f_20_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__2), 3, 2);
lean_closure_set(v___f_20_, 0, v_S_14_);
lean_closure_set(v___f_20_, 1, v_j_19_);
v___x_21_ = lp_mathlib_dotProduct___redArg(v_inst_15_, v_toMul_16_, v_toAddCommMonoid_17_, v___f_18_, v___f_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__3___boxed(lean_object* v_S_22_, lean_object* v_inst_23_, lean_object* v_toMul_24_, lean_object* v_toAddCommMonoid_25_, lean_object* v___f_26_, lean_object* v_j_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__3(v_S_22_, v_inst_23_, v_toMul_24_, v_toAddCommMonoid_25_, v___f_26_, v_j_27_);
lean_dec_ref(v_toAddCommMonoid_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_S_32_, lean_object* v_Y_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_toSemiring_36_; lean_object* v___x_37_; lean_object* v_toMul_38_; lean_object* v_toAdd_39_; lean_object* v_toAddCommMonoid_40_; lean_object* v___f_41_; lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_toSemiring_36_ = lean_ctor_get(v_inst_30_, 0);
lean_inc_ref_n(v_toSemiring_36_, 2);
lean_dec_ref(v_inst_30_);
v___x_37_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_36_);
v_toMul_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc_n(v_toMul_38_, 2);
v_toAdd_39_ = lean_ctor_get(v___x_37_, 1);
lean_inc_n(v_toAdd_39_, 2);
lean_dec_ref(v___x_37_);
v_toAddCommMonoid_40_ = lean_ctor_get(v_toSemiring_36_, 0);
lean_inc_ref_n(v_toAddCommMonoid_40_, 2);
lean_dec_ref(v_toSemiring_36_);
lean_inc_n(v_a_34_, 2);
lean_inc_n(v_Y_33_, 3);
lean_inc(v_inst_31_);
v___f_41_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__0), 4, 3);
lean_closure_set(v___f_41_, 0, v_inst_31_);
lean_closure_set(v___f_41_, 1, v_Y_33_);
lean_closure_set(v___f_41_, 2, v_a_34_);
lean_inc_n(v_a_35_, 2);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__1), 3, 2);
lean_closure_set(v___f_42_, 0, v_Y_33_);
lean_closure_set(v___f_42_, 1, v_a_35_);
lean_inc(v_inst_29_);
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_43_, 0, v_S_32_);
lean_closure_set(v___f_43_, 1, v_inst_29_);
lean_closure_set(v___f_43_, 2, v_toMul_38_);
lean_closure_set(v___f_43_, 3, v_toAddCommMonoid_40_);
lean_closure_set(v___f_43_, 4, v___f_41_);
v___x_44_ = lean_apply_2(v_Y_33_, v_a_34_, v_a_35_);
v___x_45_ = lp_mathlib_Matrix_conjTranspose___redArg(v_inst_31_, v_Y_33_, v_a_34_, v_a_35_);
v___x_46_ = lean_apply_2(v_toAdd_39_, v___x_44_, v___x_45_);
v___x_47_ = lp_mathlib_dotProduct___redArg(v_inst_29_, v_toMul_38_, v_toAddCommMonoid_40_, v___f_43_, v___f_42_);
lean_dec_ref(v_toAddCommMonoid_40_);
v___x_48_ = lean_apply_2(v_toAdd_39_, v___x_46_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi(lean_object* v_n_49_, lean_object* v_R_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_S_54_, lean_object* v_Y_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_Phi___redArg(v_inst_51_, v_inst_52_, v_inst_53_, v_S_54_, v_Y_55_, v_a_56_, v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_hermSub(lean_object* v_F_59_, lean_object* v_K_60_, lean_object* v_n_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_hF_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_hermSub___boxed(lean_object* v_F_69_, lean_object* v_K_70_, lean_object* v_n_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_hF_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_hermSub(v_F_69_, v_K_70_, v_n_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_hF_77_);
lean_dec(v_inst_76_);
lean_dec_ref(v_inst_75_);
lean_dec(v_inst_74_);
lean_dec_ref(v_inst_73_);
lean_dec_ref(v_inst_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___redArg(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_g_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___f_89_; 
v___x_83_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_79_);
v___x_84_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_83_);
v___x_85_ = lp_mathlib_Matrix_nonUnitalNonAssocSemiring___redArg(v___x_84_, v_inst_81_);
lean_inc(v_g_82_);
lean_inc_ref(v___x_85_);
v___x_86_ = lp_mathlib_AddMonoidHom_mulLeft___redArg(v___x_85_, v_g_82_);
v___x_87_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_conjTranspose), 7, 5);
lean_closure_set(v___x_87_, 0, lean_box(0));
lean_closure_set(v___x_87_, 1, lean_box(0));
lean_closure_set(v___x_87_, 2, lean_box(0));
lean_closure_set(v___x_87_, 3, v_inst_80_);
lean_closure_set(v___x_87_, 4, v_g_82_);
v___x_88_ = lp_mathlib_AddMonoidHom_mulRight___redArg(v___x_85_, v___x_87_);
v___f_89_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_89_, 0, v___x_88_);
lean_closure_set(v___f_89_, 1, v___x_86_);
return v___f_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___redArg___boxed(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_g_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___redArg(v_inst_90_, v_inst_91_, v_inst_92_, v_g_93_);
lean_dec_ref(v_inst_90_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap(lean_object* v_F_95_, lean_object* v_K_96_, lean_object* v_n_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_g_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___redArg(v_inst_99_, v_inst_100_, v_inst_102_, v_g_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap___boxed(lean_object* v_F_106_, lean_object* v_K_107_, lean_object* v_n_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_g_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_conjMap(v_F_106_, v_K_107_, v_n_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_inst_114_, v_g_115_);
lean_dec_ref(v_inst_114_);
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_inst_110_);
lean_dec_ref(v_inst_109_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler___redArg(lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_h_120_, lean_object* v_u_121_, lean_object* v_00_u03c3_122_, lean_object* v_00_u03c4_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_toAddMonoid_125_; lean_object* v_toSub_126_; lean_object* v_toAddSemigroup_127_; lean_object* v_toSemiring_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_toMul_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_toAddMonoid_125_ = lean_ctor_get(v_inst_118_, 0);
lean_inc_ref(v_toAddMonoid_125_);
v_toSub_126_ = lean_ctor_get(v_inst_118_, 2);
lean_inc_n(v_toSub_126_, 2);
lean_dec_ref(v_inst_118_);
v_toAddSemigroup_127_ = lean_ctor_get(v_toAddMonoid_125_, 0);
lean_inc(v_toAddSemigroup_127_);
lean_dec_ref(v_toAddMonoid_125_);
v_toSemiring_128_ = lean_ctor_get(v_inst_117_, 0);
lean_inc_ref(v_toSemiring_128_);
lean_dec_ref(v_inst_117_);
lean_inc(v_h_120_);
lean_inc(v_00_u03c3_122_);
lean_inc_n(v_x_124_, 2);
v___x_129_ = lean_apply_2(v_h_120_, v_x_124_, v_00_u03c3_122_);
v___x_130_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_128_);
v_toMul_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_toMul_131_);
lean_dec_ref(v___x_130_);
lean_inc_n(v_inst_119_, 2);
lean_inc_n(v_u_121_, 2);
v___x_132_ = lean_apply_2(v_inst_119_, v___x_129_, v_u_121_);
v___x_133_ = lean_apply_2(v_toSub_126_, v_x_124_, v___x_132_);
v___x_134_ = lean_apply_2(v_h_120_, v_x_124_, v_u_121_);
lean_inc(v___x_134_);
v___x_135_ = lean_apply_2(v_inst_119_, v___x_134_, v_00_u03c3_122_);
v___x_136_ = lean_apply_2(v_toAddSemigroup_127_, v___x_133_, v___x_135_);
v___x_137_ = lean_apply_2(v_toMul_131_, v_00_u03c4_123_, v___x_134_);
v___x_138_ = lean_apply_2(v_inst_119_, v___x_137_, v_u_121_);
v___x_139_ = lean_apply_2(v_toSub_126_, v___x_136_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler(lean_object* v_R_140_, lean_object* v_V_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_h_146_, lean_object* v_u_147_, lean_object* v_00_u03c3_148_, lean_object* v_00_u03c4_149_, lean_object* v_x_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler___redArg(v_inst_142_, v_inst_144_, v_inst_145_, v_h_146_, v_u_147_, v_00_u03c3_148_, v_00_u03c4_149_, v_x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler___boxed(lean_object* v_R_152_, lean_object* v_V_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_h_158_, lean_object* v_u_159_, lean_object* v_00_u03c3_160_, lean_object* v_00_u03c4_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_eichler(v_R_152_, v_V_153_, v_inst_154_, v_inst_155_, v_inst_156_, v_inst_157_, v_h_158_, v_u_159_, v_00_u03c3_160_, v_00_u03c4_161_, v_x_162_);
lean_dec(v_inst_155_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___lam__0(lean_object* v_f_x27_164_, lean_object* v_f_165_, lean_object* v_h_166_, lean_object* v_a_167_, lean_object* v_b_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_apply_1(v_f_x27_164_, v_b_168_);
v___x_170_ = lean_apply_1(v_f_165_, v_a_167_);
v___x_171_ = lean_apply_2(v_h_166_, v___x_169_, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___closed__0(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg(lean_object* v_h_173_, lean_object* v_f_174_, lean_object* v_f_x27_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; lean_object* v_toFun_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___closed__0, &lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___closed__0_once, _init_lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___closed__0);
v_toFun_179_ = lean_ctor_get(v___x_178_, 0);
v___f_180_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg___lam__0), 5, 3);
lean_closure_set(v___f_180_, 0, v_f_x27_175_);
lean_closure_set(v___f_180_, 1, v_f_174_);
lean_closure_set(v___f_180_, 2, v_h_173_);
lean_inc(v_toFun_179_);
v___x_181_ = lean_apply_3(v_toFun_179_, v___f_180_, v_a_176_, v_a_177_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram(lean_object* v_K_182_, lean_object* v_V_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_h_188_, lean_object* v_N_189_, lean_object* v_f_190_, lean_object* v_f_x27_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___redArg(v_h_188_, v_f_190_, v_f_x27_191_, v_a_192_, v_a_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram___boxed(lean_object* v_K_195_, lean_object* v_V_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_h_201_, lean_object* v_N_202_, lean_object* v_f_203_, lean_object* v_f_x27_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_crossGram(v_K_195_, v_V_196_, v_inst_197_, v_inst_198_, v_inst_199_, v_inst_200_, v_h_201_, v_N_202_, v_f_203_, v_f_x27_204_, v_a_205_, v_a_206_);
lean_dec(v_N_202_);
lean_dec(v_inst_200_);
lean_dec_ref(v_inst_199_);
lean_dec(v_inst_198_);
lean_dec_ref(v_inst_197_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg(lean_object* v_inst_209_, lean_object* v_r_210_, lean_object* v_Y_211_, lean_object* v_b_212_){
_start:
{
lean_object* v_toSemiring_213_; lean_object* v___x_214_; lean_object* v_toMonoid_215_; lean_object* v_toMul_216_; lean_object* v_toNPow_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_toNeg_220_; lean_object* v___x_221_; lean_object* v_toAddMonoidWithOne_222_; lean_object* v_toOne_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_272__overap_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_toSemiring_213_ = lean_ctor_get(v_inst_209_, 0);
lean_inc_ref(v_toSemiring_213_);
v___x_214_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_213_);
v_toMonoid_215_ = lean_ctor_get(v_toSemiring_213_, 1);
v_toMul_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_toMul_216_);
lean_dec_ref(v___x_214_);
v_toNPow_217_ = lean_ctor_get(v_toMonoid_215_, 2);
v___x_218_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_209_);
v___x_219_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_218_);
lean_dec_ref(v___x_218_);
v_toNeg_220_ = lean_ctor_get(v___x_219_, 1);
lean_inc(v_toNeg_220_);
lean_dec_ref(v___x_219_);
lean_inc_ref(v_inst_209_);
v___x_221_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_209_);
v_toAddMonoidWithOne_222_ = lean_ctor_get(v___x_221_, 1);
lean_inc_ref(v_toAddMonoidWithOne_222_);
lean_dec_ref(v___x_221_);
v_toOne_223_ = lean_ctor_get(v_toAddMonoidWithOne_222_, 2);
lean_inc(v_toOne_223_);
lean_dec_ref(v_toAddMonoidWithOne_222_);
v___x_224_ = lean_apply_1(v_toNeg_220_, v_toOne_223_);
lean_inc(v_toNPow_217_);
lean_inc(v_b_212_);
v___x_225_ = lean_apply_2(v_toNPow_217_, v_b_212_, v___x_224_);
lean_inc_n(v_r_210_, 2);
v___x_226_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_226_, 0, v_r_210_);
v___x_227_ = l_List_finRange(v_r_210_);
v___x_228_ = ((lean_object*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg___closed__0));
v___x_229_ = lean_alloc_closure((void*)(lp_mathlib_Fin_succAbove___boxed), 3, 2);
lean_closure_set(v___x_229_, 0, v_r_210_);
lean_closure_set(v___x_229_, 1, v_b_212_);
v___x_230_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_230_, 0, lean_box(0));
lean_closure_set(v___x_230_, 1, lean_box(0));
lean_closure_set(v___x_230_, 2, lean_box(0));
lean_closure_set(v___x_230_, 3, lean_box(0));
lean_closure_set(v___x_230_, 4, lean_box(0));
lean_closure_set(v___x_230_, 5, v_Y_211_);
lean_closure_set(v___x_230_, 6, v___x_228_);
lean_closure_set(v___x_230_, 7, v___x_229_);
v___x_272__overap_231_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___x_226_, v___x_227_, v_inst_209_);
v___x_232_ = lean_apply_1(v___x_272__overap_231_, v___x_230_);
v___x_233_ = lean_apply_2(v_toMul_216_, v___x_225_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec(lean_object* v_R_234_, lean_object* v_inst_235_, lean_object* v_r_236_, lean_object* v_Y_237_, lean_object* v_b_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_cofVec___redArg(v_inst_235_, v_r_236_, v_Y_237_, v_b_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__0(lean_object* v_p_240_, lean_object* v___x_241_, lean_object* v_N_242_, lean_object* v_i_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_nat_pow(v_p_240_, v_i_243_);
v___x_245_ = lean_nat_sub(v_p_240_, v___x_241_);
v___x_246_ = lean_nat_mul(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_nat_div(v_N_242_, v___x_246_);
lean_dec(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__0___boxed(lean_object* v_p_248_, lean_object* v___x_249_, lean_object* v_N_250_, lean_object* v_i_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__0(v_p_248_, v___x_249_, v_N_250_, v_i_251_);
lean_dec(v_i_251_);
lean_dec(v_N_250_);
lean_dec(v___x_249_);
lean_dec(v_p_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__1(lean_object* v_N_253_, lean_object* v_p_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = lean_unsigned_to_nat(1u);
lean_inc(v_N_253_);
lean_inc(v_p_254_);
v___f_256_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__0___boxed), 4, 3);
lean_closure_set(v___f_256_, 0, v_p_254_);
lean_closure_set(v___f_256_, 1, v___x_255_);
lean_closure_set(v___f_256_, 2, v_N_253_);
v___x_257_ = lean_nat_add(v_N_253_, v___x_255_);
lean_dec(v_N_253_);
v___x_258_ = l_List_range(v___x_257_);
v___x_259_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_258_, v___f_256_);
v___x_260_ = lean_nat_pow(v_p_254_, v___x_259_);
lean_dec(v___x_259_);
lean_dec(v_p_254_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber(lean_object* v_N_261_){
_start:
{
lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc(v_N_261_);
v___f_262_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_LatticeSumBounds_minkowskiNumber___lam__1), 2, 1);
lean_closure_set(v___f_262_, 0, v_N_261_);
v___x_263_ = lean_unsigned_to_nat(2u);
v___x_264_ = lean_nat_add(v_N_261_, v___x_263_);
lean_dec(v_N_261_);
v___x_265_ = l_List_range(v___x_264_);
v___x_266_ = lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(v___x_265_);
v___x_267_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_266_, v___f_262_);
return v___x_267_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds(uint8_t builtin) {
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
res = initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
