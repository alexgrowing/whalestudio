// Lean compiler output
// Module: Formalism.GL3MeanSquares.FourierTransformKernelSurjective
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LogVandermondeBounds.GaussOperatorProductFormula
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_vecMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Int_cast___at___00CongruenceSubgroup_Gamma0Map_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_fintype___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__0 = (const lean_object*)&lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__0_value;
static const lean_closure_object lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__0_value)} };
static const lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__1 = (const lean_object*)&lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_Uc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_Uc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___redArg___lam__0(lean_object* v_fW_1_, lean_object* v_x_2_, lean_object* v_j_3_, lean_object* v_q_4_, lean_object* v_toMul_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc(v_i_6_);
v___x_7_ = lean_apply_1(v_fW_1_, v_i_6_);
v___x_8_ = lean_apply_2(v_x_2_, v_i_6_, v_j_3_);
v___x_9_ = lp_mathlib_Int_cast___at___00CongruenceSubgroup_Gamma0Map_spec__0(v_q_4_, v___x_8_);
v___x_10_ = lean_apply_2(v_toMul_5_, v___x_7_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0_spec__0___lam__0(lean_object* v_toAdd_11_, lean_object* v_x1_12_, lean_object* v_x2_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_toAdd_11_, v_x1_12_, v_x2_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0_spec__0(lean_object* v_q_15_, lean_object* v_s_16_){
_start:
{
lean_object* v___x_17_; lean_object* v_toSemiring_18_; lean_object* v_toAddCommMonoid_19_; lean_object* v___x_20_; lean_object* v_toZero_21_; lean_object* v_toAdd_22_; lean_object* v___f_23_; lean_object* v___x_24_; 
v___x_17_ = lp_mathlib_ZMod_commRing(v_q_15_);
v_toSemiring_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_toSemiring_18_);
lean_dec_ref(v___x_17_);
v_toAddCommMonoid_19_ = lean_ctor_get(v_toSemiring_18_, 0);
lean_inc_ref(v_toAddCommMonoid_19_);
lean_dec_ref(v_toSemiring_18_);
v___x_20_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_19_);
lean_dec_ref(v_toAddCommMonoid_19_);
v_toZero_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_toZero_21_);
v_toAdd_22_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_toAdd_22_);
lean_dec_ref(v___x_20_);
v___f_23_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_23_, 0, v_toAdd_22_);
v___x_24_ = l_List_foldrTR___redArg(v___f_23_, v_toZero_21_, v_s_16_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0___redArg(lean_object* v_q_25_, lean_object* v_s_26_, lean_object* v_f_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lp_mathlib_Multiset_map___redArg(v_f_27_, v_s_26_);
v___x_29_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0_spec__0(v_q_25_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___redArg(lean_object* v_q_30_, lean_object* v_n_x27_31_, lean_object* v_fW_32_, lean_object* v_x_33_, lean_object* v_j_34_){
_start:
{
lean_object* v___x_35_; lean_object* v_toSemiring_36_; lean_object* v___x_37_; lean_object* v_toMul_38_; lean_object* v___x_39_; lean_object* v___f_40_; lean_object* v___x_41_; 
lean_inc_n(v_q_30_, 2);
v___x_35_ = lp_mathlib_ZMod_commRing(v_q_30_);
v_toSemiring_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_toSemiring_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_36_);
v_toMul_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_toMul_38_);
lean_dec_ref(v___x_37_);
v___x_39_ = l_List_finRange(v_n_x27_31_);
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___redArg___lam__0), 6, 5);
lean_closure_set(v___f_40_, 0, v_fW_32_);
lean_closure_set(v___f_40_, 1, v_x_33_);
lean_closure_set(v___f_40_, 2, v_j_34_);
lean_closure_set(v___f_40_, 3, v_q_30_);
lean_closure_set(v___f_40_, 4, v_toMul_38_);
v___x_41_ = lp_tree_Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0___redArg(v_q_30_, v___x_39_, v___f_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF(lean_object* v_q_42_, lean_object* v_n_43_, lean_object* v_n_x27_44_, lean_object* v_fW_45_, lean_object* v_x_46_, lean_object* v_j_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___redArg(v_q_42_, v_n_x27_44_, v_fW_45_, v_x_46_, v_j_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF___boxed(lean_object* v_q_49_, lean_object* v_n_50_, lean_object* v_n_x27_51_, lean_object* v_fW_52_, lean_object* v_x_53_, lean_object* v_j_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_compF(v_q_49_, v_n_50_, v_n_x27_51_, v_fW_52_, v_x_53_, v_j_54_);
lean_dec(v_n_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0(lean_object* v_q_56_, lean_object* v_00_u03b9_57_, lean_object* v_s_58_, lean_object* v_f_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_tree_Finset_sum___at___00Formalism_HermitianLattices_LocalLatticeBases_compF_spec__0___redArg(v_q_56_, v_s_58_, v_f_59_);
return v___x_60_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__0(lean_object* v_q_61_, lean_object* v_a_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lp_mathlib_ZMod_decidableEq(v_q_61_, v___y_63_, v___y_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__0___boxed(lean_object* v_q_66_, lean_object* v_a_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__0(v_q_66_, v_a_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec(v___y_68_);
lean_dec(v_a_67_);
lean_dec(v_q_66_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__1(lean_object* v___x_72_, lean_object* v_x_73_){
_start:
{
lean_inc(v___x_72_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__1___boxed(lean_object* v___x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__1(v___x_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v___x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__2(lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v___f_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_mathlib_Fintype_piFinset___redArg(v___x_77_, v___x_78_, v___f_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__2___boxed(lean_object* v___x_82_, lean_object* v___x_83_, lean_object* v___f_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__2(v___x_82_, v___x_83_, v___f_84_, v_x_85_);
lean_dec(v_x_85_);
return v_res_86_;
}
}
static lean_object* _init_lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_88_ = lp_mathlib_Complex_ofReal(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4(lean_object* v___x_89_, lean_object* v___x_90_, lean_object* v_fW_91_, lean_object* v_x_92_, lean_object* v___f_93_, lean_object* v___x_94_, lean_object* v_ph_95_, lean_object* v_f_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_vecMul), 8, 7);
lean_closure_set(v___x_97_, 0, lean_box(0));
lean_closure_set(v___x_97_, 1, lean_box(0));
lean_closure_set(v___x_97_, 2, lean_box(0));
lean_closure_set(v___x_97_, 3, v___x_89_);
lean_closure_set(v___x_97_, 4, v___x_90_);
lean_closure_set(v___x_97_, 5, v_fW_91_);
lean_closure_set(v___x_97_, 6, v_x_92_);
lean_inc(v_f_96_);
v___x_98_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_93_, v___x_94_, v___x_97_, v_f_96_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
lean_dec(v_f_96_);
lean_dec_ref(v_ph_95_);
v___x_99_ = lean_obj_once(&lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4___closed__0, &lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4___closed__0_once, _init_lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4___closed__0);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_apply_1(v_ph_95_, v_f_96_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3(lean_object* v_w_104_, lean_object* v___x_105_, lean_object* v___x_106_, lean_object* v_fW_107_, lean_object* v___f_108_, lean_object* v___x_109_, lean_object* v_ph_110_, lean_object* v___x_111_, lean_object* v___f_112_, lean_object* v___x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; lean_object* v_re_116_; lean_object* v_im_117_; lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
lean_inc(v_x_114_);
v___x_115_ = lean_apply_1(v_w_104_, v_x_114_);
v_re_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_re_116_);
v_im_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc(v_im_117_);
lean_dec_ref(v___x_115_);
lean_inc(v___x_109_);
v___f_118_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__4), 8, 7);
lean_closure_set(v___f_118_, 0, v___x_105_);
lean_closure_set(v___f_118_, 1, v___x_106_);
lean_closure_set(v___f_118_, 2, v_fW_107_);
lean_closure_set(v___f_118_, 3, v_x_114_);
lean_closure_set(v___f_118_, 4, v___f_108_);
lean_closure_set(v___f_118_, 5, v___x_109_);
lean_closure_set(v___f_118_, 6, v_ph_110_);
v___x_119_ = lp_mathlib_Fintype_piFinset___redArg(v___x_111_, v___x_109_, v___f_112_);
v___x_120_ = lp_mathlib_Finset_sum___redArg(v___x_113_, v___x_119_, v___f_118_);
v___f_121_ = ((lean_object*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___closed__1));
v___x_122_ = lp_mathlib_Complex_mulAux___redArg(v___f_121_, v_re_116_, v_im_117_, v___x_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___boxed(lean_object* v_w_123_, lean_object* v___x_124_, lean_object* v___x_125_, lean_object* v_fW_126_, lean_object* v___f_127_, lean_object* v___x_128_, lean_object* v_ph_129_, lean_object* v___x_130_, lean_object* v___f_131_, lean_object* v___x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3(v_w_123_, v___x_124_, v___x_125_, v_fW_126_, v___f_127_, v___x_128_, v_ph_129_, v___x_130_, v___f_131_, v___x_132_, v_x_133_);
lean_dec_ref(v___x_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg(lean_object* v_q_135_, lean_object* v_n_136_, lean_object* v_n_x27_137_, lean_object* v_w_138_, lean_object* v_ph_139_, lean_object* v_fW_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___f_154_; lean_object* v___x_155_; 
lean_inc(v_q_135_);
v___f_141_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_141_, 0, v_q_135_);
v___x_142_ = lp_mathlib_Complex_instAddCommMonoid;
lean_inc(v_n_x27_137_);
v___x_143_ = l_List_finRange(v_n_x27_137_);
v___x_144_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_144_, 0, v_n_x27_137_);
lean_inc(v_n_136_);
v___x_145_ = l_List_finRange(v_n_136_);
v___x_146_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_146_, 0, v_n_136_);
v___x_147_ = lp_mathlib_ZMod_fintype___redArg(v_q_135_);
v___f_148_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_148_, 0, v___x_147_);
lean_inc_ref(v___f_148_);
lean_inc(v___x_145_);
lean_inc_ref(v___x_146_);
v___f_149_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_149_, 0, v___x_146_);
lean_closure_set(v___f_149_, 1, v___x_145_);
lean_closure_set(v___f_149_, 2, v___f_148_);
lean_inc(v___x_143_);
v___x_150_ = lp_mathlib_Fintype_piFinset___redArg(v___x_144_, v___x_143_, v___f_149_);
v___x_151_ = lp_mathlib_ZMod_commRing(v_q_135_);
v___x_152_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_152_);
v___f_154_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_154_, 0, v_w_138_);
lean_closure_set(v___f_154_, 1, v___x_153_);
lean_closure_set(v___f_154_, 2, v___x_143_);
lean_closure_set(v___f_154_, 3, v_fW_140_);
lean_closure_set(v___f_154_, 4, v___f_141_);
lean_closure_set(v___f_154_, 5, v___x_145_);
lean_closure_set(v___f_154_, 6, v_ph_139_);
lean_closure_set(v___f_154_, 7, v___x_146_);
lean_closure_set(v___f_154_, 8, v___f_148_);
lean_closure_set(v___f_154_, 9, v___x_142_);
v___x_155_ = lp_mathlib_Finset_sum___redArg(v___x_142_, v___x_150_, v___f_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK(lean_object* v_q_156_, lean_object* v_n_157_, lean_object* v_n_x27_158_, lean_object* v_inst_159_, lean_object* v_w_160_, lean_object* v_ph_161_, lean_object* v_fW_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_kerK___redArg(v_q_156_, v_n_157_, v_n_x27_158_, v_w_160_, v_ph_161_, v_fW_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg(lean_object* v_K_165_, lean_object* v_x_166_){
_start:
{
lean_object* v_zero_167_; uint8_t v_isZero_168_; 
v_zero_167_ = lean_unsigned_to_nat(0u);
v_isZero_168_ = lean_nat_dec_eq(v_x_166_, v_zero_167_);
if (v_isZero_168_ == 1)
{
lean_object* v___f_169_; 
lean_dec(v_K_165_);
v___f_169_ = ((lean_object*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___closed__0));
return v___f_169_;
}
else
{
lean_object* v_one_170_; lean_object* v_n_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___f_174_; 
v_one_170_ = lean_unsigned_to_nat(1u);
v_n_171_ = lean_nat_sub(v_x_166_, v_one_170_);
lean_inc(v_K_165_);
lean_inc(v_n_171_);
v___x_172_ = lean_apply_1(v_K_165_, v_n_171_);
v___x_173_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg(v_K_165_, v_n_171_);
lean_dec(v_n_171_);
v___f_174_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_174_, 0, v___x_173_);
lean_closure_set(v___f_174_, 1, v___x_172_);
return v___f_174_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___boxed(lean_object* v_K_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg(v_K_175_, v_x_176_);
lean_dec(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK(lean_object* v_R_178_, lean_object* v_inst_179_, lean_object* v_M_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_K_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg(v_K_183_, v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___boxed(lean_object* v_R_186_, lean_object* v_inst_187_, lean_object* v_M_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_K_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK(v_R_186_, v_inst_187_, v_M_188_, v_inst_189_, v_inst_190_, v_K_191_, v_x_192_);
lean_dec(v_x_192_);
lean_dec(v_inst_190_);
lean_dec_ref(v_inst_189_);
lean_dec_ref(v_inst_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg(lean_object* v_U_194_, lean_object* v_K_195_, lean_object* v_x_196_){
_start:
{
lean_object* v_zero_197_; uint8_t v_isZero_198_; 
v_zero_197_ = lean_unsigned_to_nat(0u);
v_isZero_198_ = lean_nat_dec_eq(v_x_196_, v_zero_197_);
if (v_isZero_198_ == 1)
{
lean_object* v___f_199_; 
lean_dec(v_K_195_);
lean_dec(v_U_194_);
v___f_199_ = ((lean_object*)(lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainK___redArg___closed__0));
return v___f_199_;
}
else
{
lean_object* v_one_200_; lean_object* v_n_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___f_207_; 
v_one_200_ = lean_unsigned_to_nat(1u);
v_n_201_ = lean_nat_sub(v_x_196_, v_one_200_);
v___x_202_ = lean_nat_add(v_n_201_, v_one_200_);
lean_inc(v_U_194_);
v___x_203_ = lean_apply_1(v_U_194_, v___x_202_);
lean_inc(v_K_195_);
lean_inc(v_n_201_);
v___x_204_ = lean_apply_1(v_K_195_, v_n_201_);
v___f_205_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_205_, 0, v___x_204_);
lean_closure_set(v___f_205_, 1, v___x_203_);
v___x_206_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg(v_U_194_, v_K_195_, v_n_201_);
lean_dec(v_n_201_);
v___f_207_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_207_, 0, v___x_206_);
lean_closure_set(v___f_207_, 1, v___f_205_);
return v___f_207_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg___boxed(lean_object* v_U_208_, lean_object* v_K_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg(v_U_208_, v_K_209_, v_x_210_);
lean_dec(v_x_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK(lean_object* v_R_212_, lean_object* v_inst_213_, lean_object* v_M_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_U_217_, lean_object* v_K_218_, lean_object* v_x_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___redArg(v_U_217_, v_K_218_, v_x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK___boxed(lean_object* v_R_221_, lean_object* v_inst_222_, lean_object* v_M_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_U_226_, lean_object* v_K_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_chainUK(v_R_221_, v_inst_222_, v_M_223_, v_inst_224_, v_inst_225_, v_U_226_, v_K_227_, v_x_228_);
lean_dec(v_x_228_);
lean_dec(v_inst_225_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v_inst_222_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_Uc(lean_object* v_F_230_, lean_object* v_inst_231_, lean_object* v_n_232_, lean_object* v_fL_233_, lean_object* v_e_234_, lean_object* v_c_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLattices_LocalLatticeBases_Uc___boxed(lean_object* v_F_237_, lean_object* v_inst_238_, lean_object* v_n_239_, lean_object* v_fL_240_, lean_object* v_e_241_, lean_object* v_c_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lp_tree_Formalism_HermitianLattices_LocalLatticeBases_Uc(v_F_237_, v_inst_238_, v_n_239_, v_fL_240_, v_e_241_, v_c_242_);
lean_dec(v_c_242_);
lean_dec(v_e_241_);
lean_dec(v_fL_240_);
lean_dec(v_n_239_);
lean_dec_ref(v_inst_238_);
return v_res_243_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogVandermondeBounds_GaussOperatorProductFormula(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GL3MeanSquares_FourierTransformKernelSurjective(uint8_t builtin) {
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
res = initialize_tree_Formalism_LogVandermondeBounds_GaussOperatorProductFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
