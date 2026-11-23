// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.FockPairGl
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementA
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_factorialBinarySplitting(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00Nat_multinomial_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_fockF_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_fockF_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_REAL_sgnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sgnv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_REAL_sgnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sgnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0___redArg(lean_object* v_m_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_toFun_3_);
lean_dec_ref(v_p_2_);
v___x_4_ = lean_apply_1(v_toFun_3_, v_m_1_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0(lean_object* v_00_u03c3_5_, lean_object* v_m_6_, lean_object* v_p_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0___redArg(v_m_6_, v_p_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___redArg(lean_object* v_p_9_){
_start:
{
lean_object* v_support_10_; 
v_support_10_ = lean_ctor_get(v_p_9_, 0);
lean_inc(v_support_10_);
return v_support_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___redArg___boxed(lean_object* v_p_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___redArg(v_p_11_);
lean_dec_ref(v_p_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1(lean_object* v_00_u03c3_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_support_15_; 
v_support_15_ = lean_ctor_get(v_p_14_, 0);
lean_inc(v_support_15_);
return v_support_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1___boxed(lean_object* v_00_u03c3_16_, lean_object* v_p_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_MvPolynomial_support___at___00Formalism_REAL_fockF_spec__1(v_00_u03c3_16_, v_p_17_);
lean_dec_ref(v_p_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF___redArg___lam__0(lean_object* v_toFun_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_apply_1(v_toFun_19_, v_k_20_);
v___x_22_ = lp_mathlib_Nat_factorialBinarySplitting(v___x_21_);
lean_dec(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF___redArg___lam__1(lean_object* v_f_23_, lean_object* v_g_24_, lean_object* v_m_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_re_28_; lean_object* v_im_29_; lean_object* v_re_30_; lean_object* v_im_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_48_; 
lean_inc_ref_n(v_m_25_, 2);
v___x_26_ = lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0___redArg(v_m_25_, v_f_23_);
v___x_27_ = lp_tree_MvPolynomial_coeff___at___00Formalism_REAL_fockF_spec__0___redArg(v_m_25_, v_g_24_);
v_re_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_re_28_);
v_im_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_im_29_);
lean_dec_ref(v___x_27_);
v_re_30_ = lean_ctor_get(v___x_26_, 0);
v_im_31_ = lean_ctor_get(v___x_26_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_48_ == 0)
{
v___x_33_ = v___x_26_;
v_isShared_34_ = v_isSharedCheck_48_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_im_31_);
lean_inc(v_re_30_);
lean_dec(v___x_26_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_48_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_support_35_; lean_object* v_toFun_36_; lean_object* v___f_37_; lean_object* v___x_39_; 
v_support_35_ = lean_ctor_get(v_m_25_, 0);
lean_inc(v_support_35_);
v_toFun_36_ = lean_ctor_get(v_m_25_, 1);
lean_inc(v_toFun_36_);
lean_dec_ref(v_m_25_);
v___f_37_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_37_, 0, v_im_29_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___f_37_);
lean_ctor_set(v___x_33_, 0, v_re_28_);
v___x_39_ = v___x_33_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_re_28_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___f_37_);
v___x_39_ = v_reuseFailAlloc_47_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v_re_41_; lean_object* v_im_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_40_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_30_, v_im_31_, v___x_39_);
v_re_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_re_41_);
v_im_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_im_42_);
lean_dec_ref(v___x_40_);
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_fockF___redArg___lam__0), 2, 1);
lean_closure_set(v___f_43_, 0, v_toFun_36_);
v___x_44_ = lp_mathlib_Finset_prod___at___00Nat_multinomial_spec__1___redArg(v_support_35_, v___f_43_);
v___x_45_ = lp_mathlib_Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0(v___x_44_);
v___x_46_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_41_, v_im_42_, v___x_45_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___lam__0(lean_object* v_x1_49_, lean_object* v_x2_50_){
_start:
{
lean_object* v_re_51_; lean_object* v_im_52_; lean_object* v_re_53_; lean_object* v_im_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v_re_51_ = lean_ctor_get(v_x1_49_, 0);
lean_inc(v_re_51_);
v_im_52_ = lean_ctor_get(v_x1_49_, 1);
lean_inc(v_im_52_);
lean_dec_ref(v_x1_49_);
v_re_53_ = lean_ctor_get(v_x2_50_, 0);
v_im_54_ = lean_ctor_get(v_x2_50_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x2_50_);
if (v_isSharedCheck_63_ == 0)
{
v___x_56_ = v_x2_50_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_im_54_);
lean_inc(v_re_53_);
lean_dec(v_x2_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___x_61_; 
v___f_58_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_58_, 0, v_re_51_);
lean_closure_set(v___f_58_, 1, v_re_53_);
v___f_59_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_59_, 0, v_im_52_);
lean_closure_set(v___f_59_, 1, v_im_54_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___f_59_);
lean_ctor_set(v___x_56_, 0, v___f_58_);
v___x_61_ = v___x_56_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___f_58_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___f_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_66_ = lp_mathlib_Complex_ofReal(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(lean_object* v_s_67_){
_start:
{
lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___f_68_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__0));
v___x_69_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2___closed__1);
v___x_70_ = l_List_foldrTR___redArg(v___f_68_, v___x_69_, v_s_67_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_fockF_spec__2___redArg(lean_object* v_s_71_, lean_object* v_f_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lp_mathlib_Multiset_map___redArg(v_f_72_, v_s_71_);
v___x_74_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_fockF_spec__2_spec__2(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF___redArg(lean_object* v_f_75_, lean_object* v_g_76_){
_start:
{
lean_object* v_support_77_; lean_object* v___f_78_; lean_object* v___x_79_; 
v_support_77_ = lean_ctor_get(v_f_75_, 0);
lean_inc(v_support_77_);
v___f_78_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_fockF___redArg___lam__1), 3, 2);
lean_closure_set(v___f_78_, 0, v_f_75_);
lean_closure_set(v___f_78_, 1, v_g_76_);
v___x_79_ = lp_tree_Finset_sum___at___00Formalism_REAL_fockF_spec__2___redArg(v_support_77_, v___f_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_fockF(lean_object* v_00_u03c3_80_, lean_object* v_f_81_, lean_object* v_g_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_tree_Formalism_REAL_fockF___redArg(v_f_81_, v_g_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_fockF_spec__2(lean_object* v_00_u03b9_84_, lean_object* v_s_85_, lean_object* v_f_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_tree_Finset_sum___at___00Formalism_REAL_fockF_spec__2___redArg(v_s_85_, v_f_86_);
return v___x_87_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_REAL_sgnv___redArg(lean_object* v_00_u03b5_88_, lean_object* v_00_u03b5_x27_89_, lean_object* v_i_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_92_ = lean_apply_1(v_00_u03b5_88_, v_i_90_);
v___x_93_ = lean_apply_1(v_00_u03b5_x27_89_, v_a_91_);
v___x_94_ = lean_unbox(v___x_92_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = lean_unbox(v___x_93_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = lean_unbox(v___x_92_);
return v___x_97_;
}
}
else
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v___x_93_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sgnv___redArg___boxed(lean_object* v_00_u03b5_99_, lean_object* v_00_u03b5_x27_100_, lean_object* v_i_101_, lean_object* v_a_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = lp_tree_Formalism_REAL_sgnv___redArg(v_00_u03b5_99_, v_00_u03b5_x27_100_, v_i_101_, v_a_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_REAL_sgnv(lean_object* v_M_105_, lean_object* v_n_x27_106_, lean_object* v_00_u03b5_107_, lean_object* v_00_u03b5_x27_108_, lean_object* v_i_109_, lean_object* v_a_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lp_tree_Formalism_REAL_sgnv___redArg(v_00_u03b5_107_, v_00_u03b5_x27_108_, v_i_109_, v_a_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_sgnv___boxed(lean_object* v_M_112_, lean_object* v_n_x27_113_, lean_object* v_00_u03b5_114_, lean_object* v_00_u03b5_x27_115_, lean_object* v_i_116_, lean_object* v_a_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = lp_tree_Formalism_REAL_sgnv(v_M_112_, v_n_x27_113_, v_00_u03b5_114_, v_00_u03b5_x27_115_, v_i_116_, v_a_117_);
lean_dec(v_n_x27_113_);
lean_dec(v_M_112_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_FockPairGl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
