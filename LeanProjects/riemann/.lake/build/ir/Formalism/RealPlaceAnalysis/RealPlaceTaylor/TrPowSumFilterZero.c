// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementB
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_REAL_vand_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_REAL_TrPow__m___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_REAL_TrPow__m___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_){
_start:
{
lean_object* v_re_3_; lean_object* v_im_4_; lean_object* v_re_5_; lean_object* v_im_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_15_; 
v_re_3_ = lean_ctor_get(v_x1_1_, 0);
lean_inc(v_re_3_);
v_im_4_ = lean_ctor_get(v_x1_1_, 1);
lean_inc(v_im_4_);
lean_dec_ref(v_x1_1_);
v_re_5_ = lean_ctor_get(v_x2_2_, 0);
v_im_6_ = lean_ctor_get(v_x2_2_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_x2_2_);
if (v_isSharedCheck_15_ == 0)
{
v___x_8_ = v_x2_2_;
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_im_6_);
lean_inc(v_re_5_);
lean_dec(v_x2_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___x_13_; 
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v_re_3_);
lean_closure_set(v___f_10_, 1, v_re_5_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v_im_4_);
lean_closure_set(v___f_11_, 1, v_im_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___f_11_);
lean_ctor_set(v___x_8_, 0, v___f_10_);
v___x_13_ = v___x_8_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___f_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v___f_11_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_18_ = lp_mathlib_Complex_ofReal(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0(lean_object* v_s_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___f_20_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__0));
v___x_21_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0___closed__1);
v___x_22_ = l_List_foldrTR___redArg(v___f_20_, v___x_21_, v_s_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0___redArg(lean_object* v_s_23_, lean_object* v_f_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lp_mathlib_Multiset_map___redArg(v_f_24_, v_s_23_);
v___x_26_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0_spec__0(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_lp_tree_Formalism_REAL_TrPow__m___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_28_ = lp_mathlib_Complex_ofReal(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m___lam__0___boxed(lean_object* v_n_29_, lean_object* v_l_30_, lean_object* v_n_31_, lean_object* v_b_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_Formalism_REAL_TrPow__m___lam__0(v_n_29_, v_l_30_, v_n_31_, v_b_32_);
lean_dec(v_n_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m(lean_object* v_n_34_, lean_object* v_l_35_, lean_object* v_x_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_zero_38_; uint8_t v_isZero_39_; 
v_zero_38_ = lean_unsigned_to_nat(0u);
v_isZero_39_ = lean_nat_dec_eq(v_x_36_, v_zero_38_);
if (v_isZero_39_ == 1)
{
lean_object* v___x_40_; 
lean_dec(v_a_37_);
lean_dec_ref(v_l_35_);
lean_dec(v_n_34_);
v___x_40_ = lean_obj_once(&lp_tree_Formalism_REAL_TrPow__m___closed__0, &lp_tree_Formalism_REAL_TrPow__m___closed__0_once, _init_lp_tree_Formalism_REAL_TrPow__m___closed__0);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v_re_42_; lean_object* v_im_43_; lean_object* v_one_44_; lean_object* v_n_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v_re_48_; lean_object* v_im_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_re_54_; lean_object* v_im_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_66_; 
lean_inc_ref_n(v_l_35_, 2);
lean_inc_n(v_a_37_, 2);
v___x_41_ = lean_apply_1(v_l_35_, v_a_37_);
v_re_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_re_42_);
v_im_43_ = lean_ctor_get(v___x_41_, 1);
lean_inc(v_im_43_);
lean_dec_ref(v___x_41_);
v_one_44_ = lean_unsigned_to_nat(1u);
v_n_45_ = lean_nat_sub(v_x_36_, v_one_44_);
lean_inc_n(v_n_34_, 3);
v___x_46_ = lp_tree_Formalism_REAL_TrPow__m(v_n_34_, v_l_35_, v_n_45_, v_a_37_);
v___x_47_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_42_, v_im_43_, v___x_46_);
v_re_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_re_48_);
v_im_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_im_49_);
lean_dec_ref(v___x_47_);
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_TrPow__m___lam__0___boxed), 4, 3);
lean_closure_set(v___f_50_, 0, v_n_34_);
lean_closure_set(v___f_50_, 1, v_l_35_);
lean_closure_set(v___f_50_, 2, v_n_45_);
v___x_51_ = l_List_finRange(v_n_34_);
v___x_52_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_REAL_vand_spec__0_spec__0___redArg(v_n_34_, v_a_37_, v___x_51_);
lean_dec(v_a_37_);
lean_dec(v_n_34_);
v___x_53_ = lp_tree_Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0___redArg(v___x_52_, v___f_50_);
v_re_54_ = lean_ctor_get(v___x_53_, 0);
v_im_55_ = lean_ctor_get(v___x_53_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_66_ == 0)
{
v___x_57_ = v___x_53_;
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_im_55_);
lean_inc(v_re_54_);
lean_dec(v___x_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_64_; 
v___f_59_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_59_, 0, v_re_54_);
v___f_60_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_60_, 0, v_re_48_);
lean_closure_set(v___f_60_, 1, v___f_59_);
v___f_61_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_61_, 0, v_im_55_);
v___f_62_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_62_, 0, v_im_49_);
lean_closure_set(v___f_62_, 1, v___f_61_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___f_62_);
lean_ctor_set(v___x_57_, 0, v___f_60_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___f_60_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___f_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m___lam__0(lean_object* v_n_67_, lean_object* v_l_68_, lean_object* v_n_69_, lean_object* v_b_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_tree_Formalism_REAL_TrPow__m(v_n_67_, v_l_68_, v_n_69_, v_b_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_TrPow__m___boxed(lean_object* v_n_72_, lean_object* v_l_73_, lean_object* v_x_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_REAL_TrPow__m(v_n_72_, v_l_73_, v_x_74_, v_a_75_);
lean_dec(v_x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0(lean_object* v_00_u03b9_77_, lean_object* v_s_78_, lean_object* v_f_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_tree_Finset_sum___at___00Formalism_REAL_TrPow__m_spec__0___redArg(v_s_78_, v_f_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___redArg(lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
lean_object* v_zero_84_; uint8_t v_isZero_85_; 
v_zero_84_ = lean_unsigned_to_nat(0u);
v_isZero_85_ = lean_nat_dec_eq(v_x_81_, v_zero_84_);
if (v_isZero_85_ == 1)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_83_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__1_82_, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_one_88_; lean_object* v_n_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_82_);
v_one_88_ = lean_unsigned_to_nat(1u);
v_n_89_ = lean_nat_sub(v_x_81_, v_one_88_);
v___x_90_ = lean_apply_1(v_h__2_83_, v_n_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___redArg___boxed(lean_object* v_x_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___redArg(v_x_91_, v_h__1_92_, v_h__2_93_);
lean_dec(v_x_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter(lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
lean_object* v_zero_99_; uint8_t v_isZero_100_; 
v_zero_99_ = lean_unsigned_to_nat(0u);
v_isZero_100_ = lean_nat_dec_eq(v_x_96_, v_zero_99_);
if (v_isZero_100_ == 1)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_98_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__1_97_, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v_one_103_; lean_object* v_n_104_; lean_object* v___x_105_; 
lean_dec(v_h__1_97_);
v_one_103_ = lean_unsigned_to_nat(1u);
v_n_104_ = lean_nat_sub(v_x_96_, v_one_103_);
v___x_105_ = lean_apply_1(v_h__2_98_, v_n_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter___boxed(lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero_0__Formalism_REAL_epow_match__1_splitter(v_motive_106_, v_x_107_, v_h__1_108_, v_h__2_109_);
lean_dec(v_x_107_);
return v_res_110_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
