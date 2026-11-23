// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
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
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub___at___00Formalism_REAL_HidaSetting_adm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub___at___00Formalism_REAL_HidaSetting_adm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_HidaSetting_adm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_HidaSetting_adm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub(lean_object* v_n_1_, lean_object* v_00_u03b5_2_, lean_object* v_S_3_, lean_object* v_E_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_00_u03c3_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub___boxed(lean_object* v_n_9_, lean_object* v_00_u03b5_10_, lean_object* v_S_11_, lean_object* v_E_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_00_u03c3_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_REAL_eqvSub(v_n_9_, v_00_u03b5_10_, v_S_11_, v_E_12_, v_inst_13_, v_inst_14_, v_00_u03c3_15_);
lean_dec(v_00_u03c3_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_00_u03b5_10_);
lean_dec(v_n_9_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub___at___00Formalism_REAL_HidaSetting_adm_spec__0(lean_object* v_P_17_, lean_object* v_n_18_, lean_object* v_00_u03b5_19_, lean_object* v_S_20_, lean_object* v_00_u03c3_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_eqvSub___at___00Formalism_REAL_HidaSetting_adm_spec__0___boxed(lean_object* v_P_23_, lean_object* v_n_24_, lean_object* v_00_u03b5_25_, lean_object* v_S_26_, lean_object* v_00_u03c3_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_REAL_eqvSub___at___00Formalism_REAL_HidaSetting_adm_spec__0(v_P_23_, v_n_24_, v_00_u03b5_25_, v_S_26_, v_00_u03c3_27_);
lean_dec(v_00_u03c3_27_);
lean_dec_ref(v_00_u03b5_25_);
lean_dec(v_n_24_);
lean_dec_ref(v_P_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_HidaSetting_adm(lean_object* v_n_29_, lean_object* v_00_u03b5_30_, lean_object* v_P_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_HidaSetting_adm___boxed(lean_object* v_n_33_, lean_object* v_00_u03b5_34_, lean_object* v_P_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_REAL_HidaSetting_adm(v_n_33_, v_00_u03b5_34_, v_P_35_);
lean_dec_ref(v_P_35_);
lean_dec_ref(v_00_u03b5_34_);
lean_dec(v_n_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__0(lean_object* v_inv_37_, lean_object* v___y_38_, lean_object* v_j_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_apply_2(v_inv_37_, v_j_39_, v___y_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__1(lean_object* v_inv_41_, lean_object* v___y_42_, lean_object* v_j_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_apply_2(v_inv_41_, v___y_42_, v_j_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0___lam__0(lean_object* v_v_45_, lean_object* v_w_46_, lean_object* v_i_47_){
_start:
{
lean_object* v___x_48_; lean_object* v_re_49_; lean_object* v_im_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
lean_inc(v_i_47_);
v___x_48_ = lean_apply_1(v_v_45_, v_i_47_);
v_re_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_re_49_);
v_im_50_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_im_50_);
lean_dec_ref(v___x_48_);
v___x_51_ = lean_apply_1(v_w_46_, v_i_47_);
v___x_52_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_49_, v_im_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___lam__0(lean_object* v_x1_53_, lean_object* v_x2_54_){
_start:
{
lean_object* v_re_55_; lean_object* v_im_56_; lean_object* v_re_57_; lean_object* v_im_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_67_; 
v_re_55_ = lean_ctor_get(v_x1_53_, 0);
lean_inc(v_re_55_);
v_im_56_ = lean_ctor_get(v_x1_53_, 1);
lean_inc(v_im_56_);
lean_dec_ref(v_x1_53_);
v_re_57_ = lean_ctor_get(v_x2_54_, 0);
v_im_58_ = lean_ctor_get(v_x2_54_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x2_54_);
if (v_isSharedCheck_67_ == 0)
{
v___x_60_ = v_x2_54_;
v_isShared_61_ = v_isSharedCheck_67_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_im_58_);
lean_inc(v_re_57_);
lean_dec(v_x2_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_67_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_65_; 
v___f_62_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_62_, 0, v_re_55_);
lean_closure_set(v___f_62_, 1, v_re_57_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_63_, 0, v_im_56_);
lean_closure_set(v___f_63_, 1, v_im_58_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___f_63_);
lean_ctor_set(v___x_60_, 0, v___f_62_);
v___x_65_ = v___x_60_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___f_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___f_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_70_ = lp_mathlib_Complex_ofReal(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1(lean_object* v_s_71_){
_start:
{
lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___f_72_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__0));
v___x_73_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1___closed__1);
v___x_74_ = l_List_foldrTR___redArg(v___f_72_, v___x_73_, v_s_71_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0___redArg(lean_object* v_s_75_, lean_object* v_f_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lp_mathlib_Multiset_map___redArg(v_f_76_, v_s_75_);
v___x_78_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0_spec__1(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0(lean_object* v_n_79_, lean_object* v_v_80_, lean_object* v_w_81_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___f_82_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_82_, 0, v_v_80_);
lean_closure_set(v___f_82_, 1, v_w_81_);
v___x_83_ = l_List_finRange(v_n_79_);
v___x_84_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0___redArg(v___x_83_, v___f_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__2(lean_object* v_inv_85_, lean_object* v_inv_86_, lean_object* v_n_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v___f_90_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Rs___redArg___lam__0), 3, 2);
lean_closure_set(v___f_90_, 0, v_inv_85_);
lean_closure_set(v___f_90_, 1, v___y_89_);
v___f_91_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Rs___redArg___lam__1), 3, 2);
lean_closure_set(v___f_91_, 0, v_inv_86_);
lean_closure_set(v___f_91_, 1, v___y_88_);
v___x_92_ = lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0(v_n_87_, v___f_91_, v___f_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__3(lean_object* v_val_93_, lean_object* v___y_94_, lean_object* v_j_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_apply_2(v_val_93_, v_j_95_, v___y_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__4(lean_object* v_val_97_, lean_object* v___y_98_, lean_object* v_j_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_apply_2(v_val_97_, v___y_98_, v_j_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg___lam__5(lean_object* v_val_101_, lean_object* v_val_102_, lean_object* v_n_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_106_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Rs___redArg___lam__3), 3, 2);
lean_closure_set(v___f_106_, 0, v_val_101_);
lean_closure_set(v___f_106_, 1, v___y_105_);
v___f_107_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Rs___redArg___lam__4), 3, 2);
lean_closure_set(v___f_107_, 0, v_val_102_);
lean_closure_set(v___f_107_, 1, v___y_104_);
v___x_108_ = lp_tree_dotProduct___at___00Formalism_REAL_Rs_spec__0(v_n_103_, v___f_107_, v___f_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___redArg(lean_object* v_n_109_, lean_object* v_h_110_, lean_object* v_F_111_, lean_object* v_g_112_){
_start:
{
lean_object* v_val_113_; lean_object* v_inv_114_; lean_object* v_val_115_; lean_object* v_inv_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v_val_113_ = lean_ctor_get(v_g_112_, 0);
lean_inc(v_val_113_);
v_inv_114_ = lean_ctor_get(v_g_112_, 1);
lean_inc(v_inv_114_);
lean_dec_ref(v_g_112_);
v_val_115_ = lean_ctor_get(v_h_110_, 0);
v_inv_116_ = lean_ctor_get(v_h_110_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_h_110_);
if (v_isSharedCheck_126_ == 0)
{
v___x_118_ = v_h_110_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_inv_116_);
lean_inc(v_val_115_);
lean_dec(v_h_110_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_123_; 
lean_inc(v_n_109_);
v___f_120_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Rs___redArg___lam__2), 5, 3);
lean_closure_set(v___f_120_, 0, v_inv_114_);
lean_closure_set(v___f_120_, 1, v_inv_116_);
lean_closure_set(v___f_120_, 2, v_n_109_);
v___f_121_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Rs___redArg___lam__5), 5, 3);
lean_closure_set(v___f_121_, 0, v_val_115_);
lean_closure_set(v___f_121_, 1, v_val_113_);
lean_closure_set(v___f_121_, 2, v_n_109_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___f_120_);
lean_ctor_set(v___x_118_, 0, v___f_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___f_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___f_120_);
v___x_123_ = v_reuseFailAlloc_125_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_1(v_F_111_, v___x_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs(lean_object* v_n_127_, lean_object* v_00_u03b5_128_, lean_object* v_E_129_, lean_object* v_h_130_, lean_object* v_F_131_, lean_object* v_g_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lp_tree_Formalism_REAL_Rs___redArg(v_n_127_, v_h_130_, v_F_131_, v_g_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Rs___boxed(lean_object* v_n_134_, lean_object* v_00_u03b5_135_, lean_object* v_E_136_, lean_object* v_h_137_, lean_object* v_F_138_, lean_object* v_g_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_tree_Formalism_REAL_Rs(v_n_134_, v_00_u03b5_135_, v_E_136_, v_h_137_, v_F_138_, v_g_139_);
lean_dec_ref(v_00_u03b5_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0(lean_object* v_00_u03b9_141_, lean_object* v_s_142_, lean_object* v_f_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_Rs_spec__0_spec__0___redArg(v_s_142_, v_f_143_);
return v___x_144_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_SmoothOnGVIff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_IsRightTranslationIsometric(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_SmoothOnGVIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
