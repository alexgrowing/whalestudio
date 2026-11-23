// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionInvariants
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_REAL_Jm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___lam__0(lean_object*);
static const lean_closure_object lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___lam__0(lean_object* v_z_1_){
_start:
{
lean_object* v_re_2_; lean_object* v_im_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_re_2_ = lean_ctor_get(v_z_1_, 0);
v_im_3_ = lean_ctor_get(v_z_1_, 1);
v_isSharedCheck_11_ = !lean_is_exclusive(v_z_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_z_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_im_3_);
lean_inc(v_re_2_);
lean_dec(v_z_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___f_7_; lean_object* v___x_9_; 
v___f_7_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_7_, 0, v_im_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v___f_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_re_2_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v___f_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg(lean_object* v_M_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = ((lean_object*)(lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg___closed__0));
v___x_17_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_17_, 0, lean_box(0));
lean_closure_set(v___x_17_, 1, lean_box(0));
lean_closure_set(v___x_17_, 2, lean_box(0));
lean_closure_set(v___x_17_, 3, v_M_13_);
v___x_18_ = lp_mathlib_Matrix_map___redArg(v___x_17_, v___f_16_, v_a_14_, v_a_15_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0(lean_object* v_m_19_, lean_object* v_n_20_, lean_object* v_M_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg(v_M_21_, v_a_22_, v_a_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__0(lean_object* v_n_25_, lean_object* v_00_u03b5_26_, lean_object* v___y_27_, lean_object* v_j_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Formalism_REAL_Jm(v_n_25_, v_00_u03b5_26_, v_j_28_, v___y_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__0___boxed(lean_object* v_n_30_, lean_object* v_00_u03b5_31_, lean_object* v___y_32_, lean_object* v_j_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__0(v_n_30_, v_00_u03b5_31_, v___y_32_, v_j_33_);
lean_dec(v_n_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__1(lean_object* v_n_35_, lean_object* v_00_u03b5_36_, lean_object* v___y_37_, lean_object* v_j_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree_Formalism_REAL_Jm(v_n_35_, v_00_u03b5_36_, v___y_37_, v_j_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__1___boxed(lean_object* v_n_40_, lean_object* v_00_u03b5_41_, lean_object* v___y_42_, lean_object* v_j_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__1(v_n_40_, v_00_u03b5_41_, v___y_42_, v_j_43_);
lean_dec(v_n_40_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__2(lean_object* v_m_45_, lean_object* v_j_46_, lean_object* v_j_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Matrix_conjTranspose___at___00Formalism_REAL_indefiniteUnitaryMk_spec__0___redArg(v_m_45_, v_j_47_, v_j_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1___lam__0(lean_object* v_v_49_, lean_object* v_w_50_, lean_object* v_i_51_){
_start:
{
lean_object* v___x_52_; lean_object* v_re_53_; lean_object* v_im_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_inc(v_i_51_);
v___x_52_ = lean_apply_1(v_v_49_, v_i_51_);
v_re_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_re_53_);
v_im_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_im_54_);
lean_dec_ref(v___x_52_);
v___x_55_ = lean_apply_1(v_w_50_, v_i_51_);
v___x_56_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_53_, v_im_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___lam__0(lean_object* v_x1_57_, lean_object* v_x2_58_){
_start:
{
lean_object* v_re_59_; lean_object* v_im_60_; lean_object* v_re_61_; lean_object* v_im_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_71_; 
v_re_59_ = lean_ctor_get(v_x1_57_, 0);
lean_inc(v_re_59_);
v_im_60_ = lean_ctor_get(v_x1_57_, 1);
lean_inc(v_im_60_);
lean_dec_ref(v_x1_57_);
v_re_61_ = lean_ctor_get(v_x2_58_, 0);
v_im_62_ = lean_ctor_get(v_x2_58_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x2_58_);
if (v_isSharedCheck_71_ == 0)
{
v___x_64_ = v_x2_58_;
v_isShared_65_ = v_isSharedCheck_71_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_im_62_);
lean_inc(v_re_61_);
lean_dec(v_x2_58_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_71_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___f_66_; lean_object* v___f_67_; lean_object* v___x_69_; 
v___f_66_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_66_, 0, v_re_59_);
lean_closure_set(v___f_66_, 1, v_re_61_);
v___f_67_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_67_, 0, v_im_60_);
lean_closure_set(v___f_67_, 1, v_im_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___f_67_);
lean_ctor_set(v___x_64_, 0, v___f_66_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___f_66_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v___f_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_74_ = lp_mathlib_Complex_ofReal(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2(lean_object* v_s_75_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___f_76_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__0));
v___x_77_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2___closed__1);
v___x_78_ = l_List_foldrTR___redArg(v___f_76_, v___x_77_, v_s_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1___redArg(lean_object* v_s_79_, lean_object* v_f_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lp_mathlib_Multiset_map___redArg(v_f_80_, v_s_79_);
v___x_82_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1_spec__2(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1(lean_object* v_n_83_, lean_object* v_v_84_, lean_object* v_w_85_){
_start:
{
lean_object* v___f_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___f_86_ = lean_alloc_closure((void*)(lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_86_, 0, v_v_84_);
lean_closure_set(v___f_86_, 1, v_w_85_);
v___x_87_ = l_List_finRange(v_n_83_);
v___x_88_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1___redArg(v___x_87_, v___f_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__3(lean_object* v_m_89_, lean_object* v_n_90_, lean_object* v___f_91_, lean_object* v_j_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___x_94_; 
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__2), 3, 2);
lean_closure_set(v___f_93_, 0, v_m_89_);
lean_closure_set(v___f_93_, 1, v_j_92_);
v___x_94_ = lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1(v_n_90_, v___f_91_, v___f_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__4(lean_object* v_n_95_, lean_object* v_00_u03b5_96_, lean_object* v_m_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___x_103_; 
lean_inc_ref(v_00_u03b5_96_);
lean_inc_n(v_n_95_, 3);
v___f_100_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_100_, 0, v_n_95_);
lean_closure_set(v___f_100_, 1, v_00_u03b5_96_);
lean_closure_set(v___f_100_, 2, v___y_99_);
v___f_101_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_101_, 0, v_n_95_);
lean_closure_set(v___f_101_, 1, v_00_u03b5_96_);
lean_closure_set(v___f_101_, 2, v___y_98_);
v___f_102_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__3), 4, 3);
lean_closure_set(v___f_102_, 0, v_m_97_);
lean_closure_set(v___f_102_, 1, v_n_95_);
lean_closure_set(v___f_102_, 2, v___f_101_);
v___x_103_ = lp_tree_dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1(v_n_95_, v___f_102_, v___f_100_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg(lean_object* v_n_104_, lean_object* v_00_u03b5_105_, lean_object* v_m_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; 
lean_inc_ref(v_m_106_);
v___f_107_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg___lam__4), 5, 3);
lean_closure_set(v___f_107_, 0, v_n_104_);
lean_closure_set(v___f_107_, 1, v_00_u03b5_105_);
lean_closure_set(v___f_107_, 2, v_m_106_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_m_106_);
lean_ctor_set(v___x_108_, 1, v___f_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_indefiniteUnitaryMk(lean_object* v_n_109_, lean_object* v_00_u03b5_110_, lean_object* v_m_111_, lean_object* v_h_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lp_tree_Formalism_REAL_indefiniteUnitaryMk___redArg(v_n_109_, v_00_u03b5_110_, v_m_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1(lean_object* v_00_u03b9_114_, lean_object* v_s_115_, lean_object* v_f_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lp_tree_Finset_sum___at___00dotProduct___at___00Formalism_REAL_indefiniteUnitaryMk_spec__1_spec__1___redArg(v_s_115_, v_f_116_);
return v___x_117_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
