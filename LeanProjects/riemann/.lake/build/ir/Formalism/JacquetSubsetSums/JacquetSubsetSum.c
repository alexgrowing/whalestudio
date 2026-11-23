// Lean compiler output
// Module: Formalism.JacquetSubsetSums.JacquetSubsetSum
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
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__0 = (const lean_object*)&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm___lam__0(lean_object* v_00_u03b2_1_, lean_object* v_i_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_re_5_; lean_object* v_im_6_; lean_object* v___x_7_; lean_object* v_re_8_; lean_object* v_im_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_20_; 
lean_inc_ref(v_00_u03b2_1_);
v___x_4_ = lean_apply_1(v_00_u03b2_1_, v_i_2_);
v_re_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_re_5_);
v_im_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_im_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lean_apply_1(v_00_u03b2_1_, v_j_3_);
v_re_8_ = lean_ctor_get(v___x_7_, 0);
v_im_9_ = lean_ctor_get(v___x_7_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_20_ == 0)
{
v___x_11_ = v___x_7_;
v_isShared_12_ = v_isSharedCheck_20_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_im_9_);
lean_inc(v_re_8_);
lean_dec(v___x_7_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_20_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_18_; 
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_13_, 0, v_re_8_);
v___f_14_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_14_, 0, v_re_5_);
lean_closure_set(v___f_14_, 1, v___f_13_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_15_, 0, v_im_9_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_16_, 0, v_im_6_);
lean_closure_set(v___f_16_, 1, v___f_15_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___f_16_);
lean_ctor_set(v___x_11_, 0, v___f_14_);
v___x_18_ = v___x_11_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v___f_14_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v___f_16_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg(lean_object* v_i_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
if (lean_obj_tag(v_a_22_) == 0)
{
lean_object* v___x_24_; 
v___x_24_ = l_List_reverse___redArg(v_a_23_);
return v___x_24_;
}
else
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_36_; 
v_head_25_ = lean_ctor_get(v_a_22_, 0);
v_tail_26_ = lean_ctor_get(v_a_22_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_a_22_);
if (v_isSharedCheck_36_ == 0)
{
v___x_28_ = v_a_22_;
v_isShared_29_ = v_isSharedCheck_36_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_head_25_);
lean_dec(v_a_22_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_36_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_lt(v_i_21_, v_head_25_);
if (v___x_30_ == 0)
{
lean_del_object(v___x_28_);
lean_dec(v_head_25_);
v_a_22_ = v_tail_26_;
goto _start;
}
else
{
lean_object* v___x_33_; 
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v_a_23_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_head_25_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_a_23_);
v___x_33_ = v_reuseFailAlloc_35_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
v_a_22_ = v_tail_26_;
v_a_23_ = v___x_33_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_i_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg(v_i_37_, v_a_38_, v_a_39_);
lean_dec(v_i_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(lean_object* v_r_41_, lean_object* v_i_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_box(0);
v___x_45_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg(v_i_42_, v_s_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg___boxed(lean_object* v_r_46_, lean_object* v_i_47_, lean_object* v_s_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(v_r_46_, v_i_47_, v_s_48_);
lean_dec(v_i_47_);
lean_dec(v_r_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___lam__0(lean_object* v_x1_50_, lean_object* v_x2_51_){
_start:
{
lean_object* v_re_52_; lean_object* v_im_53_; lean_object* v___x_54_; 
v_re_52_ = lean_ctor_get(v_x1_50_, 0);
lean_inc(v_re_52_);
v_im_53_ = lean_ctor_get(v_x1_50_, 1);
lean_inc(v_im_53_);
lean_dec_ref(v_x1_50_);
v___x_54_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_52_, v_im_53_, v_x2_51_);
return v___x_54_;
}
}
static lean_object* _init_lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_57_ = lp_mathlib_Complex_ofReal(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2(lean_object* v_s_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___f_59_ = ((lean_object*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__0));
v___x_60_ = lean_obj_once(&lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__1, &lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__1_once, _init_lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2___closed__1);
v___x_61_ = l_List_foldrTR___redArg(v___f_59_, v___x_60_, v_s_58_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1___redArg(lean_object* v_s_62_, lean_object* v_f_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lp_mathlib_Multiset_map___redArg(v_f_63_, v_s_62_);
v___x_65_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_PacketSums_vdm_spec__1_spec__2(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm___lam__1(lean_object* v_00_u03b2_66_, lean_object* v_r_67_, lean_object* v___x_68_, lean_object* v_i_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_inc(v_i_69_);
v___f_70_ = lean_alloc_closure((void*)(lp_tree_Formalism_PacketSums_vdm___lam__0), 3, 2);
lean_closure_set(v___f_70_, 0, v_00_u03b2_66_);
lean_closure_set(v___f_70_, 1, v_i_69_);
v___x_71_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(v_r_67_, v_i_69_, v___x_68_);
lean_dec(v_i_69_);
v___x_72_ = lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1___redArg(v___x_71_, v___f_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm___lam__1___boxed(lean_object* v_00_u03b2_73_, lean_object* v_r_74_, lean_object* v___x_75_, lean_object* v_i_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_PacketSums_vdm___lam__1(v_00_u03b2_73_, v_r_74_, v___x_75_, v_i_76_);
lean_dec(v_r_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_PacketSums_vdm(lean_object* v_r_78_, lean_object* v_00_u03b2_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___x_82_; 
lean_inc(v_r_78_);
v___x_80_ = l_List_finRange(v_r_78_);
lean_inc(v___x_80_);
v___f_81_ = lean_alloc_closure((void*)(lp_tree_Formalism_PacketSums_vdm___lam__1___boxed), 4, 3);
lean_closure_set(v___f_81_, 0, v_00_u03b2_79_);
lean_closure_set(v___f_81_, 1, v_r_78_);
lean_closure_set(v___f_81_, 2, v___x_80_);
v___x_82_ = lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1___redArg(v___x_80_, v___f_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___redArg(lean_object* v_r_83_, lean_object* v_i_84_, lean_object* v_s_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(v_r_83_, v_i_84_, v_s_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___redArg___boxed(lean_object* v_r_87_, lean_object* v_i_88_, lean_object* v_s_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___redArg(v_r_87_, v_i_88_, v_s_89_);
lean_dec(v_i_88_);
lean_dec(v_r_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0(lean_object* v_r_91_, lean_object* v_i_92_, lean_object* v_p_93_, lean_object* v_s_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(v_r_91_, v_i_92_, v_s_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0___boxed(lean_object* v_r_96_, lean_object* v_i_97_, lean_object* v_p_98_, lean_object* v_s_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_tree_Finset_filter___at___00Formalism_PacketSums_vdm_spec__0(v_r_96_, v_i_97_, v_p_98_, v_s_99_);
lean_dec(v_i_97_);
lean_dec(v_r_96_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1(lean_object* v_00_u03b9_101_, lean_object* v_s_102_, lean_object* v_f_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_tree_Finset_prod___at___00Formalism_PacketSums_vdm_spec__1___redArg(v_s_102_, v_f_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0(lean_object* v_r_105_, lean_object* v_i_106_, lean_object* v_p_107_, lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___redArg(v_r_105_, v_i_106_, v_s_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0___boxed(lean_object* v_r_110_, lean_object* v_i_111_, lean_object* v_p_112_, lean_object* v_s_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0(v_r_110_, v_i_111_, v_p_112_, v_s_113_);
lean_dec(v_i_111_);
lean_dec(v_r_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1(lean_object* v_r_115_, lean_object* v_i_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___redArg(v_i_116_, v_a_117_, v_a_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1___boxed(lean_object* v_r_120_, lean_object* v_i_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_PacketSums_vdm_spec__0_spec__0_spec__1(v_r_120_, v_i_121_, v_a_122_, v_a_123_);
lean_dec(v_i_121_);
lean_dec(v_r_120_);
return v_res_124_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_JacquetSubsetSums_JacquetSubsetSum(uint8_t builtin) {
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
