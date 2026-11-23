// Lean compiler output
// Module: Formalism.PieriBlockIdeals.PieriColumnMinors.LrfcApplyWordAppendSingle
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.FinalD public import Formalism.GradedWeylDivisibility.StatementE
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1___closed__0 = (const lean_object*)&lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__L(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__off___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__off(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__off___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__0(lean_object* v_s_1_, lean_object* v_r_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
if (lean_obj_tag(v_a_3_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_s_1_);
v___x_5_ = lean_array_to_list(v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_22_; 
v_head_6_ = lean_ctor_get(v_a_3_, 0);
v_tail_7_ = lean_ctor_get(v_a_3_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_22_ == 0)
{
v___x_9_ = v_a_3_;
v_isShared_10_ = v_isSharedCheck_22_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_tail_7_);
lean_inc(v_head_6_);
lean_dec(v_a_3_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_22_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_lt(v_s_1_, v_head_6_);
if (v___x_11_ == 0)
{
lean_del_object(v___x_9_);
lean_dec(v_head_6_);
v_a_3_ = v_tail_7_;
goto _start;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_lt(v_s_1_, v_r_2_);
if (v___x_13_ == 0)
{
lean_del_object(v___x_9_);
lean_dec(v_head_6_);
v_a_3_ = v_tail_7_;
goto _start;
}
else
{
lean_object* v___x_16_; 
lean_inc(v_s_1_);
lean_inc(v_head_6_);
if (v_isShared_10_ == 0)
{
lean_ctor_set_tag(v___x_9_, 0);
lean_ctor_set(v___x_9_, 1, v_s_1_);
v___x_16_ = v___x_9_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_head_6_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_s_1_);
v___x_16_ = v_reuseFailAlloc_21_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v_head_6_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
lean_inc(v_s_1_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_s_1_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v___x_19_ = lean_array_push(v_a_4_, v___x_18_);
v_a_3_ = v_tail_7_;
v_a_4_ = v___x_19_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__0___boxed(lean_object* v_s_23_, lean_object* v_r_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_List_filterMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__0(v_s_23_, v_r_24_, v_a_25_, v_a_26_);
lean_dec(v_r_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1(lean_object* v_r_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
if (lean_obj_tag(v_a_31_) == 0)
{
lean_object* v___x_33_; 
lean_dec(v_r_30_);
v___x_33_ = lean_array_to_list(v_a_32_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_head_34_ = lean_ctor_get(v_a_31_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_a_31_, 1);
lean_inc(v_tail_35_);
lean_dec_ref_known(v_a_31_, 2);
lean_inc(v_r_30_);
v___x_36_ = l_List_finRange(v_r_30_);
v___x_37_ = ((lean_object*)(lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1___closed__0));
v___x_38_ = lp_tree_List_filterMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__0(v_head_34_, v_r_30_, v___x_36_, v___x_37_);
v___x_39_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_32_, v___x_38_);
v_a_31_ = v_tail_35_;
v_a_32_ = v___x_39_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__L(lean_object* v_r_41_, lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = l_List_finRange(v_n_42_);
v___x_44_ = l_List_reverse___redArg(v___x_43_);
v___x_45_ = ((lean_object*)(lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1___closed__0));
v___x_46_ = lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_CohomologicalDescent_LR_lrf__L_spec__1(v_r_41_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1_spec__2(lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
if (lean_obj_tag(v_a_47_) == 0)
{
lean_object* v___x_49_; 
v___x_49_ = l_List_reverse___redArg(v_a_48_);
return v___x_49_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_63_; 
v_head_50_ = lean_ctor_get(v_a_47_, 0);
v_tail_51_ = lean_ctor_get(v_a_47_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_a_47_);
if (v_isSharedCheck_63_ == 0)
{
v___x_53_ = v_a_47_;
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_tail_51_);
lean_inc(v_head_50_);
lean_dec(v_a_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_fst_55_; lean_object* v_snd_56_; uint8_t v___x_57_; 
v_fst_55_ = lean_ctor_get(v_head_50_, 0);
v_snd_56_ = lean_ctor_get(v_head_50_, 1);
v___x_57_ = lean_nat_dec_lt(v_snd_56_, v_fst_55_);
if (v___x_57_ == 0)
{
lean_del_object(v___x_53_);
lean_dec(v_head_50_);
v_a_47_ = v_tail_51_;
goto _start;
}
else
{
lean_object* v___x_60_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v_a_48_);
v___x_60_ = v___x_53_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_head_50_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_a_48_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
v_a_47_ = v_tail_51_;
v_a_48_ = v___x_60_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1___redArg(lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1_spec__2(v_s_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg___lam__0(lean_object* v_toFun_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_fst_69_; lean_object* v_snd_70_; uint8_t v___x_71_; 
v_fst_69_ = lean_ctor_get(v_a_68_, 0);
v_snd_70_ = lean_ctor_get(v_a_68_, 1);
v___x_71_ = lean_nat_dec_lt(v_snd_70_, v_fst_69_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_a_68_);
lean_dec(v_toFun_67_);
v___x_72_ = lean_unsigned_to_nat(0u);
return v___x_72_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_apply_1(v_toFun_67_, v_a_68_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg(lean_object* v_f_74_){
_start:
{
lean_object* v_support_75_; lean_object* v_toFun_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_85_; 
v_support_75_ = lean_ctor_get(v_f_74_, 0);
v_toFun_76_ = lean_ctor_get(v_f_74_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_f_74_);
if (v_isSharedCheck_85_ == 0)
{
v___x_78_ = v_f_74_;
v_isShared_79_ = v_isSharedCheck_85_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_toFun_76_);
lean_inc(v_support_75_);
lean_dec(v_f_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_85_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___f_80_ = lean_alloc_closure((void*)(lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_80_, 0, v_toFun_76_);
v___x_81_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1___redArg(v_support_75_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___f_80_);
lean_ctor_set(v___x_78_, 0, v___x_81_);
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___f_80_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__off___redArg(lean_object* v_m_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg(v_m_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__off(lean_object* v_r_88_, lean_object* v_n_89_, lean_object* v_m_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg(v_m_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CohomologicalDescent_LR_lrf__off___boxed(lean_object* v_r_92_, lean_object* v_n_93_, lean_object* v_m_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_tree_Formalism_CohomologicalDescent_LR_lrf__off(v_r_92_, v_n_93_, v_m_94_);
lean_dec(v_n_93_);
lean_dec(v_r_92_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0(lean_object* v_p_96_, lean_object* v_f_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_tree_Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0___redArg(v_f_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0___redArg(lean_object* v_s_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1___redArg(v_s_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0(lean_object* v_p_101_, lean_object* v_s_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1___redArg(v_s_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1(lean_object* v_p_104_, lean_object* v_s_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Finsupp_filter___at___00Formalism_CohomologicalDescent_LR_lrf__off_spec__0_spec__0_spec__1___redArg(v_s_105_);
return v___x_106_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalD(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementE(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FinalD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
