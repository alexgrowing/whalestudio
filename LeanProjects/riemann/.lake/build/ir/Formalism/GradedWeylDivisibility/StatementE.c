// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.StatementE
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.FinalD
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1___closed__0 = (const lean_object*)&lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_wordOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_GradedWeylDivisibility_transposeWord_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_transposeWord___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_transposeWord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_transposeWord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_bDual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_bDual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame___redArg(lean_object* v_inst_1_, lean_object* v_v_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; uint8_t v___x_5_; 
v_fst_3_ = lean_ctor_get(v_v_2_, 0);
v_snd_4_ = lean_ctor_get(v_v_2_, 1);
v___x_5_ = lean_nat_dec_eq(v_fst_3_, v_snd_4_);
if (v___x_5_ == 0)
{
lean_object* v_toSemiring_6_; lean_object* v___x_7_; lean_object* v_toZero_8_; 
v_toSemiring_6_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_6_);
lean_dec_ref(v_inst_1_);
v___x_7_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_6_);
v_toZero_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toZero_8_);
lean_dec_ref(v___x_7_);
return v_toZero_8_;
}
else
{
lean_object* v___x_9_; lean_object* v_toAddMonoidWithOne_10_; lean_object* v_toOne_11_; 
v___x_9_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc_ref(v_toAddMonoidWithOne_10_);
lean_dec_ref(v___x_9_);
v_toOne_11_ = lean_ctor_get(v_toAddMonoidWithOne_10_, 2);
lean_inc(v_toOne_11_);
lean_dec_ref(v_toAddMonoidWithOne_10_);
return v_toOne_11_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame___redArg___boxed(lean_object* v_inst_12_, lean_object* v_v_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_GradedWeylDivisibility_idFrame___redArg(v_inst_12_, v_v_13_);
lean_dec_ref(v_v_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame(lean_object* v_R_15_, lean_object* v_inst_16_, lean_object* v_r_17_, lean_object* v_n_18_, lean_object* v_v_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_Formalism_GradedWeylDivisibility_idFrame___redArg(v_inst_16_, v_v_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_idFrame___boxed(lean_object* v_R_21_, lean_object* v_inst_22_, lean_object* v_r_23_, lean_object* v_n_24_, lean_object* v_v_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_GradedWeylDivisibility_idFrame(v_R_21_, v_inst_22_, v_r_23_, v_n_24_, v_v_25_);
lean_dec_ref(v_v_25_);
lean_dec(v_n_24_);
lean_dec(v_r_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__0(lean_object* v_s_27_, lean_object* v_r_28_, lean_object* v_e_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
if (lean_obj_tag(v_a_30_) == 0)
{
lean_object* v___x_32_; 
lean_dec_ref(v_e_29_);
lean_dec(v_s_27_);
v___x_32_ = lean_array_to_list(v_a_31_);
return v___x_32_;
}
else
{
lean_object* v_head_33_; lean_object* v_tail_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_51_; 
v_head_33_ = lean_ctor_get(v_a_30_, 0);
v_tail_34_ = lean_ctor_get(v_a_30_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_a_30_);
if (v_isSharedCheck_51_ == 0)
{
v___x_36_ = v_a_30_;
v_isShared_37_ = v_isSharedCheck_51_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_tail_34_);
lean_inc(v_head_33_);
lean_dec(v_a_30_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_51_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
uint8_t v___x_38_; 
v___x_38_ = lean_nat_dec_lt(v_s_27_, v_head_33_);
if (v___x_38_ == 0)
{
lean_del_object(v___x_36_);
lean_dec(v_head_33_);
v_a_30_ = v_tail_34_;
goto _start;
}
else
{
uint8_t v___x_40_; 
v___x_40_ = lean_nat_dec_lt(v_s_27_, v_r_28_);
if (v___x_40_ == 0)
{
lean_del_object(v___x_36_);
lean_dec(v_head_33_);
v_a_30_ = v_tail_34_;
goto _start;
}
else
{
lean_object* v_toFun_42_; lean_object* v___x_44_; 
v_toFun_42_ = lean_ctor_get(v_e_29_, 1);
lean_inc(v_s_27_);
lean_inc(v_head_33_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 0);
lean_ctor_set(v___x_36_, 1, v_s_27_);
v___x_44_ = v___x_36_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_head_33_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_s_27_);
v___x_44_ = v_reuseFailAlloc_50_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_inc(v_toFun_42_);
v___x_45_ = lean_apply_1(v_toFun_42_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_head_33_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
lean_inc(v_s_27_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_s_27_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_array_push(v_a_31_, v___x_47_);
v_a_30_ = v_tail_34_;
v_a_31_ = v___x_48_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__0___boxed(lean_object* v_s_52_, lean_object* v_r_53_, lean_object* v_e_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_List_filterMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__0(v_s_52_, v_r_53_, v_e_54_, v_a_55_, v_a_56_);
lean_dec(v_r_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1(lean_object* v_r_60_, lean_object* v_e_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v___x_64_; 
lean_dec_ref(v_e_61_);
lean_dec(v_r_60_);
v___x_64_ = lean_array_to_list(v_a_63_);
return v___x_64_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_head_65_ = lean_ctor_get(v_a_62_, 0);
lean_inc(v_head_65_);
v_tail_66_ = lean_ctor_get(v_a_62_, 1);
lean_inc(v_tail_66_);
lean_dec_ref_known(v_a_62_, 2);
lean_inc(v_r_60_);
v___x_67_ = l_List_finRange(v_r_60_);
v___x_68_ = ((lean_object*)(lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1___closed__0));
lean_inc_ref(v_e_61_);
v___x_69_ = lp_tree_List_filterMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__0(v_head_65_, v_r_60_, v_e_61_, v___x_67_, v___x_68_);
v___x_70_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_63_, v___x_69_);
v_a_62_ = v_tail_66_;
v_a_63_ = v___x_70_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_wordOf(lean_object* v_r_72_, lean_object* v_n_73_, lean_object* v_e_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = l_List_finRange(v_n_73_);
v___x_76_ = l_List_reverse___redArg(v___x_75_);
v___x_77_ = ((lean_object*)(lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1___closed__0));
v___x_78_ = lp_tree___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Formalism_GradedWeylDivisibility_wordOf_spec__1(v_r_72_, v_e_74_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_mapTR_loop___at___00Formalism_GradedWeylDivisibility_transposeWord_spec__0(lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
if (lean_obj_tag(v_a_79_) == 0)
{
lean_object* v___x_81_; 
v___x_81_ = l_List_reverse___redArg(v_a_80_);
return v___x_81_;
}
else
{
lean_object* v_head_82_; lean_object* v_snd_83_; lean_object* v_tail_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_110_; 
v_head_82_ = lean_ctor_get(v_a_79_, 0);
lean_inc(v_head_82_);
v_snd_83_ = lean_ctor_get(v_head_82_, 1);
lean_inc(v_snd_83_);
v_tail_84_ = lean_ctor_get(v_a_79_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v_a_79_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v_a_79_, 0);
lean_dec(v_unused_111_);
v___x_86_ = v_a_79_;
v_isShared_87_ = v_isSharedCheck_110_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_tail_84_);
lean_dec(v_a_79_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_110_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_fst_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_108_; 
v_fst_88_ = lean_ctor_get(v_head_82_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_head_82_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_head_82_, 1);
lean_dec(v_unused_109_);
v___x_90_ = v_head_82_;
v_isShared_91_ = v_isSharedCheck_108_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_fst_88_);
lean_dec(v_head_82_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_108_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_fst_92_; lean_object* v_snd_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_107_; 
v_fst_92_ = lean_ctor_get(v_snd_83_, 0);
v_snd_93_ = lean_ctor_get(v_snd_83_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_snd_83_);
if (v_isSharedCheck_107_ == 0)
{
v___x_95_ = v_snd_83_;
v_isShared_96_ = v_isSharedCheck_107_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_snd_93_);
lean_inc(v_fst_92_);
lean_dec(v_snd_83_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_107_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v_fst_88_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_fst_88_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_snd_93_);
v___x_98_ = v_reuseFailAlloc_106_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_98_);
lean_ctor_set(v___x_90_, 0, v_fst_92_);
v___x_100_ = v___x_90_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_fst_92_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_a_80_);
lean_ctor_set(v___x_86_, 0, v___x_100_);
v___x_102_ = v___x_86_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_a_80_);
v___x_102_ = v_reuseFailAlloc_104_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
v_a_79_ = v_tail_84_;
v_a_80_ = v___x_102_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_transposeWord___redArg(lean_object* v_w_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_box(0);
v___x_114_ = lp_tree_List_mapTR_loop___at___00Formalism_GradedWeylDivisibility_transposeWord_spec__0(v_w_112_, v___x_113_);
v___x_115_ = l_List_reverse___redArg(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_transposeWord(lean_object* v_r_116_, lean_object* v_w_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lp_tree_Formalism_GradedWeylDivisibility_transposeWord___redArg(v_w_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_transposeWord___boxed(lean_object* v_r_119_, lean_object* v_w_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_Formalism_GradedWeylDivisibility_transposeWord(v_r_119_, v_w_120_);
lean_dec(v_r_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_bDual(lean_object* v_r_122_, lean_object* v_n_123_, lean_object* v_hn_124_, lean_object* v_00_u03bd_125_, lean_object* v_M_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_bDual___boxed(lean_object* v_r_128_, lean_object* v_n_129_, lean_object* v_hn_130_, lean_object* v_00_u03bd_131_, lean_object* v_M_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = lp_tree_Formalism_GradedWeylDivisibility_bDual(v_r_128_, v_n_129_, v_hn_130_, v_00_u03bd_131_, v_M_132_);
lean_dec_ref(v_00_u03bd_131_);
lean_dec(v_n_129_);
lean_dec(v_r_128_);
return v_res_133_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FinalD(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementE(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
