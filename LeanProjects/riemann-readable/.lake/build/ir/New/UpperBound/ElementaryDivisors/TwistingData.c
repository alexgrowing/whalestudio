// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.TwistingData
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.Basic public import Lib.General.Groups.BesselGroups
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
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_RingHom_comp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_defectThreshold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_defectThreshold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_rootVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_rootVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_rootVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock___redArg(lean_object* v_r_1_, lean_object* v_b_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_b_2_, v_r_1_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(1u);
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(0u);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock___redArg___boxed(lean_object* v_r_6_, lean_object* v_b_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_twoBlock___redArg(v_r_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_r_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock(lean_object* v_k_9_, lean_object* v_r_10_, lean_object* v_b_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_GRH_New_twoBlock___redArg(v_r_10_, v_b_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twoBlock___boxed(lean_object* v_k_13_, lean_object* v_r_14_, lean_object* v_b_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_twoBlock(v_k_13_, v_r_14_, v_b_15_);
lean_dec(v_b_15_);
lean_dec(v_r_14_);
lean_dec(v_k_13_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_defectThreshold(lean_object* v_k_17_, lean_object* v_c_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_unsigned_to_nat(3u);
v___x_20_ = lean_nat_mul(v___x_19_, v_k_17_);
v___x_21_ = lean_nat_mul(v___x_20_, v_c_18_);
lean_dec(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_defectThreshold___boxed(lean_object* v_k_22_, lean_object* v_c_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_defectThreshold(v_k_22_, v_c_23_);
lean_dec(v_c_23_);
lean_dec(v_k_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P___redArg(lean_object* v_T_25_){
_start:
{
lean_object* v_p_26_; lean_object* v_frobExp_27_; lean_object* v___x_28_; 
v_p_26_ = lean_ctor_get(v_T_25_, 0);
v_frobExp_27_ = lean_ctor_get(v_T_25_, 1);
v___x_28_ = lean_nat_pow(v_p_26_, v_frobExp_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P___redArg___boxed(lean_object* v_T_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_FrobeniusCycle_P___redArg(v_T_29_);
lean_dec_ref(v_T_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P(lean_object* v_N_31_, lean_object* v_W_32_, lean_object* v_R_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_T_37_){
_start:
{
lean_object* v_p_38_; lean_object* v_frobExp_39_; lean_object* v___x_40_; 
v_p_38_ = lean_ctor_get(v_T_37_, 0);
v_frobExp_39_ = lean_ctor_get(v_T_37_, 1);
v___x_40_ = lean_nat_pow(v_p_38_, v_frobExp_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_P___boxed(lean_object* v_N_41_, lean_object* v_W_42_, lean_object* v_R_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_T_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_FrobeniusCycle_P(v_N_41_, v_W_42_, v_R_43_, v_inst_44_, v_inst_45_, v_inst_46_, v_T_47_);
lean_dec_ref(v_T_47_);
lean_dec_ref(v_inst_46_);
lean_dec_ref(v_inst_44_);
lean_dec(v_N_41_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q___redArg(lean_object* v_N_49_, lean_object* v_T_50_){
_start:
{
lean_object* v_p_51_; lean_object* v_frobExp_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_p_51_ = lean_ctor_get(v_T_50_, 0);
v_frobExp_52_ = lean_ctor_get(v_T_50_, 1);
v___x_53_ = lean_nat_pow(v_p_51_, v_frobExp_52_);
v___x_54_ = lean_nat_pow(v___x_53_, v_N_49_);
lean_dec(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q___redArg___boxed(lean_object* v_N_55_, lean_object* v_T_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_GRH_New_FrobeniusCycle_q___redArg(v_N_55_, v_T_56_);
lean_dec_ref(v_T_56_);
lean_dec(v_N_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q(lean_object* v_N_58_, lean_object* v_W_59_, lean_object* v_R_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_T_64_){
_start:
{
lean_object* v_p_65_; lean_object* v_frobExp_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_p_65_ = lean_ctor_get(v_T_64_, 0);
v_frobExp_66_ = lean_ctor_get(v_T_64_, 1);
v___x_67_ = lean_nat_pow(v_p_65_, v_frobExp_66_);
v___x_68_ = lean_nat_pow(v___x_67_, v_N_58_);
lean_dec(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_q___boxed(lean_object* v_N_69_, lean_object* v_W_70_, lean_object* v_R_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_T_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_FrobeniusCycle_q(v_N_69_, v_W_70_, v_R_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_T_75_);
lean_dec_ref(v_T_75_);
lean_dec_ref(v_inst_74_);
lean_dec_ref(v_inst_72_);
lean_dec(v_N_69_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_map___redArg(lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_00_u03c6_80_, lean_object* v_T_81_){
_start:
{
lean_object* v_p_82_; lean_object* v_frobExp_83_; lean_object* v_embedding_84_; lean_object* v_isEven_85_; lean_object* v_sqrtPrime_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_102_; 
v_p_82_ = lean_ctor_get(v_T_81_, 0);
v_frobExp_83_ = lean_ctor_get(v_T_81_, 1);
v_embedding_84_ = lean_ctor_get(v_T_81_, 2);
v_isEven_85_ = lean_ctor_get(v_T_81_, 3);
v_sqrtPrime_86_ = lean_ctor_get(v_T_81_, 4);
v_isSharedCheck_102_ = !lean_is_exclusive(v_T_81_);
if (v_isSharedCheck_102_ == 0)
{
v___x_88_ = v_T_81_;
v_isShared_89_ = v_isSharedCheck_102_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_sqrtPrime_86_);
lean_inc(v_isEven_85_);
lean_inc(v_embedding_84_);
lean_inc(v_frobExp_83_);
lean_inc(v_p_82_);
lean_dec(v_T_81_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_102_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v_toSemiring_90_; lean_object* v___x_91_; lean_object* v_toSemiring_92_; lean_object* v___x_93_; lean_object* v_toSemiring_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v_toSemiring_90_ = lean_ctor_get(v_inst_77_, 0);
lean_inc_ref(v_toSemiring_90_);
lean_dec_ref(v_inst_77_);
v___x_91_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_90_);
v_toSemiring_92_ = lean_ctor_get(v_inst_78_, 0);
lean_inc_ref(v_toSemiring_92_);
lean_dec_ref(v_inst_78_);
v___x_93_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_92_);
v_toSemiring_94_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_toSemiring_94_);
lean_dec_ref(v_inst_79_);
v___x_95_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_94_);
lean_inc(v_00_u03c6_80_);
v___x_96_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___boxed), 8, 7);
lean_closure_set(v___x_96_, 0, lean_box(0));
lean_closure_set(v___x_96_, 1, lean_box(0));
lean_closure_set(v___x_96_, 2, lean_box(0));
lean_closure_set(v___x_96_, 3, v___x_91_);
lean_closure_set(v___x_96_, 4, v___x_93_);
lean_closure_set(v___x_96_, 5, v___x_95_);
lean_closure_set(v___x_96_, 6, v_00_u03c6_80_);
v___x_97_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_97_, 0, lean_box(0));
lean_closure_set(v___x_97_, 1, lean_box(0));
lean_closure_set(v___x_97_, 2, lean_box(0));
lean_closure_set(v___x_97_, 3, v___x_96_);
lean_closure_set(v___x_97_, 4, v_embedding_84_);
v___x_98_ = lean_apply_1(v_00_u03c6_80_, v_sqrtPrime_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_98_);
lean_ctor_set(v___x_88_, 2, v___x_97_);
v___x_100_ = v___x_88_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_p_82_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_frobExp_83_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_isEven_85_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_map(lean_object* v_N_103_, lean_object* v_W_104_, lean_object* v_R_105_, lean_object* v_R_x27_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_00_u03c6_111_, lean_object* v_T_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lp_GRH_New_FrobeniusCycle_map___redArg(v_inst_107_, v_inst_109_, v_inst_110_, v_00_u03c6_111_, v_T_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_map___boxed(lean_object* v_N_114_, lean_object* v_W_115_, lean_object* v_R_116_, lean_object* v_R_x27_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_00_u03c6_122_, lean_object* v_T_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_GRH_New_FrobeniusCycle_map(v_N_114_, v_W_115_, v_R_116_, v_R_x27_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_00_u03c6_122_, v_T_123_);
lean_dec(v_N_114_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__0(lean_object* v_embedding_125_, lean_object* v_s_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_apply_2(v_embedding_125_, v_s_126_, v___y_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__1(uint8_t v___x_129_, lean_object* v_g_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
if (v___x_129_ == 0)
{
lean_object* v_inv_133_; lean_object* v___x_134_; 
v_inv_133_ = lean_ctor_get(v_g_130_, 1);
lean_inc(v_inv_133_);
lean_dec_ref(v_g_130_);
v___x_134_ = lp_mathlib_Matrix_transpose___redArg(v_inv_133_, v___y_131_, v___y_132_);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
v_val_135_ = lean_ctor_get(v_g_130_, 0);
lean_inc(v_val_135_);
lean_dec_ref(v_g_130_);
v___x_136_ = lean_apply_2(v_val_135_, v___y_131_, v___y_132_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__1___boxed(lean_object* v___x_137_, lean_object* v_g_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
uint8_t v___x_116__boxed_141_; lean_object* v_res_142_; 
v___x_116__boxed_141_ = lean_unbox(v___x_137_);
v_res_142_ = lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__1(v___x_116__boxed_141_, v_g_138_, v___y_139_, v___y_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__2(lean_object* v_T_143_, lean_object* v_s_144_, lean_object* v_g_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_embedding_148_; lean_object* v_isEven_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___y_152_; lean_object* v___x_153_; 
v_embedding_148_ = lean_ctor_get(v_T_143_, 2);
lean_inc(v_embedding_148_);
v_isEven_149_ = lean_ctor_get(v_T_143_, 3);
lean_inc_ref(v_isEven_149_);
lean_dec_ref(v_T_143_);
lean_inc(v_s_144_);
v___f_150_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_150_, 0, v_embedding_148_);
lean_closure_set(v___f_150_, 1, v_s_144_);
v___x_151_ = lean_apply_1(v_isEven_149_, v_s_144_);
v___y_152_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___y_152_, 0, v___x_151_);
lean_closure_set(v___y_152_, 1, v_g_145_);
v___x_153_ = lp_mathlib_Matrix_map___redArg(v___y_152_, v___f_150_, v___y_146_, v___y_147_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___redArg(lean_object* v_T_154_, lean_object* v_s_155_){
_start:
{
lean_object* v___f_156_; 
v___f_156_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__2), 5, 2);
lean_closure_set(v___f_156_, 0, v_T_154_);
lean_closure_set(v___f_156_, 1, v_s_155_);
return v___f_156_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix(lean_object* v_k_157_, lean_object* v_N_158_, lean_object* v_W_159_, lean_object* v_R_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_T_164_, lean_object* v_s_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterMatrix___redArg___lam__2), 5, 2);
lean_closure_set(v___f_166_, 0, v_T_164_);
lean_closure_set(v___f_166_, 1, v_s_165_);
return v___f_166_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterMatrix___boxed(lean_object* v_k_167_, lean_object* v_N_168_, lean_object* v_W_169_, lean_object* v_R_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_T_174_, lean_object* v_s_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_GRH_New_FrobeniusCycle_letterMatrix(v_k_167_, v_N_168_, v_W_169_, v_R_170_, v_inst_171_, v_inst_172_, v_inst_173_, v_T_174_, v_s_175_);
lean_dec_ref(v_inst_173_);
lean_dec_ref(v_inst_171_);
lean_dec(v_N_168_);
lean_dec(v_k_167_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(lean_object* v_T_177_, lean_object* v_r_178_, lean_object* v_x_179_){
_start:
{
uint8_t v___y_181_; lean_object* v_isEven_184_; lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_isEven_184_ = lean_ctor_get(v_T_177_, 3);
lean_inc_ref(v_isEven_184_);
lean_dec_ref(v_T_177_);
v_fst_185_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_fst_185_);
v_snd_186_ = lean_ctor_get(v_x_179_, 1);
lean_inc(v_snd_186_);
lean_dec_ref(v_x_179_);
v___x_187_ = lean_apply_1(v_isEven_184_, v_snd_186_);
v___x_188_ = lean_nat_dec_le(v_r_178_, v_fst_185_);
lean_dec(v_fst_185_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; 
v___x_189_ = lean_unbox(v___x_187_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(1u);
return v___x_190_;
}
else
{
v___y_181_ = v___x_188_;
goto v___jp_180_;
}
}
else
{
uint8_t v___x_191_; 
v___x_191_ = lean_unbox(v___x_187_);
v___y_181_ = v___x_191_;
goto v___jp_180_;
}
v___jp_180_:
{
if (v___y_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(0u);
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(1u);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___redArg___boxed(lean_object* v_T_192_, lean_object* v_r_193_, lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(v_T_192_, v_r_193_, v_x_194_);
lean_dec(v_r_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator(lean_object* v_k_196_, lean_object* v_N_197_, lean_object* v_W_198_, lean_object* v_R_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_T_203_, lean_object* v_r_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(v_T_203_, v_r_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___boxed(lean_object* v_k_207_, lean_object* v_N_208_, lean_object* v_W_209_, lean_object* v_R_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_T_214_, lean_object* v_r_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = lp_GRH_New_FrobeniusCycle_deepIndicator(v_k_207_, v_N_208_, v_W_209_, v_R_210_, v_inst_211_, v_inst_212_, v_inst_213_, v_T_214_, v_r_215_, v_x_216_);
lean_dec(v_r_215_);
lean_dec_ref(v_inst_213_);
lean_dec_ref(v_inst_211_);
lean_dec(v_N_208_);
lean_dec(v_k_207_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_rootVar___redArg(lean_object* v_T_218_, lean_object* v_a_219_, lean_object* v_a_x27_220_, lean_object* v_s_221_){
_start:
{
lean_object* v_isEven_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_isEven_222_ = lean_ctor_get(v_T_218_, 3);
lean_inc_ref(v_isEven_222_);
lean_dec_ref(v_T_218_);
lean_inc(v_s_221_);
v___x_223_ = lean_apply_1(v_isEven_222_, v_s_221_);
v___x_224_ = lean_unbox(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec(v_a_x27_220_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_a_219_);
lean_ctor_set(v___x_225_, 1, v_s_221_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
lean_dec(v_a_219_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_x27_220_);
lean_ctor_set(v___x_226_, 1, v_s_221_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_rootVar(lean_object* v_k_227_, lean_object* v_N_228_, lean_object* v_W_229_, lean_object* v_R_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_T_234_, lean_object* v_a_235_, lean_object* v_a_x27_236_, lean_object* v_s_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lp_GRH_New_FrobeniusCycle_rootVar___redArg(v_T_234_, v_a_235_, v_a_x27_236_, v_s_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_rootVar___boxed(lean_object* v_k_239_, lean_object* v_N_240_, lean_object* v_W_241_, lean_object* v_R_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_T_246_, lean_object* v_a_247_, lean_object* v_a_x27_248_, lean_object* v_s_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = lp_GRH_New_FrobeniusCycle_rootVar(v_k_239_, v_N_240_, v_W_241_, v_R_242_, v_inst_243_, v_inst_244_, v_inst_245_, v_T_246_, v_a_247_, v_a_x27_248_, v_s_249_);
lean_dec_ref(v_inst_245_);
lean_dec_ref(v_inst_243_);
lean_dec(v_N_240_);
lean_dec(v_k_239_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn___redArg(){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn___redArg___boxed(lean_object* v___dummy_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = lp_GRH_New_FrobeniusCycle_translatesIn___redArg();
return v_res_254_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn(lean_object* v_k_255_, lean_object* v_N_256_, lean_object* v_W_257_, lean_object* v_R_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_T_263_, lean_object* v_n_264_, lean_object* v_00_u03c4_265_, lean_object* v_I_266_, lean_object* v_B_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_translatesIn___boxed(lean_object* v_k_269_, lean_object* v_N_270_, lean_object* v_W_271_, lean_object* v_R_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_T_277_, lean_object* v_n_278_, lean_object* v_00_u03c4_279_, lean_object* v_I_280_, lean_object* v_B_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = lp_GRH_New_FrobeniusCycle_translatesIn(v_k_269_, v_N_270_, v_W_271_, v_R_272_, v_inst_273_, v_inst_274_, v_inst_275_, v_inst_276_, v_T_277_, v_n_278_, v_00_u03c4_279_, v_I_280_, v_B_281_);
lean_dec_ref(v_00_u03c4_279_);
lean_dec(v_n_278_);
lean_dec_ref(v_T_277_);
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_273_);
lean_dec(v_N_270_);
lean_dec(v_k_269_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions___redArg(){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_box(0);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions___redArg___boxed(lean_object* v___dummy_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = lp_GRH_New_FrobeniusCycle_defectConditions___redArg();
return v_res_286_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions(lean_object* v_k_287_, lean_object* v_N_288_, lean_object* v_W_289_, lean_object* v_R_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_T_295_, lean_object* v_n_296_, lean_object* v_a_297_, lean_object* v_a_x27_298_, lean_object* v_I_299_, lean_object* v_h_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_defectConditions___boxed(lean_object* v_k_302_, lean_object* v_N_303_, lean_object* v_W_304_, lean_object* v_R_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_T_310_, lean_object* v_n_311_, lean_object* v_a_312_, lean_object* v_a_x27_313_, lean_object* v_I_314_, lean_object* v_h_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = lp_GRH_New_FrobeniusCycle_defectConditions(v_k_302_, v_N_303_, v_W_304_, v_R_305_, v_inst_306_, v_inst_307_, v_inst_308_, v_inst_309_, v_T_310_, v_n_311_, v_a_312_, v_a_x27_313_, v_I_314_, v_h_315_);
lean_dec(v_h_315_);
lean_dec(v_a_x27_313_);
lean_dec(v_a_312_);
lean_dec(v_n_311_);
lean_dec_ref(v_T_310_);
lean_dec_ref(v_inst_308_);
lean_dec_ref(v_inst_306_);
lean_dec(v_N_303_);
lean_dec(v_k_302_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms___redArg(){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms___redArg___boxed(lean_object* v___dummy_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = lp_GRH_New_FrobeniusCycle_deepForms___redArg();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms(lean_object* v_N_321_, lean_object* v_W_322_, lean_object* v_R_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_T_328_, lean_object* v_k_329_, lean_object* v_n_330_, lean_object* v_r_331_, lean_object* v_d_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_deepForms___boxed(lean_object* v_N_334_, lean_object* v_W_335_, lean_object* v_R_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_T_341_, lean_object* v_k_342_, lean_object* v_n_343_, lean_object* v_r_344_, lean_object* v_d_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = lp_GRH_New_FrobeniusCycle_deepForms(v_N_334_, v_W_335_, v_R_336_, v_inst_337_, v_inst_338_, v_inst_339_, v_inst_340_, v_T_341_, v_k_342_, v_n_343_, v_r_344_, v_d_345_);
lean_dec(v_d_345_);
lean_dec(v_r_344_);
lean_dec(v_n_343_);
lean_dec(v_k_342_);
lean_dec_ref(v_T_341_);
lean_dec_ref(v_inst_339_);
lean_dec_ref(v_inst_337_);
lean_dec(v_N_334_);
return v_res_346_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_BesselGroups(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_TwistingData(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_SchurModule_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Groups_BesselGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
