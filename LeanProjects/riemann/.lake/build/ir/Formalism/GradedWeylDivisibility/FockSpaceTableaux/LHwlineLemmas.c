// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementB public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* l_Fin_decLt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__elim___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_, lean_object* v_t_4_, lean_object* v_x_5_, lean_object* v_v_6_){
_start:
{
lean_object* v_fst_7_; lean_object* v_snd_8_; uint8_t v___x_9_; 
v_fst_7_ = lean_ctor_get(v_v_6_, 0);
v_snd_8_ = lean_ctor_get(v_v_6_, 1);
v___x_9_ = lean_nat_dec_eq(v_fst_7_, v_b_3_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_t_4_);
lean_dec(v_a_2_);
v___x_10_ = lean_apply_1(v_x_5_, v_v_6_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toSemiring_13_; lean_object* v___x_14_; lean_object* v_toMul_15_; lean_object* v_toAdd_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_27_; 
lean_inc(v_snd_8_);
v___x_11_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_12_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_11_);
v_toSemiring_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc_ref(v_toSemiring_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_13_);
v_toMul_15_ = lean_ctor_get(v___x_14_, 0);
v_toAdd_16_ = lean_ctor_get(v___x_14_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_27_ == 0)
{
v___x_18_ = v___x_14_;
v_isShared_19_ = v_isSharedCheck_27_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_toAdd_16_);
lean_inc(v_toMul_15_);
lean_dec(v___x_14_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_27_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; lean_object* v___x_22_; 
lean_inc(v_x_5_);
v___x_20_ = lean_apply_1(v_x_5_, v_v_6_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v_snd_8_);
lean_ctor_set(v___x_18_, 0, v_a_2_);
v___x_22_ = v___x_18_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_2_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_snd_8_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_apply_1(v_x_5_, v___x_22_);
v___x_24_ = lean_apply_2(v_toMul_15_, v_t_4_, v___x_23_);
v___x_25_ = lean_apply_2(v_toAdd_16_, v___x_20_, v___x_24_);
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___redArg___boxed(lean_object* v_inst_28_, lean_object* v_a_29_, lean_object* v_b_30_, lean_object* v_t_31_, lean_object* v_x_32_, lean_object* v_v_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___redArg(v_inst_28_, v_a_29_, v_b_30_, v_t_31_, v_x_32_, v_v_33_);
lean_dec(v_b_30_);
lean_dec_ref(v_inst_28_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp(lean_object* v_K_35_, lean_object* v_inst_36_, lean_object* v_r_37_, lean_object* v_n_38_, lean_object* v_a_39_, lean_object* v_b_40_, lean_object* v_t_41_, lean_object* v_x_42_, lean_object* v_v_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___redArg(v_inst_36_, v_a_39_, v_b_40_, v_t_41_, v_x_42_, v_v_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp___boxed(lean_object* v_K_45_, lean_object* v_inst_46_, lean_object* v_r_47_, lean_object* v_n_48_, lean_object* v_a_49_, lean_object* v_b_50_, lean_object* v_t_51_, lean_object* v_x_52_, lean_object* v_v_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__rowOp(v_K_45_, v_inst_46_, v_r_47_, v_n_48_, v_a_49_, v_b_50_, v_t_51_, v_x_52_, v_v_53_);
lean_dec(v_b_50_);
lean_dec(v_n_48_);
lean_dec(v_r_47_);
lean_dec_ref(v_inst_46_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___redArg(lean_object* v_inst_55_, lean_object* v_l_56_, lean_object* v_j_57_, lean_object* v_c_58_, lean_object* v_x_59_, lean_object* v_v_60_){
_start:
{
lean_object* v_fst_61_; lean_object* v_snd_62_; uint8_t v___x_63_; 
v_fst_61_ = lean_ctor_get(v_v_60_, 0);
v_snd_62_ = lean_ctor_get(v_v_60_, 1);
v___x_63_ = lean_nat_dec_eq(v_snd_62_, v_j_57_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
lean_dec(v_c_58_);
lean_dec(v_l_56_);
v___x_64_ = lean_apply_1(v_x_59_, v_v_60_);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_toSemiring_67_; lean_object* v___x_68_; lean_object* v_toMul_69_; lean_object* v_toAdd_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_81_; 
lean_inc(v_fst_61_);
v___x_65_ = lp_mathlib_Field_toSemifield___redArg(v_inst_55_);
v___x_66_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_65_);
v_toSemiring_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_toSemiring_67_);
lean_dec_ref(v___x_66_);
v___x_68_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_67_);
v_toMul_69_ = lean_ctor_get(v___x_68_, 0);
v_toAdd_70_ = lean_ctor_get(v___x_68_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_81_ == 0)
{
v___x_72_ = v___x_68_;
v_isShared_73_ = v_isSharedCheck_81_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_toAdd_70_);
lean_inc(v_toMul_69_);
lean_dec(v___x_68_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_81_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
lean_inc(v_x_59_);
v___x_74_ = lean_apply_1(v_x_59_, v_v_60_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v_l_56_);
lean_ctor_set(v___x_72_, 0, v_fst_61_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_fst_61_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_l_56_);
v___x_76_ = v_reuseFailAlloc_80_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_apply_1(v_x_59_, v___x_76_);
v___x_78_ = lean_apply_2(v_toMul_69_, v_c_58_, v___x_77_);
v___x_79_ = lean_apply_2(v_toAdd_70_, v___x_74_, v___x_78_);
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___redArg___boxed(lean_object* v_inst_82_, lean_object* v_l_83_, lean_object* v_j_84_, lean_object* v_c_85_, lean_object* v_x_86_, lean_object* v_v_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___redArg(v_inst_82_, v_l_83_, v_j_84_, v_c_85_, v_x_86_, v_v_87_);
lean_dec(v_j_84_);
lean_dec_ref(v_inst_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp(lean_object* v_K_89_, lean_object* v_inst_90_, lean_object* v_r_91_, lean_object* v_n_92_, lean_object* v_l_93_, lean_object* v_j_94_, lean_object* v_c_95_, lean_object* v_x_96_, lean_object* v_v_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___redArg(v_inst_90_, v_l_93_, v_j_94_, v_c_95_, v_x_96_, v_v_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp___boxed(lean_object* v_K_99_, lean_object* v_inst_100_, lean_object* v_r_101_, lean_object* v_n_102_, lean_object* v_l_103_, lean_object* v_j_104_, lean_object* v_c_105_, lean_object* v_x_106_, lean_object* v_v_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__colOp(v_K_99_, v_inst_100_, v_r_101_, v_n_102_, v_l_103_, v_j_104_, v_c_105_, v_x_106_, v_v_107_);
lean_dec(v_j_104_);
lean_dec(v_n_102_);
lean_dec(v_r_101_);
lean_dec_ref(v_inst_100_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg(lean_object* v_inst_109_, lean_object* v_r_110_, lean_object* v_p_111_, lean_object* v_S_112_, lean_object* v_t_113_, lean_object* v_x_114_, lean_object* v_v_115_){
_start:
{
lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_fst_116_ = lean_ctor_get(v_v_115_, 0);
v_snd_117_ = lean_ctor_get(v_v_115_, 1);
v___x_118_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_118_, 0, v_r_110_);
lean_inc(v_fst_116_);
v___x_119_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_118_, v_fst_116_, v_S_112_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec(v_t_113_);
lean_dec(v_p_111_);
v___x_120_ = lean_apply_1(v_x_114_, v_v_115_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_toSemiring_123_; lean_object* v___x_124_; lean_object* v_toMul_125_; lean_object* v_toAdd_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_138_; 
lean_inc(v_snd_117_);
lean_inc(v_fst_116_);
v___x_121_ = lp_mathlib_Field_toSemifield___redArg(v_inst_109_);
v___x_122_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_121_);
v_toSemiring_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref(v_toSemiring_123_);
lean_dec_ref(v___x_122_);
v___x_124_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_123_);
v_toMul_125_ = lean_ctor_get(v___x_124_, 0);
v_toAdd_126_ = lean_ctor_get(v___x_124_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_138_ == 0)
{
v___x_128_ = v___x_124_;
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_toAdd_126_);
lean_inc(v_toMul_125_);
lean_dec(v___x_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_inc(v_x_114_);
v___x_130_ = lean_apply_1(v_x_114_, v_v_115_);
v___x_131_ = lean_apply_1(v_t_113_, v_fst_116_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_snd_117_);
lean_ctor_set(v___x_128_, 0, v_p_111_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_p_111_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_snd_117_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_apply_1(v_x_114_, v___x_133_);
v___x_135_ = lean_apply_2(v_toMul_125_, v___x_131_, v___x_134_);
v___x_136_ = lean_apply_2(v_toAdd_126_, v___x_130_, v___x_135_);
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg___boxed(lean_object* v_inst_139_, lean_object* v_r_140_, lean_object* v_p_141_, lean_object* v_S_142_, lean_object* v_t_143_, lean_object* v_x_144_, lean_object* v_v_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg(v_inst_139_, v_r_140_, v_p_141_, v_S_142_, v_t_143_, v_x_144_, v_v_145_);
lean_dec_ref(v_inst_139_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow(lean_object* v_K_147_, lean_object* v_inst_148_, lean_object* v_r_149_, lean_object* v_n_150_, lean_object* v_p_151_, lean_object* v_S_152_, lean_object* v_t_153_, lean_object* v_x_154_, lean_object* v_v_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg(v_inst_148_, v_r_149_, v_p_151_, v_S_152_, v_t_153_, v_x_154_, v_v_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___boxed(lean_object* v_K_157_, lean_object* v_inst_158_, lean_object* v_r_159_, lean_object* v_n_160_, lean_object* v_p_161_, lean_object* v_S_162_, lean_object* v_t_163_, lean_object* v_x_164_, lean_object* v_v_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow(v_K_157_, v_inst_158_, v_r_159_, v_n_160_, v_p_161_, v_S_162_, v_t_163_, v_x_164_, v_v_165_);
lean_dec(v_n_160_);
lean_dec_ref(v_inst_158_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg(lean_object* v_inst_167_, lean_object* v_n_168_, lean_object* v_q_169_, lean_object* v_S_170_, lean_object* v_c_171_, lean_object* v_x_172_, lean_object* v_v_173_){
_start:
{
lean_object* v_fst_174_; lean_object* v_snd_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_fst_174_ = lean_ctor_get(v_v_173_, 0);
v_snd_175_ = lean_ctor_get(v_v_173_, 1);
v___x_176_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_176_, 0, v_n_168_);
lean_inc(v_snd_175_);
v___x_177_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_176_, v_snd_175_, v_S_170_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v_c_171_);
lean_dec(v_q_169_);
v___x_178_ = lean_apply_1(v_x_172_, v_v_173_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_toSemiring_181_; lean_object* v___x_182_; lean_object* v_toMul_183_; lean_object* v_toAdd_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_196_; 
lean_inc(v_snd_175_);
lean_inc(v_fst_174_);
v___x_179_ = lp_mathlib_Field_toSemifield___redArg(v_inst_167_);
v___x_180_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_179_);
v_toSemiring_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_toSemiring_181_);
lean_dec_ref(v___x_180_);
v___x_182_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_181_);
v_toMul_183_ = lean_ctor_get(v___x_182_, 0);
v_toAdd_184_ = lean_ctor_get(v___x_182_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_196_ == 0)
{
v___x_186_ = v___x_182_;
v_isShared_187_ = v_isSharedCheck_196_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_toAdd_184_);
lean_inc(v_toMul_183_);
lean_dec(v___x_182_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_196_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
lean_inc(v_x_172_);
v___x_188_ = lean_apply_1(v_x_172_, v_v_173_);
v___x_189_ = lean_apply_1(v_c_171_, v_snd_175_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v_q_169_);
lean_ctor_set(v___x_186_, 0, v_fst_174_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_fst_174_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_q_169_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_apply_1(v_x_172_, v___x_191_);
v___x_193_ = lean_apply_2(v_toMul_183_, v___x_189_, v___x_192_);
v___x_194_ = lean_apply_2(v_toAdd_184_, v___x_188_, v___x_193_);
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg___boxed(lean_object* v_inst_197_, lean_object* v_n_198_, lean_object* v_q_199_, lean_object* v_S_200_, lean_object* v_c_201_, lean_object* v_x_202_, lean_object* v_v_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg(v_inst_197_, v_n_198_, v_q_199_, v_S_200_, v_c_201_, v_x_202_, v_v_203_);
lean_dec_ref(v_inst_197_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol(lean_object* v_K_205_, lean_object* v_inst_206_, lean_object* v_r_207_, lean_object* v_n_208_, lean_object* v_q_209_, lean_object* v_S_210_, lean_object* v_c_211_, lean_object* v_x_212_, lean_object* v_v_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg(v_inst_206_, v_n_208_, v_q_209_, v_S_210_, v_c_211_, v_x_212_, v_v_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___boxed(lean_object* v_K_215_, lean_object* v_inst_216_, lean_object* v_r_217_, lean_object* v_n_218_, lean_object* v_q_219_, lean_object* v_S_220_, lean_object* v_c_221_, lean_object* v_x_222_, lean_object* v_v_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol(v_K_215_, v_inst_216_, v_r_217_, v_n_218_, v_q_219_, v_S_220_, v_c_221_, v_x_222_, v_v_223_);
lean_dec(v_r_217_);
lean_dec_ref(v_inst_216_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__0(lean_object* v_q_225_, lean_object* v_x_226_, lean_object* v_p_227_, lean_object* v_toDiv_228_, lean_object* v_toNeg_229_, lean_object* v_b_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_inc(v_q_225_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_b_230_);
lean_ctor_set(v___x_231_, 1, v_q_225_);
lean_inc(v_x_226_);
v___x_232_ = lean_apply_1(v_x_226_, v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_p_227_);
lean_ctor_set(v___x_233_, 1, v_q_225_);
v___x_234_ = lean_apply_1(v_x_226_, v___x_233_);
v___x_235_ = lean_apply_2(v_toDiv_228_, v___x_232_, v___x_234_);
v___x_236_ = lean_apply_1(v_toNeg_229_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__1(lean_object* v_p_237_, lean_object* v_inst_238_, lean_object* v_r_239_, lean_object* v___x_240_, lean_object* v___f_241_, lean_object* v_x_242_, lean_object* v_q_243_, lean_object* v_toDiv_244_, lean_object* v_toNeg_245_, lean_object* v_j_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_inc_n(v_p_237_, 3);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_p_237_);
lean_ctor_set(v___x_247_, 1, v_j_246_);
lean_inc(v_x_242_);
lean_inc(v___f_241_);
lean_inc(v___x_240_);
lean_inc(v_r_239_);
v___x_248_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg(v_inst_238_, v_r_239_, v_p_237_, v___x_240_, v___f_241_, v_x_242_, v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_p_237_);
lean_ctor_set(v___x_249_, 1, v_q_243_);
v___x_250_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___redArg(v_inst_238_, v_r_239_, v_p_237_, v___x_240_, v___f_241_, v_x_242_, v___x_249_);
v___x_251_ = lean_apply_2(v_toDiv_244_, v___x_248_, v___x_250_);
v___x_252_ = lean_apply_1(v_toNeg_245_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__1___boxed(lean_object* v_p_253_, lean_object* v_inst_254_, lean_object* v_r_255_, lean_object* v___x_256_, lean_object* v___f_257_, lean_object* v_x_258_, lean_object* v_q_259_, lean_object* v_toDiv_260_, lean_object* v_toNeg_261_, lean_object* v_j_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__1(v_p_253_, v_inst_254_, v_r_255_, v___x_256_, v___f_257_, v_x_258_, v_q_259_, v_toDiv_260_, v_toNeg_261_, v_j_262_);
lean_dec_ref(v_inst_254_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg(lean_object* v_inst_264_, lean_object* v_r_265_, lean_object* v_n_266_, lean_object* v_p_267_, lean_object* v_q_268_, lean_object* v_x_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; lean_object* v_toRing_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_toNeg_275_; lean_object* v___x_276_; lean_object* v_toDiv_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v_y_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_ref_n(v_inst_264_, 3);
v___x_271_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_264_);
v_toRing_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_toRing_272_);
v___x_273_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_272_);
lean_dec_ref(v_toRing_272_);
v___x_274_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_273_);
lean_dec_ref(v___x_273_);
v_toNeg_275_ = lean_ctor_get(v___x_274_, 1);
lean_inc_n(v_toNeg_275_, 2);
lean_dec_ref(v___x_274_);
v___x_276_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_271_);
lean_dec_ref(v___x_271_);
v_toDiv_277_ = lean_ctor_get(v___x_276_, 2);
lean_inc_n(v_toDiv_277_, 2);
lean_dec_ref(v___x_276_);
lean_inc_n(v_p_267_, 3);
lean_inc_n(v_r_265_, 3);
v___x_278_ = lean_alloc_closure((void*)(l_Fin_decLt___boxed), 3, 2);
lean_closure_set(v___x_278_, 0, v_r_265_);
lean_closure_set(v___x_278_, 1, v_p_267_);
v___x_279_ = l_List_finRange(v_r_265_);
v___x_280_ = lp_mathlib_Multiset_filter___redArg(v___x_278_, v___x_279_);
lean_inc_n(v_x_269_, 2);
lean_inc_n(v_q_268_, 3);
v___f_281_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__0), 6, 5);
lean_closure_set(v___f_281_, 0, v_q_268_);
lean_closure_set(v___f_281_, 1, v_x_269_);
lean_closure_set(v___f_281_, 2, v_p_267_);
lean_closure_set(v___f_281_, 3, v_toDiv_277_);
lean_closure_set(v___f_281_, 4, v_toNeg_275_);
lean_inc_ref(v___f_281_);
lean_inc(v___x_280_);
v___f_282_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_282_, 0, v_p_267_);
lean_closure_set(v___f_282_, 1, v_inst_264_);
lean_closure_set(v___f_282_, 2, v_r_265_);
lean_closure_set(v___f_282_, 3, v___x_280_);
lean_closure_set(v___f_282_, 4, v___f_281_);
lean_closure_set(v___f_282_, 5, v_x_269_);
lean_closure_set(v___f_282_, 6, v_q_268_);
lean_closure_set(v___f_282_, 7, v_toDiv_277_);
lean_closure_set(v___f_282_, 8, v_toNeg_275_);
lean_inc_n(v_n_266_, 3);
v_y_283_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_lhwline__mrow___boxed), 9, 8);
lean_closure_set(v_y_283_, 0, lean_box(0));
lean_closure_set(v_y_283_, 1, v_inst_264_);
lean_closure_set(v_y_283_, 2, v_r_265_);
lean_closure_set(v_y_283_, 3, v_n_266_);
lean_closure_set(v_y_283_, 4, v_p_267_);
lean_closure_set(v_y_283_, 5, v___x_280_);
lean_closure_set(v_y_283_, 6, v___f_281_);
lean_closure_set(v_y_283_, 7, v_x_269_);
v___x_284_ = lean_alloc_closure((void*)(l_Fin_decLt___boxed), 3, 2);
lean_closure_set(v___x_284_, 0, v_n_266_);
lean_closure_set(v___x_284_, 1, v_q_268_);
v___x_285_ = l_List_finRange(v_n_266_);
v___x_286_ = lp_mathlib_Multiset_filter___redArg(v___x_284_, v___x_285_);
v___x_287_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__mcol___redArg(v_inst_264_, v_n_266_, v_q_268_, v___x_286_, v___f_282_, v_y_283_, v_a_270_);
lean_dec_ref(v_inst_264_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate(lean_object* v_K_288_, lean_object* v_inst_289_, lean_object* v_r_290_, lean_object* v_n_291_, lean_object* v_p_292_, lean_object* v_q_293_, lean_object* v_x_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg(v_inst_289_, v_r_290_, v_n_291_, v_p_292_, v_q_293_, v_x_294_, v_a_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__elim___redArg(lean_object* v_inst_297_, lean_object* v_r_298_, lean_object* v_n_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_zero_303_; uint8_t v_isZero_304_; 
v_zero_303_ = lean_unsigned_to_nat(0u);
v_isZero_304_ = lean_nat_dec_eq(v_x_300_, v_zero_303_);
if (v_isZero_304_ == 1)
{
lean_object* v___x_305_; 
lean_dec(v_x_300_);
lean_dec(v_n_299_);
lean_dec(v_r_298_);
lean_dec_ref(v_inst_297_);
v___x_305_ = lean_apply_1(v_x_301_, v_a_302_);
return v___x_305_;
}
else
{
lean_object* v_one_306_; lean_object* v_n_307_; uint8_t v___x_308_; 
v_one_306_ = lean_unsigned_to_nat(1u);
v_n_307_ = lean_nat_sub(v_x_300_, v_one_306_);
lean_dec(v_x_300_);
v___x_308_ = lean_nat_dec_lt(v_n_307_, v_r_298_);
if (v___x_308_ == 0)
{
v_x_300_ = v_n_307_;
goto _start;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = lean_nat_dec_lt(v_n_307_, v_n_299_);
if (v___x_310_ == 0)
{
v_x_300_ = v_n_307_;
goto _start;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc_n(v_n_307_, 2);
lean_inc(v_n_299_);
lean_inc(v_r_298_);
lean_inc_ref(v_inst_297_);
v___x_312_ = lean_alloc_closure((void*)(lp_tree_Formalism_GradedWeylDivisibility_lhwline__elim___redArg), 6, 5);
lean_closure_set(v___x_312_, 0, v_inst_297_);
lean_closure_set(v___x_312_, 1, v_r_298_);
lean_closure_set(v___x_312_, 2, v_n_299_);
lean_closure_set(v___x_312_, 3, v_n_307_);
lean_closure_set(v___x_312_, 4, v_x_301_);
v___x_313_ = lp_tree_Formalism_GradedWeylDivisibility_highestWeightLineUpdate___redArg(v_inst_297_, v_r_298_, v_n_299_, v_n_307_, v_n_307_, v___x_312_, v_a_302_);
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_lhwline__elim(lean_object* v_K_314_, lean_object* v_inst_315_, lean_object* v_r_316_, lean_object* v_n_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lp_tree_Formalism_GradedWeylDivisibility_lhwline__elim___redArg(v_inst_315_, v_r_316_, v_n_317_, v_x_318_, v_x_319_, v_a_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___redArg(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_){
_start:
{
lean_object* v_zero_326_; uint8_t v_isZero_327_; 
v_zero_326_ = lean_unsigned_to_nat(0u);
v_isZero_327_ = lean_nat_dec_eq(v_x_322_, v_zero_326_);
if (v_isZero_327_ == 1)
{
lean_object* v___x_328_; 
lean_dec(v_h__2_325_);
v___x_328_ = lean_apply_1(v_h__1_324_, v_x_323_);
return v___x_328_;
}
else
{
lean_object* v_one_329_; lean_object* v_n_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_324_);
v_one_329_ = lean_unsigned_to_nat(1u);
v_n_330_ = lean_nat_sub(v_x_322_, v_one_329_);
v___x_331_ = lean_apply_2(v_h__2_325_, v_n_330_, v_x_323_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___redArg___boxed(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___redArg(v_x_332_, v_x_333_, v_h__1_334_, v_h__2_335_);
lean_dec(v_x_332_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter(lean_object* v_K_337_, lean_object* v_r_338_, lean_object* v_n_339_, lean_object* v_motive_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_h__1_343_, lean_object* v_h__2_344_){
_start:
{
lean_object* v_zero_345_; uint8_t v_isZero_346_; 
v_zero_345_ = lean_unsigned_to_nat(0u);
v_isZero_346_ = lean_nat_dec_eq(v_x_341_, v_zero_345_);
if (v_isZero_346_ == 1)
{
lean_object* v___x_347_; 
lean_dec(v_h__2_344_);
v___x_347_ = lean_apply_1(v_h__1_343_, v_x_342_);
return v___x_347_;
}
else
{
lean_object* v_one_348_; lean_object* v_n_349_; lean_object* v___x_350_; 
lean_dec(v_h__1_343_);
v_one_348_ = lean_unsigned_to_nat(1u);
v_n_349_ = lean_nat_sub(v_x_341_, v_one_348_);
v___x_350_ = lean_apply_2(v_h__2_344_, v_n_349_, v_x_342_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter___boxed(lean_object* v_K_351_, lean_object* v_r_352_, lean_object* v_n_353_, lean_object* v_motive_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = lp_tree___private_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas_0__Formalism_GradedWeylDivisibility_lhwline__elim_match__1_splitter(v_K_351_, v_r_352_, v_n_353_, v_motive_354_, v_x_355_, v_x_356_, v_h__1_357_, v_h__2_358_);
lean_dec(v_x_355_);
lean_dec(v_n_353_);
lean_dec(v_r_352_);
return v_res_359_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementB(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_DualWeylDominanceOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
