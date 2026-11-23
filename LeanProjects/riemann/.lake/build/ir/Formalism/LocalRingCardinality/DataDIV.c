// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataDIV
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.DegreeFormula.FlagDegFormula
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
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_cc(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_Gk___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_Gk___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_Gk(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_ck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_ck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_toGG___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_toGG___closed__0;
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_toGG___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_toGG___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_toGG(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_BasicNotions_DV_kapW___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_BasicNotions_DV_kapW___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_kapW(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_Gk___lam__0(lean_object* v_toNPow_1_, lean_object* v_y_2_, lean_object* v_k_3_, lean_object* v_y_x27_4_, lean_object* v_toMul_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc(v_toNPow_1_);
lean_inc(v_a_6_);
v___x_7_ = lean_apply_2(v_toNPow_1_, v_a_6_, v_y_2_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_sub(v_k_3_, v___x_8_);
v___x_10_ = lean_nat_sub(v___x_9_, v_a_6_);
lean_dec(v_a_6_);
lean_dec(v___x_9_);
v___x_11_ = lean_apply_2(v_toNPow_1_, v___x_10_, v_y_x27_4_);
v___x_12_ = lean_apply_2(v_toMul_5_, v___x_7_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_Gk___lam__0___boxed(lean_object* v_toNPow_13_, lean_object* v_y_14_, lean_object* v_k_15_, lean_object* v_y_x27_16_, lean_object* v_toMul_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_tree_Formalism_BasicNotions_DV_Gk___lam__0(v_toNPow_13_, v_y_14_, v_k_15_, v_y_x27_16_, v_toMul_17_, v_a_18_);
lean_dec(v_k_15_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0___lam__0(lean_object* v_toAdd_20_, lean_object* v_x1_21_, lean_object* v_x2_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_2(v_toAdd_20_, v_x1_21_, v_x2_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0(lean_object* v_Z_24_, lean_object* v_s_25_){
_start:
{
lean_object* v_ring_26_; lean_object* v_toSemiring_27_; lean_object* v_toAddCommMonoid_28_; lean_object* v___x_29_; lean_object* v_toZero_30_; lean_object* v_toAdd_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v_ring_26_ = lean_ctor_get(v_Z_24_, 0);
v_toSemiring_27_ = lean_ctor_get(v_ring_26_, 0);
v_toAddCommMonoid_28_ = lean_ctor_get(v_toSemiring_27_, 0);
v___x_29_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_28_);
v_toZero_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_toZero_30_);
v_toAdd_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_toAdd_31_);
lean_dec_ref(v___x_29_);
v___f_32_ = lean_alloc_closure((void*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_32_, 0, v_toAdd_31_);
v___x_33_ = l_List_foldrTR___redArg(v___f_32_, v_toZero_30_, v_s_25_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0___boxed(lean_object* v_Z_34_, lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0(v_Z_34_, v_s_35_);
lean_dec_ref(v_Z_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg(lean_object* v_Z_37_, lean_object* v_s_38_, lean_object* v_f_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lp_mathlib_Multiset_map___redArg(v_f_39_, v_s_38_);
v___x_41_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0_spec__0(v_Z_37_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg___boxed(lean_object* v_Z_42_, lean_object* v_s_43_, lean_object* v_f_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg(v_Z_42_, v_s_43_, v_f_44_);
lean_dec_ref(v_Z_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_Gk(lean_object* v_Z_46_, lean_object* v_k_47_, lean_object* v_y_48_, lean_object* v_y_x27_49_){
_start:
{
lean_object* v_ring_50_; lean_object* v_toSemiring_51_; lean_object* v___x_52_; lean_object* v_toMonoid_53_; lean_object* v_toMul_54_; lean_object* v_toNPow_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___x_58_; 
v_ring_50_ = lean_ctor_get(v_Z_46_, 0);
v_toSemiring_51_ = lean_ctor_get(v_ring_50_, 0);
lean_inc_ref(v_toSemiring_51_);
v___x_52_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_51_);
v_toMonoid_53_ = lean_ctor_get(v_toSemiring_51_, 1);
v_toMul_54_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_toMul_54_);
lean_dec_ref(v___x_52_);
v_toNPow_55_ = lean_ctor_get(v_toMonoid_53_, 2);
lean_inc(v_k_47_);
v___x_56_ = l_List_range(v_k_47_);
lean_inc(v_toNPow_55_);
v___f_57_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_DV_Gk___lam__0___boxed), 6, 5);
lean_closure_set(v___f_57_, 0, v_toNPow_55_);
lean_closure_set(v___f_57_, 1, v_y_48_);
lean_closure_set(v___f_57_, 2, v_k_47_);
lean_closure_set(v___f_57_, 3, v_y_x27_49_);
lean_closure_set(v___f_57_, 4, v_toMul_54_);
v___x_58_ = lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg(v_Z_46_, v___x_56_, v___f_57_);
lean_dec_ref(v_Z_46_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0(lean_object* v_Z_59_, lean_object* v_00_u03b9_60_, lean_object* v_s_61_, lean_object* v_f_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___redArg(v_Z_59_, v_s_61_, v_f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0___boxed(lean_object* v_Z_64_, lean_object* v_00_u03b9_65_, lean_object* v_s_66_, lean_object* v_f_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Finset_sum___at___00Formalism_BasicNotions_DV_Gk_spec__0(v_Z_64_, v_00_u03b9_65_, v_s_66_, v_f_67_);
lean_dec_ref(v_Z_64_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_ck___lam__0(lean_object* v_P_69_, lean_object* v_c1_70_, lean_object* v_Z_71_, lean_object* v_k_72_, lean_object* v_toMul_73_, lean_object* v_Q_74_, lean_object* v_capDeg_75_, lean_object* v_i_76_){
_start:
{
lean_object* v_x_77_; lean_object* v_x_x27_78_; lean_object* v_Dv_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_x_77_ = lean_ctor_get(v_P_69_, 0);
lean_inc(v_x_77_);
v_x_x27_78_ = lean_ctor_get(v_P_69_, 1);
lean_inc(v_x_x27_78_);
v_Dv_79_ = lean_ctor_get(v_P_69_, 2);
lean_inc(v_Dv_79_);
lean_dec_ref(v_P_69_);
lean_inc_n(v_i_76_, 2);
v___x_80_ = lean_apply_1(v_Dv_79_, v_i_76_);
v___x_81_ = lean_apply_1(v_x_77_, v_i_76_);
lean_inc(v_c1_70_);
v___x_82_ = lean_apply_1(v_c1_70_, v___x_81_);
v___x_83_ = lean_apply_1(v_x_x27_78_, v_i_76_);
v___x_84_ = lean_apply_1(v_c1_70_, v___x_83_);
v___x_85_ = lp_tree_Formalism_BasicNotions_DV_Gk(v_Z_71_, v_k_72_, v___x_82_, v___x_84_);
v___x_86_ = lean_apply_2(v_toMul_73_, v___x_85_, v_Q_74_);
v___x_87_ = lean_apply_2(v_capDeg_75_, v___x_80_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_ck(lean_object* v_Z_88_, lean_object* v_r_89_, lean_object* v_P_90_, lean_object* v_k_91_, lean_object* v_Q_92_){
_start:
{
lean_object* v_ring_93_; lean_object* v_c1_94_; lean_object* v_capDeg_95_; lean_object* v_toSemiring_96_; lean_object* v___x_97_; lean_object* v_toMul_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
v_ring_93_ = lean_ctor_get(v_Z_88_, 0);
v_c1_94_ = lean_ctor_get(v_Z_88_, 2);
lean_inc(v_c1_94_);
v_capDeg_95_ = lean_ctor_get(v_Z_88_, 6);
lean_inc_ref(v_capDeg_95_);
v_toSemiring_96_ = lean_ctor_get(v_ring_93_, 0);
lean_inc_ref(v_toSemiring_96_);
v___x_97_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_96_);
v_toMul_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_toMul_98_);
lean_dec_ref(v___x_97_);
v___x_99_ = l_List_finRange(v_r_89_);
v___f_100_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_DV_ck___lam__0), 8, 7);
lean_closure_set(v___f_100_, 0, v_P_90_);
lean_closure_set(v___f_100_, 1, v_c1_94_);
lean_closure_set(v___f_100_, 2, v_Z_88_);
lean_closure_set(v___f_100_, 3, v_k_91_);
lean_closure_set(v___f_100_, 4, v_toMul_98_);
lean_closure_set(v___f_100_, 5, v_Q_92_);
lean_closure_set(v___f_100_, 6, v_capDeg_95_);
v___x_101_ = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(v___x_99_, v___f_100_);
return v___x_101_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_toGG___closed__0(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_102_;
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_toGG___closed__1(void){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_toGG(lean_object* v_D_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_eTau_106_; lean_object* v_val_107_; lean_object* v_toFun_108_; lean_object* v___x_109_; 
v_eTau_106_ = lean_ctor_get(v_D_104_, 5);
lean_inc_ref(v_eTau_106_);
lean_dec_ref(v_D_104_);
v_val_107_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_x_105_, 1);
v_toFun_108_ = lean_ctor_get(v_eTau_106_, 0);
lean_inc(v_toFun_108_);
lean_dec_ref(v_eTau_106_);
v___x_109_ = lean_apply_1(v_toFun_108_, v_val_107_);
return v___x_109_;
}
else
{
lean_object* v_R_110_; lean_object* v_toFrame_111_; lean_object* v_grp_112_; lean_object* v_toAddMonoid_113_; lean_object* v_eTau_114_; lean_object* v_val_115_; lean_object* v_toAddSemigroup_116_; lean_object* v_toFun_117_; lean_object* v___x_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_121_; lean_object* v_fst_122_; lean_object* v_fst_123_; lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_176_; 
v_R_110_ = lean_ctor_get(v_D_104_, 0);
v_toFrame_111_ = lean_ctor_get(v_R_110_, 0);
lean_inc_ref(v_toFrame_111_);
v_grp_112_ = lean_ctor_get(v_toFrame_111_, 2);
v_toAddMonoid_113_ = lean_ctor_get(v_grp_112_, 0);
v_eTau_114_ = lean_ctor_get(v_D_104_, 5);
lean_inc_ref(v_eTau_114_);
lean_dec_ref(v_D_104_);
v_val_115_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v_x_105_, 1);
v_toAddSemigroup_116_ = lean_ctor_get(v_toAddMonoid_113_, 0);
lean_inc(v_toAddSemigroup_116_);
v_toFun_117_ = lean_ctor_get(v_eTau_114_, 0);
lean_inc(v_toFun_117_);
lean_dec_ref(v_eTau_114_);
v___x_118_ = lean_apply_1(v_toFun_117_, v_val_115_);
v_fst_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_fst_119_);
v_snd_120_ = lean_ctor_get(v___x_118_, 1);
lean_inc(v_snd_120_);
lean_dec_ref(v___x_118_);
v___x_121_ = lp_tree_Formalism_HC_Frame_cc(v_toFrame_111_);
lean_dec_ref(v_toFrame_111_);
v_fst_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_fst_122_);
v_fst_123_ = lean_ctor_get(v_fst_119_, 0);
lean_inc(v_fst_123_);
v_fst_124_ = lean_ctor_get(v_fst_122_, 0);
lean_inc(v_fst_124_);
v_snd_125_ = lean_ctor_get(v_fst_119_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_fst_119_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_fst_119_, 0);
lean_dec(v_unused_177_);
v___x_127_ = v_fst_119_;
v_isShared_128_ = v_isSharedCheck_176_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snd_125_);
lean_dec(v_fst_119_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_176_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_snd_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_174_; 
v_snd_129_ = lean_ctor_get(v_fst_122_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_fst_122_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v_fst_122_, 0);
lean_dec(v_unused_175_);
v___x_131_ = v_fst_122_;
v_isShared_132_ = v_isSharedCheck_174_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snd_129_);
lean_dec(v_fst_122_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_174_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_snd_133_; lean_object* v_val_134_; lean_object* v_inv_135_; lean_object* v_val_136_; lean_object* v_inv_137_; lean_object* v_val_138_; lean_object* v_inv_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_173_; 
v_snd_133_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_snd_133_);
lean_dec_ref(v___x_121_);
v_val_134_ = lean_ctor_get(v_fst_123_, 0);
lean_inc(v_val_134_);
v_inv_135_ = lean_ctor_get(v_fst_123_, 1);
lean_inc(v_inv_135_);
lean_dec(v_fst_123_);
v_val_136_ = lean_ctor_get(v_fst_124_, 0);
lean_inc(v_val_136_);
v_inv_137_ = lean_ctor_get(v_fst_124_, 1);
lean_inc(v_inv_137_);
lean_dec(v_fst_124_);
v_val_138_ = lean_ctor_get(v_snd_125_, 0);
v_inv_139_ = lean_ctor_get(v_snd_125_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_snd_125_);
if (v_isSharedCheck_173_ == 0)
{
v___x_141_ = v_snd_125_;
v_isShared_142_ = v_isSharedCheck_173_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_inv_139_);
lean_inc(v_val_138_);
lean_dec(v_snd_125_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_173_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_val_143_; lean_object* v_inv_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_172_; 
v_val_143_ = lean_ctor_get(v_snd_129_, 0);
v_inv_144_ = lean_ctor_get(v_snd_129_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_snd_129_);
if (v_isSharedCheck_172_ == 0)
{
v___x_146_ = v_snd_129_;
v_isShared_147_ = v_isSharedCheck_172_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_inv_144_);
lean_inc(v_val_143_);
lean_dec(v_snd_129_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_172_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v_toFun_149_; lean_object* v___x_150_; lean_object* v_toFun_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_148_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_toGG___closed__0, &lp_tree_Formalism_BasicNotions_DV_toGG___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_toGG___closed__0);
v_toFun_149_ = lean_ctor_get(v___x_148_, 0);
v___x_150_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_toGG___closed__1, &lp_tree_Formalism_BasicNotions_DV_toGG___closed__1_once, _init_lp_tree_Formalism_BasicNotions_DV_toGG___closed__1);
v_toFun_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_toFun_149_);
v___x_152_ = lean_apply_1(v_toFun_149_, v_snd_120_);
v___x_153_ = lean_int_mul(v_val_134_, v_val_136_);
lean_dec(v_val_136_);
lean_dec(v_val_134_);
v___x_154_ = lean_int_mul(v_inv_137_, v_inv_135_);
lean_dec(v_inv_135_);
lean_dec(v_inv_137_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_154_);
lean_ctor_set(v___x_146_, 0, v___x_153_);
v___x_156_ = v___x_146_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_154_);
v___x_156_ = v_reuseFailAlloc_171_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_157_ = lean_int_mul(v_val_138_, v_val_143_);
lean_dec(v_val_143_);
lean_dec(v_val_138_);
v___x_158_ = lean_int_mul(v_inv_144_, v_inv_139_);
lean_dec(v_inv_139_);
lean_dec(v_inv_144_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_158_);
lean_ctor_set(v___x_141_, 0, v___x_157_);
v___x_160_ = v___x_141_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_170_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_160_);
lean_ctor_set(v___x_131_, 0, v___x_156_);
v___x_162_ = v___x_131_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_169_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_toFun_149_);
v___x_163_ = lean_apply_1(v_toFun_149_, v_snd_133_);
v___x_164_ = lean_apply_2(v_toAddSemigroup_116_, v___x_152_, v___x_163_);
lean_inc(v_toFun_151_);
v___x_165_ = lean_apply_1(v_toFun_151_, v___x_164_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_165_);
lean_ctor_set(v___x_127_, 0, v___x_162_);
v___x_167_ = v___x_127_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_lp_tree_Formalism_BasicNotions_DV_kapW___closed__0(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_nat_to_int(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_DV_kapW(lean_object* v_D_180_, lean_object* v_j_181_, lean_object* v_00_u03c4_182_, lean_object* v_i_183_){
_start:
{
lean_object* v_R_184_; lean_object* v_what_u2082_185_; lean_object* v___x_186_; lean_object* v_fst_187_; lean_object* v_snd_188_; uint8_t v___x_189_; 
v_R_184_ = lean_ctor_get(v_D_180_, 0);
lean_inc_ref(v_R_184_);
v_what_u2082_185_ = lean_ctor_get(v_D_180_, 4);
lean_inc_ref(v_what_u2082_185_);
lean_dec_ref(v_D_180_);
v___x_186_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_184_, v_j_181_);
v_fst_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_fst_187_);
v_snd_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc(v_snd_188_);
lean_dec_ref(v___x_186_);
v___x_189_ = lean_nat_dec_lt(v_i_183_, v_fst_187_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_nat_sub(v_i_183_, v_fst_187_);
lean_dec(v_fst_187_);
lean_dec(v_i_183_);
v___x_191_ = lean_nat_dec_lt(v___x_190_, v_snd_188_);
lean_dec(v_snd_188_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
lean_dec(v___x_190_);
lean_dec_ref(v_what_u2082_185_);
lean_dec_ref(v_R_184_);
lean_dec(v_00_u03c4_182_);
lean_dec(v_j_181_);
v___x_192_ = lean_obj_once(&lp_tree_Formalism_BasicNotions_DV_kapW___closed__0, &lp_tree_Formalism_BasicNotions_DV_kapW___closed__0_once, _init_lp_tree_Formalism_BasicNotions_DV_kapW___closed__0);
return v___x_192_;
}
else
{
lean_object* v_kaSmall_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_kaSmall_193_ = lean_ctor_get(v_what_u2082_185_, 45);
lean_inc_ref(v_kaSmall_193_);
lean_dec_ref(v_what_u2082_185_);
v___x_194_ = lean_apply_3(v_kaSmall_193_, v_j_181_, v_00_u03c4_182_, v___x_190_);
v___x_195_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_184_);
lean_dec_ref(v_R_184_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_shiftr(v___x_195_, v___x_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_nat_to_int(v___x_197_);
v___x_199_ = lean_int_sub(v___x_194_, v___x_198_);
lean_dec(v___x_198_);
lean_dec(v___x_194_);
return v___x_199_;
}
}
else
{
lean_object* v_kaBig_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_snd_188_);
lean_dec(v_fst_187_);
v_kaBig_200_ = lean_ctor_get(v_what_u2082_185_, 44);
lean_inc_ref(v_kaBig_200_);
lean_dec_ref(v_what_u2082_185_);
v___x_201_ = lean_apply_3(v_kaBig_200_, v_j_181_, v_00_u03c4_182_, v_i_183_);
v___x_202_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_184_);
lean_dec_ref(v_R_184_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_shiftr(v___x_202_, v___x_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_nat_to_int(v___x_204_);
v___x_206_ = lean_int_add(v___x_201_, v___x_205_);
lean_dec(v___x_205_);
lean_dec(v___x_201_);
return v___x_206_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_DegreeFormula_FlagDegFormula(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_DegreeFormula_FlagDegFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
