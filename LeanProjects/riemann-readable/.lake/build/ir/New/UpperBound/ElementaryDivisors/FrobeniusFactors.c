// Lean compiler output
// Module: New.UpperBound.ElementaryDivisors.FrobeniusFactors
// Imports: public import Init public meta import Init public import New.UpperBound.ElementaryDivisors.RootLemma
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
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_adjugate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_one___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_instMulOfFintypeOfAddCommMonoid___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_parityCofactor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_parityCofactor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_parityCofactor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_rootVector___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_rootVector___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_rootVector___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_rootVector___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_rootVector___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rootVector___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rootVector(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_rootVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_parityCofactor___redArg(lean_object* v_k_1_, lean_object* v_inst_2_, lean_object* v_T_3_, lean_object* v_s_4_, lean_object* v_M_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_isEven_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_isEven_8_ = lean_ctor_get(v_T_3_, 3);
lean_inc_ref(v_isEven_8_);
lean_dec_ref(v_T_3_);
v___x_9_ = lean_apply_1(v_isEven_8_, v_s_4_);
v___x_10_ = lean_unbox(v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
lean_inc(v_k_1_);
v___x_11_ = l_List_finRange(v_k_1_);
v___x_12_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_12_, 0, v_k_1_);
v___x_13_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_adjugate), 8, 6);
lean_closure_set(v___x_13_, 0, lean_box(0));
lean_closure_set(v___x_13_, 1, lean_box(0));
lean_closure_set(v___x_13_, 2, v___x_12_);
lean_closure_set(v___x_13_, 3, v___x_11_);
lean_closure_set(v___x_13_, 4, v_inst_2_);
lean_closure_set(v___x_13_, 5, v_M_5_);
v___x_14_ = lp_mathlib_Matrix_transpose___redArg(v___x_13_, v_a_6_, v_a_7_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; 
lean_dec_ref(v_inst_2_);
lean_dec(v_k_1_);
v___x_15_ = lean_apply_2(v_M_5_, v_a_6_, v_a_7_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_parityCofactor(lean_object* v_N_16_, lean_object* v_k_17_, lean_object* v_W_18_, lean_object* v_O_19_, lean_object* v_R_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_T_25_, lean_object* v_s_26_, lean_object* v_M_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_GRH_New_FrobeniusCycle_parityCofactor___redArg(v_k_17_, v_inst_24_, v_T_25_, v_s_26_, v_M_27_, v_a_28_, v_a_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_parityCofactor___boxed(lean_object* v_N_31_, lean_object* v_k_32_, lean_object* v_W_33_, lean_object* v_O_34_, lean_object* v_R_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_T_40_, lean_object* v_s_41_, lean_object* v_M_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_GRH_New_FrobeniusCycle_parityCofactor(v_N_31_, v_k_32_, v_W_33_, v_O_34_, v_R_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_T_40_, v_s_41_, v_M_42_, v_a_43_, v_a_44_);
lean_dec_ref(v_inst_38_);
lean_dec_ref(v_inst_36_);
lean_dec(v_N_31_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___lam__0(lean_object* v_k_46_, lean_object* v_toZero_47_, lean_object* v_toOne_48_, lean_object* v_00_u03c8_49_, lean_object* v_s_50_, lean_object* v_T_51_, lean_object* v_r_52_, lean_object* v_00_u2113_53_, lean_object* v___f_54_, lean_object* v_inst_55_, lean_object* v_b_56_, lean_object* v_c_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc(v_k_46_);
v___x_58_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_58_, 0, v_k_46_);
v___x_59_ = lp_mathlib_Matrix_one___redArg(v___x_58_, v_toZero_47_, v_toOne_48_);
lean_inc_n(v_s_50_, 2);
v___x_60_ = lean_apply_1(v_00_u03c8_49_, v_s_50_);
lean_inc(v_b_56_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_b_56_);
lean_ctor_set(v___x_61_, 1, v_s_50_);
lean_inc_ref(v_T_51_);
v___x_62_ = lp_GRH_New_FrobeniusCycle_deepIndicator___redArg(v_T_51_, v_r_52_, v___x_61_);
v___x_63_ = lean_nat_add(v_00_u2113_53_, v___x_62_);
lean_dec(v___x_62_);
v___x_64_ = l_List_range(v___x_63_);
v___x_65_ = lean_box(0);
v___x_66_ = l_List_mapTR_loop___redArg(v___x_60_, v___x_64_, v___x_65_);
v___x_67_ = l_List_reverse___redArg(v___x_66_);
v___x_68_ = l_List_prod___redArg(v___f_54_, v___x_59_, v___x_67_);
lean_dec(v___x_59_);
v___x_69_ = lp_GRH_New_FrobeniusCycle_parityCofactor___redArg(v_k_46_, v_inst_55_, v_T_51_, v_s_50_, v___x_68_, v_b_56_, v_c_57_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___lam__0___boxed(lean_object* v_k_70_, lean_object* v_toZero_71_, lean_object* v_toOne_72_, lean_object* v_00_u03c8_73_, lean_object* v_s_74_, lean_object* v_T_75_, lean_object* v_r_76_, lean_object* v_00_u2113_77_, lean_object* v___f_78_, lean_object* v_inst_79_, lean_object* v_b_80_, lean_object* v_c_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___lam__0(v_k_70_, v_toZero_71_, v_toOne_72_, v_00_u03c8_73_, v_s_74_, v_T_75_, v_r_76_, v_00_u2113_77_, v___f_78_, v_inst_79_, v_b_80_, v_c_81_);
lean_dec(v_00_u2113_77_);
lean_dec(v_r_76_);
return v_res_82_;
}
}
static lean_object* _init_lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_mathlib_Equiv_refl___redArg();
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg(lean_object* v_k_84_, lean_object* v_inst_85_, lean_object* v_T_86_, lean_object* v_r_87_, lean_object* v_00_u2113_88_, lean_object* v_00_u03c8_89_, lean_object* v_s_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_toSemiring_93_; lean_object* v___x_94_; lean_object* v_toMul_95_; lean_object* v_toAddCommMonoid_96_; lean_object* v___x_97_; lean_object* v_toZero_98_; lean_object* v___x_99_; lean_object* v_toAddMonoidWithOne_100_; lean_object* v_toOne_101_; lean_object* v___x_102_; lean_object* v_toFun_103_; lean_object* v___x_104_; lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v_toSemiring_93_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref_n(v_toSemiring_93_, 2);
v___x_94_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_93_);
v_toMul_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_toMul_95_);
lean_dec_ref(v___x_94_);
v_toAddCommMonoid_96_ = lean_ctor_get(v_toSemiring_93_, 0);
v___x_97_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_93_);
v_toZero_98_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_toZero_98_);
lean_dec_ref(v___x_97_);
lean_inc_ref(v_inst_85_);
v___x_99_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_85_);
v_toAddMonoidWithOne_100_ = lean_ctor_get(v___x_99_, 1);
lean_inc_ref(v_toAddMonoidWithOne_100_);
lean_dec_ref(v___x_99_);
v_toOne_101_ = lean_ctor_get(v_toAddMonoidWithOne_100_, 2);
lean_inc(v_toOne_101_);
lean_dec_ref(v_toAddMonoidWithOne_100_);
v___x_102_ = lean_obj_once(&lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___closed__0, &lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___closed__0_once, _init_lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___closed__0);
v_toFun_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_k_84_);
v___x_104_ = l_List_finRange(v_k_84_);
lean_inc_ref(v_toAddCommMonoid_96_);
v___f_105_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_instMulOfFintypeOfAddCommMonoid___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_105_, 0, v___x_104_);
lean_closure_set(v___f_105_, 1, v_toMul_95_);
lean_closure_set(v___f_105_, 2, v_toAddCommMonoid_96_);
v___f_106_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg___lam__0___boxed), 12, 10);
lean_closure_set(v___f_106_, 0, v_k_84_);
lean_closure_set(v___f_106_, 1, v_toZero_98_);
lean_closure_set(v___f_106_, 2, v_toOne_101_);
lean_closure_set(v___f_106_, 3, v_00_u03c8_89_);
lean_closure_set(v___f_106_, 4, v_s_90_);
lean_closure_set(v___f_106_, 5, v_T_86_);
lean_closure_set(v___f_106_, 6, v_r_87_);
lean_closure_set(v___f_106_, 7, v_00_u2113_88_);
lean_closure_set(v___f_106_, 8, v___f_105_);
lean_closure_set(v___f_106_, 9, v_inst_85_);
lean_inc(v_toFun_103_);
v___x_107_ = lean_apply_3(v_toFun_103_, v___f_106_, v_a_91_, v_a_92_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix(lean_object* v_N_108_, lean_object* v_k_109_, lean_object* v_W_110_, lean_object* v_O_111_, lean_object* v_R_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_T_117_, lean_object* v_r_118_, lean_object* v_00_u2113_119_, lean_object* v_00_u03c8_120_, lean_object* v_s_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___redArg(v_k_109_, v_inst_116_, v_T_117_, v_r_118_, v_00_u2113_119_, v_00_u03c8_120_, v_s_121_, v_a_122_, v_a_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix___boxed(lean_object* v_N_125_, lean_object* v_k_126_, lean_object* v_W_127_, lean_object* v_O_128_, lean_object* v_R_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_T_134_, lean_object* v_r_135_, lean_object* v_00_u2113_136_, lean_object* v_00_u03c8_137_, lean_object* v_s_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_GRH_New_FrobeniusCycle_substitutionLetterMatrix(v_N_125_, v_k_126_, v_W_127_, v_O_128_, v_R_129_, v_inst_130_, v_inst_131_, v_inst_132_, v_inst_133_, v_T_134_, v_r_135_, v_00_u2113_136_, v_00_u03c8_137_, v_s_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_inst_132_);
lean_dec_ref(v_inst_130_);
lean_dec(v_N_125_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__0(lean_object* v_embedding_142_, lean_object* v_s_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_apply_2(v_embedding_142_, v_s_143_, v___y_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__1(lean_object* v_val_146_, lean_object* v___f_147_, lean_object* v___y_148_, lean_object* v_j_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lp_mathlib_Matrix_map___redArg(v_val_146_, v___f_147_, v___y_148_, v_j_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__2(lean_object* v_M_151_, lean_object* v_j_152_, lean_object* v_j_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_apply_2(v_M_151_, v_j_153_, v_j_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__3(lean_object* v_M_155_, lean_object* v___x_156_, lean_object* v_toMul_157_, lean_object* v_toAddCommMonoid_158_, lean_object* v___f_159_, lean_object* v_j_160_){
_start:
{
lean_object* v___f_161_; lean_object* v___x_162_; 
v___f_161_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__2), 3, 2);
lean_closure_set(v___f_161_, 0, v_M_155_);
lean_closure_set(v___f_161_, 1, v_j_160_);
v___x_162_ = lp_mathlib_dotProduct___redArg(v___x_156_, v_toMul_157_, v_toAddCommMonoid_158_, v___f_159_, v___f_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__3___boxed(lean_object* v_M_163_, lean_object* v___x_164_, lean_object* v_toMul_165_, lean_object* v_toAddCommMonoid_166_, lean_object* v___f_167_, lean_object* v_j_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__3(v_M_163_, v___x_164_, v_toMul_165_, v_toAddCommMonoid_166_, v___f_167_, v_j_168_);
lean_dec_ref(v_toAddCommMonoid_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__4(lean_object* v_inv_170_, lean_object* v___f_171_, lean_object* v___y_172_, lean_object* v_j_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lp_mathlib_Matrix_map___redArg(v_inv_170_, v___f_171_, v_j_173_, v___y_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__5(lean_object* v_h_175_, lean_object* v_T_176_, lean_object* v_s_177_, lean_object* v___x_178_, lean_object* v_toMul_179_, lean_object* v_toAddCommMonoid_180_, lean_object* v_M_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_val_184_; lean_object* v_inv_185_; lean_object* v_embedding_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; 
v_val_184_ = lean_ctor_get(v_h_175_, 0);
lean_inc(v_val_184_);
v_inv_185_ = lean_ctor_get(v_h_175_, 1);
lean_inc(v_inv_185_);
lean_dec_ref(v_h_175_);
v_embedding_186_ = lean_ctor_get(v_T_176_, 2);
lean_inc(v_embedding_186_);
lean_dec_ref(v_T_176_);
v___f_187_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__0), 3, 2);
lean_closure_set(v___f_187_, 0, v_embedding_186_);
lean_closure_set(v___f_187_, 1, v_s_177_);
lean_inc_ref(v___f_187_);
v___f_188_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__1), 4, 3);
lean_closure_set(v___f_188_, 0, v_val_184_);
lean_closure_set(v___f_188_, 1, v___f_187_);
lean_closure_set(v___f_188_, 2, v___y_182_);
lean_inc_ref(v_toAddCommMonoid_180_);
lean_inc(v_toMul_179_);
lean_inc(v___x_178_);
v___f_189_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_189_, 0, v_M_181_);
lean_closure_set(v___f_189_, 1, v___x_178_);
lean_closure_set(v___f_189_, 2, v_toMul_179_);
lean_closure_set(v___f_189_, 3, v_toAddCommMonoid_180_);
lean_closure_set(v___f_189_, 4, v___f_188_);
v___f_190_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__4), 4, 3);
lean_closure_set(v___f_190_, 0, v_inv_185_);
lean_closure_set(v___f_190_, 1, v___f_187_);
lean_closure_set(v___f_190_, 2, v___y_183_);
v___x_191_ = lp_mathlib_dotProduct___redArg(v___x_178_, v_toMul_179_, v_toAddCommMonoid_180_, v___f_189_, v___f_190_);
lean_dec_ref(v_toAddCommMonoid_180_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___redArg(lean_object* v_k_192_, lean_object* v_inst_193_, lean_object* v_T_194_, lean_object* v_h_195_, lean_object* v_s_196_){
_start:
{
lean_object* v_toSemiring_197_; lean_object* v_toAddCommMonoid_198_; lean_object* v___x_199_; lean_object* v_toMul_200_; lean_object* v___x_201_; lean_object* v___f_202_; 
v_toSemiring_197_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toSemiring_197_);
lean_dec_ref(v_inst_193_);
v_toAddCommMonoid_198_ = lean_ctor_get(v_toSemiring_197_, 0);
lean_inc_ref(v_toAddCommMonoid_198_);
v___x_199_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_197_);
v_toMul_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_toMul_200_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_List_finRange(v_k_192_);
v___f_202_ = lean_alloc_closure((void*)(lp_GRH_New_FrobeniusCycle_letterConj___redArg___lam__5), 9, 6);
lean_closure_set(v___f_202_, 0, v_h_195_);
lean_closure_set(v___f_202_, 1, v_T_194_);
lean_closure_set(v___f_202_, 2, v_s_196_);
lean_closure_set(v___f_202_, 3, v___x_201_);
lean_closure_set(v___f_202_, 4, v_toMul_200_);
lean_closure_set(v___f_202_, 5, v_toAddCommMonoid_198_);
return v___f_202_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj(lean_object* v_N_203_, lean_object* v_k_204_, lean_object* v_W_205_, lean_object* v_O_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_T_210_, lean_object* v_h_211_, lean_object* v_s_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lp_GRH_New_FrobeniusCycle_letterConj___redArg(v_k_204_, v_inst_209_, v_T_210_, v_h_211_, v_s_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FrobeniusCycle_letterConj___boxed(lean_object* v_N_214_, lean_object* v_k_215_, lean_object* v_W_216_, lean_object* v_O_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_T_221_, lean_object* v_h_222_, lean_object* v_s_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = lp_GRH_New_FrobeniusCycle_letterConj(v_N_214_, v_k_215_, v_W_216_, v_O_217_, v_inst_218_, v_inst_219_, v_inst_220_, v_T_221_, v_h_222_, v_s_223_);
lean_dec_ref(v_inst_218_);
lean_dec(v_N_214_);
return v_res_224_;
}
}
static lean_object* _init_lp_GRH_New_rootVector___redArg___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_nat_to_int(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_lp_GRH_New_rootVector___redArg___closed__1(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_to_int(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootVector___redArg(lean_object* v_a_229_, lean_object* v_a_x27_230_, lean_object* v_b_231_){
_start:
{
lean_object* v___y_233_; uint8_t v___x_239_; 
v___x_239_ = lean_nat_dec_eq(v_b_231_, v_a_x27_230_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&lp_GRH_New_rootVector___redArg___closed__0, &lp_GRH_New_rootVector___redArg___closed__0_once, _init_lp_GRH_New_rootVector___redArg___closed__0);
v___y_233_ = v___x_240_;
goto v___jp_232_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&lp_GRH_New_rootVector___redArg___closed__1, &lp_GRH_New_rootVector___redArg___closed__1_once, _init_lp_GRH_New_rootVector___redArg___closed__1);
v___y_233_ = v___x_241_;
goto v___jp_232_;
}
v___jp_232_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_nat_dec_eq(v_b_231_, v_a_229_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&lp_GRH_New_rootVector___redArg___closed__0, &lp_GRH_New_rootVector___redArg___closed__0_once, _init_lp_GRH_New_rootVector___redArg___closed__0);
v___x_236_ = lean_int_sub(v___y_233_, v___x_235_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&lp_GRH_New_rootVector___redArg___closed__1, &lp_GRH_New_rootVector___redArg___closed__1_once, _init_lp_GRH_New_rootVector___redArg___closed__1);
v___x_238_ = lean_int_sub(v___y_233_, v___x_237_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootVector___redArg___boxed(lean_object* v_a_242_, lean_object* v_a_x27_243_, lean_object* v_b_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_GRH_New_rootVector___redArg(v_a_242_, v_a_x27_243_, v_b_244_);
lean_dec(v_b_244_);
lean_dec(v_a_x27_243_);
lean_dec(v_a_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootVector(lean_object* v_k_246_, lean_object* v_a_247_, lean_object* v_a_x27_248_, lean_object* v_b_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lp_GRH_New_rootVector___redArg(v_a_247_, v_a_x27_248_, v_b_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_rootVector___boxed(lean_object* v_k_251_, lean_object* v_a_252_, lean_object* v_a_x27_253_, lean_object* v_b_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = lp_GRH_New_rootVector(v_k_251_, v_a_252_, v_a_x27_253_, v_b_254_);
lean_dec(v_b_254_);
lean_dec(v_a_x27_253_);
lean_dec(v_a_252_);
lean_dec(v_k_251_);
return v_res_255_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_ElementaryDivisors_FrobeniusFactors(uint8_t builtin) {
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
res = initialize_GRH_New_UpperBound_ElementaryDivisors_RootLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
