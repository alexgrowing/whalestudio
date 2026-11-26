// Lean compiler output
// Module: Lib.Weil.Periods.Grading
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.RationalPoints public import Lib.DiscreteSeries.Rigidity.KernelFixes
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
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_GRH_New_U_conj___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Fin_rev___boxed(lean_object*, lean_object*);
lean_object* l_Sum_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_gradedGram___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_gradedGram___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Grading_gradeOf___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__0;
static lean_once_cell_t lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Grading_gradeOf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Grading_gradeOf___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Grading_gradeOf___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Grading_gradeOf___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Grading_stringReversal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Grading_stringReversal___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Grading_stringReversal___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringReversal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringReversal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringReversal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_mapDegree___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_mapDegree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_mapDegree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_frameEquiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_frameEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_frameEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks___redArg___lam__0(lean_object* v___x_1_, lean_object* v___y_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v___x_1_, 0);
lean_inc(v_toFun_3_);
lean_dec_ref(v___x_1_);
v___x_4_ = lean_apply_1(v_toFun_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks___redArg(lean_object* v_inst_5_, lean_object* v_e_x27_6_, lean_object* v_e_7_, lean_object* v_A_8_, lean_object* v_B_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_toSemiring_12_; lean_object* v___x_13_; lean_object* v_toZero_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v___x_21_; 
v_toSemiring_12_ = lean_ctor_get(v_inst_5_, 0);
lean_inc_ref(v_toSemiring_12_);
lean_dec_ref(v_inst_5_);
v___x_13_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_12_);
v_toZero_14_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_toZero_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_15_, 0, lean_box(0));
lean_closure_set(v___x_15_, 1, lean_box(0));
lean_closure_set(v___x_15_, 2, lean_box(0));
lean_closure_set(v___x_15_, 3, v_toZero_14_);
lean_inc_ref(v___x_15_);
v___x_16_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_16_, 0, lean_box(0));
lean_closure_set(v___x_16_, 1, lean_box(0));
lean_closure_set(v___x_16_, 2, lean_box(0));
lean_closure_set(v___x_16_, 3, lean_box(0));
lean_closure_set(v___x_16_, 4, lean_box(0));
lean_closure_set(v___x_16_, 5, v_A_8_);
lean_closure_set(v___x_16_, 6, v___x_15_);
lean_closure_set(v___x_16_, 7, v___x_15_);
lean_closure_set(v___x_16_, 8, v_B_9_);
v___x_17_ = lp_mathlib_Equiv_symm___redArg(v_e_x27_6_);
v___f_18_ = lean_alloc_closure((void*)(lp_GRH_New_gradedBlocks___redArg___lam__0), 2, 1);
lean_closure_set(v___f_18_, 0, v___x_17_);
v___x_19_ = lp_mathlib_Equiv_symm___redArg(v_e_7_);
v___f_20_ = lean_alloc_closure((void*)(lp_GRH_New_gradedBlocks___redArg___lam__0), 2, 1);
lean_closure_set(v___f_20_, 0, v___x_19_);
v___x_21_ = lp_mathlib_Matrix_submatrix___redArg(v___x_16_, v___f_18_, v___f_20_, v_a_10_, v_a_11_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks(lean_object* v_R_22_, lean_object* v_X_23_, lean_object* v_X_x27_24_, lean_object* v_00_u03b9_25_, lean_object* v_00_u03b9_x27_26_, lean_object* v_s_27_, lean_object* v_s_x27_28_, lean_object* v_inst_29_, lean_object* v_e_x27_30_, lean_object* v_e_31_, lean_object* v_A_32_, lean_object* v_B_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_toSemiring_36_; lean_object* v___x_37_; lean_object* v_toZero_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___f_44_; lean_object* v___x_45_; 
v_toSemiring_36_ = lean_ctor_get(v_inst_29_, 0);
lean_inc_ref(v_toSemiring_36_);
lean_dec_ref(v_inst_29_);
v___x_37_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_36_);
v_toZero_38_ = lean_ctor_get(v___x_37_, 1);
lean_inc(v_toZero_38_);
lean_dec_ref(v___x_37_);
v___x_39_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_39_, 0, lean_box(0));
lean_closure_set(v___x_39_, 1, lean_box(0));
lean_closure_set(v___x_39_, 2, lean_box(0));
lean_closure_set(v___x_39_, 3, v_toZero_38_);
lean_inc_ref(v___x_39_);
v___x_40_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_40_, 0, lean_box(0));
lean_closure_set(v___x_40_, 1, lean_box(0));
lean_closure_set(v___x_40_, 2, lean_box(0));
lean_closure_set(v___x_40_, 3, lean_box(0));
lean_closure_set(v___x_40_, 4, lean_box(0));
lean_closure_set(v___x_40_, 5, v_A_32_);
lean_closure_set(v___x_40_, 6, v___x_39_);
lean_closure_set(v___x_40_, 7, v___x_39_);
lean_closure_set(v___x_40_, 8, v_B_33_);
v___x_41_ = lp_mathlib_Equiv_symm___redArg(v_e_x27_30_);
v___f_42_ = lean_alloc_closure((void*)(lp_GRH_New_gradedBlocks___redArg___lam__0), 2, 1);
lean_closure_set(v___f_42_, 0, v___x_41_);
v___x_43_ = lp_mathlib_Equiv_symm___redArg(v_e_31_);
v___f_44_ = lean_alloc_closure((void*)(lp_GRH_New_gradedBlocks___redArg___lam__0), 2, 1);
lean_closure_set(v___f_44_, 0, v___x_43_);
v___x_45_ = lp_mathlib_Matrix_submatrix___redArg(v___x_40_, v___f_42_, v___f_44_, v_a_34_, v_a_35_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedBlocks___boxed(lean_object* v_R_46_, lean_object* v_X_47_, lean_object* v_X_x27_48_, lean_object* v_00_u03b9_49_, lean_object* v_00_u03b9_x27_50_, lean_object* v_s_51_, lean_object* v_s_x27_52_, lean_object* v_inst_53_, lean_object* v_e_x27_54_, lean_object* v_e_55_, lean_object* v_A_56_, lean_object* v_B_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_GRH_New_gradedBlocks(v_R_46_, v_X_47_, v_X_x27_48_, v_00_u03b9_49_, v_00_u03b9_x27_50_, v_s_51_, v_s_x27_52_, v_inst_53_, v_e_x27_54_, v_e_55_, v_A_56_, v_B_57_, v_a_58_, v_a_59_);
lean_dec(v_s_x27_52_);
lean_dec(v_s_51_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__0(lean_object* v_toOne_61_, lean_object* v_x_62_){
_start:
{
lean_inc(v_toOne_61_);
return v_toOne_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__0___boxed(lean_object* v_toOne_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_GRH_New_gradedGram___redArg___lam__0(v_toOne_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_toOne_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__1(lean_object* v_s_66_, lean_object* v_toZero_67_, lean_object* v_toOne_68_, lean_object* v_toNeg_69_, lean_object* v_N_70_, lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_b_72_, v___x_73_);
v___x_75_ = lean_nat_sub(v_s_66_, v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = lean_nat_dec_eq(v_a_71_, v___x_75_);
lean_dec(v___x_75_);
if (v___x_76_ == 0)
{
lean_dec(v_N_70_);
lean_dec(v_toNeg_69_);
lean_inc(v_toZero_67_);
return v_toZero_67_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_eq(v_a_71_, v_b_72_);
if (v___x_77_ == 0)
{
lean_dec(v_N_70_);
lean_dec(v_toNeg_69_);
lean_inc(v_toOne_68_);
return v_toOne_68_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = lean_apply_1(v_toNeg_69_, v_N_70_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__1___boxed(lean_object* v_s_79_, lean_object* v_toZero_80_, lean_object* v_toOne_81_, lean_object* v_toNeg_82_, lean_object* v_N_83_, lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_gradedGram___redArg___lam__1(v_s_79_, v_toZero_80_, v_toOne_81_, v_toNeg_82_, v_N_83_, v_a_84_, v_b_85_);
lean_dec(v_b_85_);
lean_dec(v_a_84_);
lean_dec(v_toOne_81_);
lean_dec(v_toZero_80_);
lean_dec(v_s_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg___lam__2(lean_object* v___x_87_, lean_object* v___f_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_toFun_91_; lean_object* v___x_92_; 
v_toFun_91_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_toFun_91_);
lean_dec_ref(v___x_87_);
v___x_92_ = lean_apply_3(v_toFun_91_, v___f_88_, v___y_89_, v___y_90_);
return v___x_92_;
}
}
static lean_object* _init_lp_GRH_New_gradedGram___redArg___closed__0(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_mathlib_Equiv_refl___redArg();
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram___redArg(lean_object* v_s_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_e_97_, lean_object* v_N_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_toSemiring_101_; lean_object* v___x_102_; lean_object* v_toZero_103_; lean_object* v___x_104_; lean_object* v_toAddMonoidWithOne_105_; lean_object* v_toOne_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_toNeg_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_toSemiring_101_ = lean_ctor_get(v_inst_95_, 0);
lean_inc_ref(v_toSemiring_101_);
v___x_102_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_101_);
v_toZero_103_ = lean_ctor_get(v___x_102_, 1);
lean_inc_n(v_toZero_103_, 3);
lean_dec_ref(v___x_102_);
lean_inc_ref(v_inst_95_);
v___x_104_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_95_);
v_toAddMonoidWithOne_105_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_toAddMonoidWithOne_105_);
lean_dec_ref(v___x_104_);
v_toOne_106_ = lean_ctor_get(v_toAddMonoidWithOne_105_, 2);
lean_inc_n(v_toOne_106_, 2);
lean_dec_ref(v_toAddMonoidWithOne_105_);
v___x_107_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_95_);
lean_dec_ref(v_inst_95_);
v___x_108_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_107_);
lean_dec_ref(v___x_107_);
v_toNeg_109_ = lean_ctor_get(v___x_108_, 1);
lean_inc(v_toNeg_109_);
lean_dec_ref(v___x_108_);
v___f_110_ = lean_alloc_closure((void*)(lp_GRH_New_gradedGram___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_110_, 0, v_toOne_106_);
v___x_111_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_111_, 0, lean_box(0));
lean_closure_set(v___x_111_, 1, lean_box(0));
lean_closure_set(v___x_111_, 2, v_inst_96_);
lean_closure_set(v___x_111_, 3, v_toZero_103_);
lean_closure_set(v___x_111_, 4, v___f_110_);
v___f_112_ = lean_alloc_closure((void*)(lp_GRH_New_gradedGram___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_112_, 0, v_s_94_);
lean_closure_set(v___f_112_, 1, v_toZero_103_);
lean_closure_set(v___f_112_, 2, v_toOne_106_);
lean_closure_set(v___f_112_, 3, v_toNeg_109_);
lean_closure_set(v___f_112_, 4, v_N_98_);
v___x_113_ = lean_obj_once(&lp_GRH_New_gradedGram___redArg___closed__0, &lp_GRH_New_gradedGram___redArg___closed__0_once, _init_lp_GRH_New_gradedGram___redArg___closed__0);
v___f_114_ = lean_alloc_closure((void*)(lp_GRH_New_gradedGram___redArg___lam__2), 4, 2);
lean_closure_set(v___f_114_, 0, v___x_113_);
lean_closure_set(v___f_114_, 1, v___f_112_);
v___x_115_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_115_, 0, lean_box(0));
lean_closure_set(v___x_115_, 1, lean_box(0));
lean_closure_set(v___x_115_, 2, lean_box(0));
lean_closure_set(v___x_115_, 3, v_toZero_103_);
lean_inc_ref(v___x_115_);
v___x_116_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, lean_box(0));
lean_closure_set(v___x_116_, 2, lean_box(0));
lean_closure_set(v___x_116_, 3, lean_box(0));
lean_closure_set(v___x_116_, 4, lean_box(0));
lean_closure_set(v___x_116_, 5, v___x_111_);
lean_closure_set(v___x_116_, 6, v___x_115_);
lean_closure_set(v___x_116_, 7, v___x_115_);
lean_closure_set(v___x_116_, 8, v___f_114_);
v___x_117_ = lp_mathlib_Equiv_symm___redArg(v_e_97_);
v___f_118_ = lean_alloc_closure((void*)(lp_GRH_New_gradedBlocks___redArg___lam__0), 2, 1);
lean_closure_set(v___f_118_, 0, v___x_117_);
lean_inc_ref(v___f_118_);
v___x_119_ = lp_mathlib_Matrix_submatrix___redArg(v___x_116_, v___f_118_, v___f_118_, v_a_99_, v_a_100_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedGram(lean_object* v_R_120_, lean_object* v_X_121_, lean_object* v_00_u03b9_122_, lean_object* v_s_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_e_126_, lean_object* v_N_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_GRH_New_gradedGram___redArg(v_s_123_, v_inst_124_, v_inst_125_, v_e_126_, v_N_127_, v_a_128_, v_a_129_);
return v___x_130_;
}
}
static lean_object* _init_lp_GRH_New_Grading_gradeOf___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__0(lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&lp_GRH_New_Grading_gradeOf___redArg___lam__0___closed__0, &lp_GRH_New_Grading_gradeOf___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Grading_gradeOf___redArg___lam__0___closed__0);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__0___boxed(lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = lp_GRH_New_Grading_gradeOf___redArg___lam__0(v_x_135_);
lean_dec(v_x_135_);
return v_res_136_;
}
}
static lean_object* _init_lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_to_int(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = lean_nat_to_int(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg___lam__1(lean_object* v_s_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_143_ = lean_nat_to_int(v_s_141_);
v___x_144_ = lean_obj_once(&lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__0, &lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__0_once, _init_lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__0);
v___x_145_ = lean_int_sub(v___x_143_, v___x_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_obj_once(&lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__1, &lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__1_once, _init_lp_GRH_New_Grading_gradeOf___redArg___lam__1___closed__1);
v___x_147_ = lean_nat_to_int(v_a_142_);
v___x_148_ = lean_int_mul(v___x_146_, v___x_147_);
lean_dec(v___x_147_);
v___x_149_ = lean_int_sub(v___x_145_, v___x_148_);
lean_dec(v___x_148_);
lean_dec(v___x_145_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___redArg(lean_object* v_s_151_, lean_object* v_Y_152_, lean_object* v_i_153_){
_start:
{
lean_object* v_indexEquiv_154_; lean_object* v___x_155_; lean_object* v_toFun_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_indexEquiv_154_ = lean_ctor_get(v_Y_152_, 0);
lean_inc_ref(v_indexEquiv_154_);
lean_dec_ref(v_Y_152_);
v___x_155_ = lp_mathlib_Equiv_symm___redArg(v_indexEquiv_154_);
v_toFun_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_toFun_156_);
lean_dec_ref(v___x_155_);
v___f_157_ = ((lean_object*)(lp_GRH_New_Grading_gradeOf___redArg___closed__0));
v___f_158_ = lean_alloc_closure((void*)(lp_GRH_New_Grading_gradeOf___redArg___lam__1), 2, 1);
lean_closure_set(v___f_158_, 0, v_s_151_);
v___x_159_ = lean_apply_1(v_toFun_156_, v_i_153_);
v___x_160_ = l_Sum_elim___redArg(v___f_157_, v___f_158_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf(lean_object* v_X_161_, lean_object* v_00_u03b9_162_, lean_object* v_s_163_, lean_object* v_E_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_00_u03b5_170_, lean_object* v_N_171_, lean_object* v_V_172_, lean_object* v_Y_173_, lean_object* v_i_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lp_GRH_New_Grading_gradeOf___redArg(v_s_163_, v_Y_173_, v_i_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_gradeOf___boxed(lean_object* v_X_176_, lean_object* v_00_u03b9_177_, lean_object* v_s_178_, lean_object* v_E_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_00_u03b5_185_, lean_object* v_N_186_, lean_object* v_V_187_, lean_object* v_Y_188_, lean_object* v_i_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_GRH_New_Grading_gradeOf(v_X_176_, v_00_u03b9_177_, v_s_178_, v_E_179_, v_inst_180_, v_inst_181_, v_inst_182_, v_inst_183_, v_inst_184_, v_00_u03b5_185_, v_N_186_, v_V_187_, v_Y_188_, v_i_189_);
lean_dec_ref(v_V_187_);
lean_dec(v_N_186_);
lean_dec_ref(v_00_u03b5_185_);
lean_dec_ref(v_inst_184_);
lean_dec_ref(v_inst_183_);
lean_dec(v_inst_182_);
lean_dec_ref(v_inst_181_);
lean_dec_ref(v_inst_180_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringReversal___redArg(lean_object* v_s_192_, lean_object* v_Y_193_, lean_object* v_i_194_){
_start:
{
lean_object* v_indexEquiv_195_; lean_object* v___x_196_; lean_object* v_toFun_197_; lean_object* v_toFun_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_indexEquiv_195_ = lean_ctor_get(v_Y_193_, 0);
lean_inc_ref_n(v_indexEquiv_195_, 2);
lean_dec_ref(v_Y_193_);
v___x_196_ = lp_mathlib_Equiv_symm___redArg(v_indexEquiv_195_);
v_toFun_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_toFun_197_);
lean_dec_ref(v___x_196_);
v_toFun_198_ = lean_ctor_get(v_indexEquiv_195_, 0);
lean_inc(v_toFun_198_);
lean_dec_ref(v_indexEquiv_195_);
v___x_199_ = ((lean_object*)(lp_GRH_New_Grading_stringReversal___redArg___closed__0));
v___x_200_ = lean_alloc_closure((void*)(l_Fin_rev___boxed), 2, 1);
lean_closure_set(v___x_200_, 0, v_s_192_);
v___x_201_ = lean_apply_1(v_toFun_197_, v_i_194_);
v___x_202_ = l_Sum_map___redArg(v___x_199_, v___x_200_, v___x_201_);
v___x_203_ = lean_apply_1(v_toFun_198_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringReversal(lean_object* v_E_204_, lean_object* v_00_u03b9_205_, lean_object* v_X_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_s_212_, lean_object* v_00_u03b5_213_, lean_object* v_N_214_, lean_object* v_V_215_, lean_object* v_Y_216_, lean_object* v_i_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lp_GRH_New_Grading_stringReversal___redArg(v_s_212_, v_Y_216_, v_i_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_stringReversal___boxed(lean_object* v_E_219_, lean_object* v_00_u03b9_220_, lean_object* v_X_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_s_227_, lean_object* v_00_u03b5_228_, lean_object* v_N_229_, lean_object* v_V_230_, lean_object* v_Y_231_, lean_object* v_i_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = lp_GRH_New_Grading_stringReversal(v_E_219_, v_00_u03b9_220_, v_X_221_, v_inst_222_, v_inst_223_, v_inst_224_, v_inst_225_, v_inst_226_, v_s_227_, v_00_u03b5_228_, v_N_229_, v_V_230_, v_Y_231_, v_i_232_);
lean_dec_ref(v_V_230_);
lean_dec(v_N_229_);
lean_dec_ref(v_00_u03b5_228_);
lean_dec_ref(v_inst_226_);
lean_dec(v_inst_225_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v_inst_223_);
lean_dec_ref(v_inst_222_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_mapDegree___redArg(lean_object* v_s_234_, lean_object* v_Y_235_, lean_object* v_d_236_, lean_object* v_r_237_){
_start:
{
lean_object* v_fst_238_; lean_object* v_snd_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_fst_238_ = lean_ctor_get(v_r_237_, 0);
lean_inc(v_fst_238_);
v_snd_239_ = lean_ctor_get(v_r_237_, 1);
lean_inc(v_snd_239_);
lean_dec_ref(v_r_237_);
v___x_240_ = lean_apply_1(v_d_236_, v_fst_238_);
v___x_241_ = lp_GRH_New_Grading_gradeOf___redArg(v_s_234_, v_Y_235_, v_snd_239_);
v___x_242_ = lean_int_sub(v___x_240_, v___x_241_);
lean_dec(v___x_241_);
lean_dec(v___x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_mapDegree(lean_object* v_E_243_, lean_object* v_00_u03b9_244_, lean_object* v_00_u03b9_x27_245_, lean_object* v_X_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_s_252_, lean_object* v_00_u03b5_253_, lean_object* v_N_254_, lean_object* v_V_255_, lean_object* v_Y_256_, lean_object* v_d_257_, lean_object* v_r_258_){
_start:
{
lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_fst_259_ = lean_ctor_get(v_r_258_, 0);
lean_inc(v_fst_259_);
v_snd_260_ = lean_ctor_get(v_r_258_, 1);
lean_inc(v_snd_260_);
lean_dec_ref(v_r_258_);
v___x_261_ = lean_apply_1(v_d_257_, v_fst_259_);
v___x_262_ = lp_GRH_New_Grading_gradeOf___redArg(v_s_252_, v_Y_256_, v_snd_260_);
v___x_263_ = lean_int_sub(v___x_261_, v___x_262_);
lean_dec(v___x_262_);
lean_dec(v___x_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_mapDegree___boxed(lean_object* v_E_264_, lean_object* v_00_u03b9_265_, lean_object* v_00_u03b9_x27_266_, lean_object* v_X_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_s_273_, lean_object* v_00_u03b5_274_, lean_object* v_N_275_, lean_object* v_V_276_, lean_object* v_Y_277_, lean_object* v_d_278_, lean_object* v_r_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = lp_GRH_New_Grading_mapDegree(v_E_264_, v_00_u03b9_265_, v_00_u03b9_x27_266_, v_X_267_, v_inst_268_, v_inst_269_, v_inst_270_, v_inst_271_, v_inst_272_, v_s_273_, v_00_u03b5_274_, v_N_275_, v_V_276_, v_Y_277_, v_d_278_, v_r_279_);
lean_dec_ref(v_V_276_);
lean_dec(v_N_275_);
lean_dec_ref(v_00_u03b5_274_);
lean_dec_ref(v_inst_272_);
lean_dec(v_inst_271_);
lean_dec_ref(v_inst_270_);
lean_dec_ref(v_inst_269_);
lean_dec_ref(v_inst_268_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps___redArg(){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_box(0);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps___redArg___boxed(lean_object* v___dummy_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_GRH_New_Grading_nonnegMaps___redArg();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps(lean_object* v_E_285_, lean_object* v_00_u03b9_286_, lean_object* v_00_u03b9_x27_287_, lean_object* v_X_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_s_294_, lean_object* v_00_u03b5_295_, lean_object* v_N_296_, lean_object* v_V_297_, lean_object* v_Y_298_, lean_object* v_d_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Grading_nonnegMaps___boxed(lean_object* v_E_301_, lean_object* v_00_u03b9_302_, lean_object* v_00_u03b9_x27_303_, lean_object* v_X_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_s_310_, lean_object* v_00_u03b5_311_, lean_object* v_N_312_, lean_object* v_V_313_, lean_object* v_Y_314_, lean_object* v_d_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = lp_GRH_New_Grading_nonnegMaps(v_E_301_, v_00_u03b9_302_, v_00_u03b9_x27_303_, v_X_304_, v_inst_305_, v_inst_306_, v_inst_307_, v_inst_308_, v_inst_309_, v_s_310_, v_00_u03b5_311_, v_N_312_, v_V_313_, v_Y_314_, v_d_315_);
lean_dec_ref(v_d_315_);
lean_dec_ref(v_Y_314_);
lean_dec_ref(v_V_313_);
lean_dec(v_N_312_);
lean_dec_ref(v_00_u03b5_311_);
lean_dec(v_s_310_);
lean_dec_ref(v_inst_309_);
lean_dec(v_inst_308_);
lean_dec_ref(v_inst_307_);
lean_dec_ref(v_inst_306_);
lean_dec_ref(v_inst_305_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_frameEquiv___redArg(lean_object* v_inst_317_, lean_object* v_p_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lp_mathlib_Complex_commRing;
v___x_320_ = lp_GRH_New_U_conj___redArg(v_inst_317_, v___x_319_, v_p_318_);
v___x_321_ = lp_mathlib_Equiv_symm___redArg(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_frameEquiv(lean_object* v_n_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_00_u03b5_325_, lean_object* v_J_326_, lean_object* v_p_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lp_GRH_New_DiscreteSeries_frameEquiv___redArg(v_inst_323_, v_p_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_frameEquiv___boxed(lean_object* v_n_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_00_u03b5_332_, lean_object* v_J_333_, lean_object* v_p_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = lp_GRH_New_DiscreteSeries_frameEquiv(v_n_329_, v_inst_330_, v_inst_331_, v_00_u03b5_332_, v_J_333_, v_p_334_);
lean_dec_ref(v_J_333_);
lean_dec_ref(v_00_u03b5_332_);
lean_dec_ref(v_inst_331_);
return v_res_335_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_RationalPoints(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Rigidity_KernelFixes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Periods_Grading(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_RationalPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Rigidity_KernelFixes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
