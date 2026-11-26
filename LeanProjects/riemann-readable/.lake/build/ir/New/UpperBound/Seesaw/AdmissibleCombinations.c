// Lean compiler output
// Module: New.UpperBound.Seesaw.AdmissibleCombinations
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.PAdicGauge public import Lib.ClassField.HeckeCharacter.AlgebraicValues public import Lib.General.LinearAlgebra.TensorChains public import Lib.Weil.DualPair.WeilAction
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_gradedLatticeBasis___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_gradedLatticeBasis___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_gradedLatticeBasis___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Seesaw_stringSign___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Seesaw_stringSign___closed__0;
static lean_once_cell_t lp_GRH_New_Seesaw_stringSign___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Seesaw_stringSign___closed__1;
static lean_once_cell_t lp_GRH_New_Seesaw_stringSign___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Seesaw_stringSign___closed__2;
static lean_once_cell_t lp_GRH_New_Seesaw_stringSign___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Seesaw_stringSign___closed__3;
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_stringSign(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_stringSign___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__0(lean_object* v_00_u03c0_1_, lean_object* v_inst_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_inv_4_; lean_object* v___x_5_; 
v_inv_4_ = lean_ctor_get(v_00_u03c0_1_, 1);
lean_inc(v_inv_4_);
lean_dec_ref(v_00_u03c0_1_);
v___x_5_ = lean_apply_1(v_inst_2_, v_inv_4_);
return v___x_5_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_gradedLatticeBasis___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_10_ = l_instDecidableEqSum_decEq___redArg(v_inst_6_, v___x_9_, v_a_7_, v_b_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__1___boxed(lean_object* v_inst_11_, lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__1(v_inst_11_, v_a_12_, v_b_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__3(lean_object* v_toZero_16_, lean_object* v_x_17_){
_start:
{
lean_inc(v_toZero_16_);
return v_toZero_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__3___boxed(lean_object* v_toZero_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__3(v_toZero_18_, v_x_19_);
lean_dec(v_x_19_);
lean_dec(v_toZero_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__2(lean_object* v_toOne_21_, lean_object* v_x_22_){
_start:
{
lean_inc(v_toOne_21_);
return v_toOne_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__2___boxed(lean_object* v_toOne_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__2(v_toOne_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_toOne_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__4(lean_object* v_toOne_26_, lean_object* v_x_27_){
_start:
{
lean_inc(v_toOne_26_);
return v_toOne_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__4___boxed(lean_object* v_toOne_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__4(v_toOne_28_, v_x_29_);
lean_dec_ref(v_x_29_);
lean_dec(v_toOne_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__5(lean_object* v_b_31_, lean_object* v_s_32_, lean_object* v_toZero_33_, lean_object* v_00_u03c0_34_, lean_object* v_toMonoid_35_, lean_object* v_inst_36_, lean_object* v_toMul_37_, lean_object* v_u_38_, lean_object* v_x_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_add(v_b_31_, v___x_40_);
v___x_42_ = lean_nat_sub(v_s_32_, v___x_41_);
lean_dec(v___x_41_);
v___x_43_ = lean_nat_dec_eq(v_b_31_, v___x_42_);
lean_dec(v___x_42_);
if (v___x_43_ == 0)
{
lean_dec(v_u_38_);
lean_dec(v_toMul_37_);
lean_dec(v_inst_36_);
lean_dec_ref(v_00_u03c0_34_);
lean_inc(v_toZero_33_);
return v_toZero_33_;
}
else
{
lean_object* v_inv_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toMul_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_inv_44_ = lean_ctor_get(v_00_u03c0_34_, 1);
lean_inc_n(v_inv_44_, 2);
lean_dec_ref(v_00_u03c0_34_);
v___x_45_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_35_);
v___x_46_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_45_);
v_toMul_47_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_toMul_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_apply_1(v_inst_36_, v_inv_44_);
v___x_49_ = lean_apply_2(v_toMul_47_, v_inv_44_, v___x_48_);
v___x_50_ = lean_apply_2(v_toMul_37_, v_u_38_, v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__5___boxed(lean_object* v_b_51_, lean_object* v_s_52_, lean_object* v_toZero_53_, lean_object* v_00_u03c0_54_, lean_object* v_toMonoid_55_, lean_object* v_inst_56_, lean_object* v_toMul_57_, lean_object* v_u_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__5(v_b_51_, v_s_52_, v_toZero_53_, v_00_u03c0_54_, v_toMonoid_55_, v_inst_56_, v_toMul_57_, v_u_58_, v_x_59_);
lean_dec_ref(v_toMonoid_55_);
lean_dec(v_toZero_53_);
lean_dec(v_s_52_);
lean_dec(v_b_51_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__6(lean_object* v_s_61_, lean_object* v_toZero_62_, lean_object* v_00_u03c0_63_, lean_object* v_toMonoid_64_, lean_object* v_inst_65_, lean_object* v_toMul_66_, lean_object* v_u_67_, lean_object* v___f_68_, lean_object* v_b_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; 
v___f_71_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_71_, 0, v_b_69_);
lean_closure_set(v___f_71_, 1, v_s_61_);
lean_closure_set(v___f_71_, 2, v_toZero_62_);
lean_closure_set(v___f_71_, 3, v_00_u03c0_63_);
lean_closure_set(v___f_71_, 4, v_toMonoid_64_);
lean_closure_set(v___f_71_, 5, v_inst_65_);
lean_closure_set(v___f_71_, 6, v_toMul_66_);
lean_closure_set(v___f_71_, 7, v_u_67_);
v___x_72_ = l_Sum_elim___redArg(v___f_68_, v___f_71_, v___y_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__7(uint8_t v___x_73_, lean_object* v___f_74_, lean_object* v_toZero_75_, lean_object* v___f_76_, lean_object* v___f_77_, lean_object* v___f_78_, lean_object* v___f_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
if (v___x_73_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref(v___f_79_);
lean_dec(v___f_78_);
lean_dec(v___f_77_);
v___x_82_ = lp_mathlib_Matrix_diagonal___redArg(v___f_74_, v_toZero_75_, v___f_76_, v___y_80_, v___y_81_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v___f_76_);
lean_dec_ref(v___f_74_);
v___x_83_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, lean_box(0));
lean_closure_set(v___x_83_, 2, lean_box(0));
lean_closure_set(v___x_83_, 3, v___f_77_);
lean_closure_set(v___x_83_, 4, v___f_78_);
v___x_84_ = lp_mathlib_Matrix_diagonal___redArg(v___f_79_, v_toZero_75_, v___x_83_, v___y_80_, v___y_81_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__7___boxed(lean_object* v___x_85_, lean_object* v___f_86_, lean_object* v_toZero_87_, lean_object* v___f_88_, lean_object* v___f_89_, lean_object* v___f_90_, lean_object* v___f_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___x_1134__boxed_94_; lean_object* v_res_95_; 
v___x_1134__boxed_94_ = lean_unbox(v___x_85_);
v_res_95_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__7(v___x_1134__boxed_94_, v___f_86_, v_toZero_87_, v___f_88_, v___f_89_, v___f_90_, v___f_91_, v___y_92_, v___y_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__8(uint8_t v___x_96_, lean_object* v___x_97_, lean_object* v_s_98_, lean_object* v_a_99_, lean_object* v_inst_100_, lean_object* v_toMul_101_, lean_object* v_u_102_, lean_object* v_toOne_103_, lean_object* v_b_104_){
_start:
{
if (v___x_96_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
lean_dec(v_toOne_103_);
v___x_105_ = lean_nat_mul(v___x_97_, v_b_104_);
v___x_106_ = lean_nat_dec_lt(v___x_105_, v_s_98_);
lean_dec(v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v_val_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_val_107_ = lean_ctor_get(v_a_99_, 0);
lean_inc(v_val_107_);
lean_dec_ref(v_a_99_);
v___x_108_ = lean_apply_1(v_inst_100_, v_val_107_);
v___x_109_ = lean_apply_2(v_toMul_101_, v_u_102_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v_inv_110_; lean_object* v___x_111_; 
lean_dec(v_inst_100_);
v_inv_110_ = lean_ctor_get(v_a_99_, 1);
lean_inc(v_inv_110_);
lean_dec_ref(v_a_99_);
v___x_111_ = lean_apply_2(v_toMul_101_, v_u_102_, v_inv_110_);
return v___x_111_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec(v_inst_100_);
lean_dec_ref(v_a_99_);
v___x_112_ = lean_apply_2(v_toMul_101_, v_u_102_, v_toOne_103_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__8___boxed(lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_s_115_, lean_object* v_a_116_, lean_object* v_inst_117_, lean_object* v_toMul_118_, lean_object* v_u_119_, lean_object* v_toOne_120_, lean_object* v_b_121_){
_start:
{
uint8_t v___x_1164__boxed_122_; lean_object* v_res_123_; 
v___x_1164__boxed_122_ = lean_unbox(v___x_113_);
v_res_123_ = lp_GRH_New_gradedLatticeBasis___redArg___lam__8(v___x_1164__boxed_122_, v___x_114_, v_s_115_, v_a_116_, v_inst_117_, v_toMul_118_, v_u_119_, v_toOne_120_, v_b_121_);
lean_dec(v_b_121_);
lean_dec(v_s_115_);
lean_dec(v___x_114_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg___lam__9(lean_object* v___x_124_, lean_object* v___f_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_toFun_128_; lean_object* v___x_129_; 
v_toFun_128_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_toFun_128_);
lean_dec_ref(v___x_124_);
v___x_129_ = lean_apply_3(v_toFun_128_, v___f_125_, v___y_126_, v___y_127_);
return v___x_129_;
}
}
static lean_object* _init_lp_GRH_New_gradedLatticeBasis___redArg___closed__0(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_mathlib_Equiv_refl___redArg();
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis___redArg(lean_object* v_inst_131_, lean_object* v_s_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_00_u03c0_137_, lean_object* v_u_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_toSemiring_141_; lean_object* v___x_142_; lean_object* v_toZero_143_; lean_object* v___x_144_; lean_object* v_toAddMonoidWithOne_145_; lean_object* v_toOne_146_; lean_object* v_toMonoid_147_; lean_object* v___x_148_; lean_object* v_toMul_149_; lean_object* v___x_150_; lean_object* v_toFun_151_; lean_object* v___x_152_; lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___y_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_toSemiring_141_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref_n(v_toSemiring_141_, 2);
v___x_142_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_141_);
v_toZero_143_ = lean_ctor_get(v___x_142_, 1);
lean_inc_n(v_toZero_143_, 5);
lean_dec_ref(v___x_142_);
v___x_144_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_133_);
v_toAddMonoidWithOne_145_ = lean_ctor_get(v___x_144_, 1);
lean_inc_ref(v_toAddMonoidWithOne_145_);
lean_dec_ref(v___x_144_);
v_toOne_146_ = lean_ctor_get(v_toAddMonoidWithOne_145_, 2);
lean_inc_n(v_toOne_146_, 3);
lean_dec_ref(v_toAddMonoidWithOne_145_);
v_toMonoid_147_ = lean_ctor_get(v_toSemiring_141_, 1);
lean_inc_ref(v_toMonoid_147_);
v___x_148_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_141_);
v_toMul_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc_n(v_toMul_149_, 2);
lean_dec_ref(v___x_148_);
lean_inc_ref(v_e_135_);
v___x_150_ = lp_mathlib_Matrix_reindex___redArg(v_e_135_, v_e_135_);
v_toFun_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_toFun_151_);
lean_dec_ref(v___x_150_);
v___x_152_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_152_, 0, lean_box(0));
lean_closure_set(v___x_152_, 1, lean_box(0));
lean_closure_set(v___x_152_, 2, lean_box(0));
lean_closure_set(v___x_152_, 3, v_toZero_143_);
lean_inc_n(v_inst_134_, 2);
lean_inc_ref(v_00_u03c0_137_);
v___f_153_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__0), 3, 2);
lean_closure_set(v___f_153_, 0, v_00_u03c0_137_);
lean_closure_set(v___f_153_, 1, v_inst_134_);
v___f_154_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_154_, 0, v_inst_131_);
v___f_155_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_155_, 0, v_toZero_143_);
v___f_156_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_156_, 0, v_toOne_146_);
v___f_157_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_157_, 0, v_toOne_146_);
lean_inc(v_u_138_);
lean_inc_n(v_s_132_, 2);
v___f_158_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__6), 10, 8);
lean_closure_set(v___f_158_, 0, v_s_132_);
lean_closure_set(v___f_158_, 1, v_toZero_143_);
lean_closure_set(v___f_158_, 2, v_00_u03c0_137_);
lean_closure_set(v___f_158_, 3, v_toMonoid_147_);
lean_closure_set(v___f_158_, 4, v_inst_134_);
lean_closure_set(v___f_158_, 5, v_toMul_149_);
lean_closure_set(v___f_158_, 6, v_u_138_);
lean_closure_set(v___f_158_, 7, v___f_155_);
v___x_159_ = lean_unsigned_to_nat(2u);
v___x_160_ = lean_nat_mod(v_s_132_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_dec_eq(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(v___x_162_);
lean_inc_ref(v___f_154_);
v___y_164_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__7___boxed), 9, 7);
lean_closure_set(v___y_164_, 0, v___x_163_);
lean_closure_set(v___y_164_, 1, v___f_154_);
lean_closure_set(v___y_164_, 2, v_toZero_143_);
lean_closure_set(v___y_164_, 3, v___f_157_);
lean_closure_set(v___y_164_, 4, v___f_156_);
lean_closure_set(v___y_164_, 5, v___f_153_);
lean_closure_set(v___y_164_, 6, v___f_154_);
v___x_165_ = lean_box(v___x_162_);
v___f_166_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_166_, 0, v___x_165_);
lean_closure_set(v___f_166_, 1, v___x_159_);
lean_closure_set(v___f_166_, 2, v_s_132_);
lean_closure_set(v___f_166_, 3, v_a_136_);
lean_closure_set(v___f_166_, 4, v_inst_134_);
lean_closure_set(v___f_166_, 5, v_toMul_149_);
lean_closure_set(v___f_166_, 6, v_u_138_);
lean_closure_set(v___f_166_, 7, v_toOne_146_);
v___x_167_ = lean_obj_once(&lp_GRH_New_gradedLatticeBasis___redArg___closed__0, &lp_GRH_New_gradedLatticeBasis___redArg___closed__0_once, _init_lp_GRH_New_gradedLatticeBasis___redArg___closed__0);
v___f_168_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__9), 4, 2);
lean_closure_set(v___f_168_, 0, v___x_167_);
lean_closure_set(v___f_168_, 1, v___f_158_);
v___x_169_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_169_, 0, v_s_132_);
v___x_170_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, lean_box(0));
lean_closure_set(v___x_170_, 2, v___x_169_);
lean_closure_set(v___x_170_, 3, v_toZero_143_);
lean_closure_set(v___x_170_, 4, v___f_166_);
v___x_171_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_fromBlocks), 11, 9);
lean_closure_set(v___x_171_, 0, lean_box(0));
lean_closure_set(v___x_171_, 1, lean_box(0));
lean_closure_set(v___x_171_, 2, lean_box(0));
lean_closure_set(v___x_171_, 3, lean_box(0));
lean_closure_set(v___x_171_, 4, lean_box(0));
lean_closure_set(v___x_171_, 5, v___y_164_);
lean_closure_set(v___x_171_, 6, v___x_152_);
lean_closure_set(v___x_171_, 7, v___f_168_);
lean_closure_set(v___x_171_, 8, v___x_170_);
v___x_172_ = lean_apply_3(v_toFun_151_, v___x_171_, v_a_139_, v_a_140_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_gradedLatticeBasis(lean_object* v_R_173_, lean_object* v_X_x27_174_, lean_object* v_00_u03b9_175_, lean_object* v_inst_176_, lean_object* v_s_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_00_u03c0_182_, lean_object* v_u_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lp_GRH_New_gradedLatticeBasis___redArg(v_inst_176_, v_s_177_, v_inst_178_, v_inst_179_, v_e_180_, v_a_181_, v_00_u03c0_182_, v_u_183_, v_a_184_, v_a_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway___redArg(){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway___redArg___boxed(lean_object* v___dummy_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_GRH_New_Seesaw_integralAway___redArg();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway(lean_object* v_n_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_integralAway___boxed(lean_object* v_n_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = lp_GRH_New_Seesaw_integralAway(v_n_193_);
lean_dec(v_n_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations___redArg(){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations___redArg___boxed(lean_object* v___dummy_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_GRH_New_Seesaw_weightedTranslations___redArg();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations(lean_object* v_00_u03b9_199_, lean_object* v_E_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_q_203_, lean_object* v_d_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_weightedTranslations___boxed(lean_object* v_00_u03b9_206_, lean_object* v_E_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_q_210_, lean_object* v_d_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = lp_GRH_New_Seesaw_weightedTranslations(v_00_u03b9_206_, v_E_207_, v_inst_208_, v_inst_209_, v_q_210_, v_d_211_);
lean_dec(v_d_211_);
lean_dec(v_q_210_);
lean_dec_ref(v_inst_208_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations___redArg(){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations___redArg___boxed(lean_object* v___dummy_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_GRH_New_Seesaw_translations___redArg();
return v_res_216_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations(lean_object* v_E_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_00_u03b9_220_, lean_object* v_q_221_, lean_object* v_d_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_translations___boxed(lean_object* v_E_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_00_u03b9_227_, lean_object* v_q_228_, lean_object* v_d_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = lp_GRH_New_Seesaw_translations(v_E_224_, v_inst_225_, v_inst_226_, v_00_u03b9_227_, v_q_228_, v_d_229_);
lean_dec(v_d_229_);
lean_dec(v_q_228_);
lean_dec_ref(v_inst_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__1(lean_object* v_toZero_231_, lean_object* v_x_232_, lean_object* v___y_233_){
_start:
{
lean_inc(v_toZero_231_);
return v_toZero_231_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__1___boxed(lean_object* v_toZero_234_, lean_object* v_x_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_GRH_New_Seesaw_gluedGram___redArg___lam__1(v_toZero_234_, v_x_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec(v_x_235_);
lean_dec(v_toZero_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__0(lean_object* v_s_238_, lean_object* v_toZero_239_, lean_object* v_toNeg_240_, lean_object* v_toOne_241_, lean_object* v_x_242_, lean_object* v_b_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_b_243_, v___x_244_);
v___x_246_ = lean_nat_sub(v_s_238_, v___x_245_);
lean_dec(v___x_245_);
v___x_247_ = lean_nat_dec_eq(v_b_243_, v___x_246_);
lean_dec(v___x_246_);
if (v___x_247_ == 0)
{
lean_dec(v_toOne_241_);
lean_dec(v_toNeg_240_);
lean_inc(v_toZero_239_);
return v_toZero_239_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_apply_1(v_toNeg_240_, v_toOne_241_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__0___boxed(lean_object* v_s_249_, lean_object* v_toZero_250_, lean_object* v_toNeg_251_, lean_object* v_toOne_252_, lean_object* v_x_253_, lean_object* v_b_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = lp_GRH_New_Seesaw_gluedGram___redArg___lam__0(v_s_249_, v_toZero_250_, v_toNeg_251_, v_toOne_252_, v_x_253_, v_b_254_);
lean_dec(v_b_254_);
lean_dec(v_toZero_250_);
lean_dec(v_s_249_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__3(lean_object* v_s_256_, lean_object* v_toOne_257_, lean_object* v_q_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_260_ = lean_unsigned_to_nat(2u);
v___x_261_ = lean_nat_mod(v_s_256_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_dec_eq(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
if (v___x_263_ == 0)
{
lean_inc(v_toOne_257_);
return v_toOne_257_;
}
else
{
lean_inc(v_q_258_);
return v_q_258_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__3___boxed(lean_object* v_s_264_, lean_object* v_toOne_265_, lean_object* v_q_266_, lean_object* v_x_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = lp_GRH_New_Seesaw_gluedGram___redArg___lam__3(v_s_264_, v_toOne_265_, v_q_266_, v_x_267_);
lean_dec(v_q_266_);
lean_dec(v_toOne_265_);
lean_dec(v_s_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__2(lean_object* v_s_269_, lean_object* v_toZero_270_, lean_object* v_toOne_271_, lean_object* v_toNeg_272_, lean_object* v_p_273_, lean_object* v_b_274_, lean_object* v_c_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_c_275_, v___x_276_);
v___x_278_ = lean_nat_sub(v_s_269_, v___x_277_);
lean_dec(v___x_277_);
v___x_279_ = lean_nat_dec_eq(v_b_274_, v___x_278_);
lean_dec(v___x_278_);
if (v___x_279_ == 0)
{
lean_dec(v_p_273_);
lean_dec(v_toNeg_272_);
lean_inc(v_toZero_270_);
return v_toZero_270_;
}
else
{
uint8_t v___x_280_; 
v___x_280_ = lean_nat_dec_eq(v_b_274_, v_c_275_);
if (v___x_280_ == 0)
{
lean_dec(v_p_273_);
lean_dec(v_toNeg_272_);
lean_inc(v_toOne_271_);
return v_toOne_271_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_apply_1(v_toNeg_272_, v_p_273_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__2___boxed(lean_object* v_s_282_, lean_object* v_toZero_283_, lean_object* v_toOne_284_, lean_object* v_toNeg_285_, lean_object* v_p_286_, lean_object* v_b_287_, lean_object* v_c_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_GRH_New_Seesaw_gluedGram___redArg___lam__2(v_s_282_, v_toZero_283_, v_toOne_284_, v_toNeg_285_, v_p_286_, v_b_287_, v_c_288_);
lean_dec(v_c_288_);
lean_dec(v_b_287_);
lean_dec(v_toOne_284_);
lean_dec(v_toZero_283_);
lean_dec(v_s_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__4(lean_object* v___x_290_, lean_object* v___x_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_toFun_294_; lean_object* v___x_295_; 
v_toFun_294_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_toFun_294_);
lean_dec_ref(v___x_290_);
v___x_295_ = lean_apply_3(v_toFun_294_, v___x_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg___lam__5(lean_object* v___x_296_, lean_object* v___f_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_toFun_300_; lean_object* v___x_301_; 
v_toFun_300_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_toFun_300_);
lean_dec_ref(v___x_296_);
v___x_301_ = lean_apply_3(v_toFun_300_, v___f_297_, v___y_298_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram___redArg(lean_object* v_inst_302_, lean_object* v_s_303_, lean_object* v_inst_304_, lean_object* v_p_305_, lean_object* v_q_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_toSemiring_309_; lean_object* v___x_310_; lean_object* v_toZero_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_toNeg_314_; lean_object* v___x_315_; lean_object* v_toAddMonoidWithOne_316_; lean_object* v_toOne_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_C_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___f_330_; lean_object* v___x_331_; 
v_toSemiring_309_ = lean_ctor_get(v_inst_304_, 0);
lean_inc_ref(v_toSemiring_309_);
v___x_310_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_309_);
v_toZero_311_ = lean_ctor_get(v___x_310_, 1);
lean_inc_n(v_toZero_311_, 4);
lean_dec_ref(v___x_310_);
v___x_312_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_304_);
v___x_313_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_312_);
lean_dec_ref(v___x_312_);
v_toNeg_314_ = lean_ctor_get(v___x_313_, 1);
lean_inc_n(v_toNeg_314_, 2);
lean_dec_ref(v___x_313_);
v___x_315_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_304_);
v_toAddMonoidWithOne_316_ = lean_ctor_get(v___x_315_, 1);
lean_inc_ref(v_toAddMonoidWithOne_316_);
lean_dec_ref(v___x_315_);
v_toOne_317_ = lean_ctor_get(v_toAddMonoidWithOne_316_, 2);
lean_inc_n(v_toOne_317_, 4);
lean_dec_ref(v_toAddMonoidWithOne_316_);
v___f_318_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_318_, 0, v_inst_302_);
v___f_319_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_gluedGram___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_319_, 0, v_toZero_311_);
lean_inc_n(v_s_303_, 2);
v___f_320_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_gluedGram___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_320_, 0, v_s_303_);
lean_closure_set(v___f_320_, 1, v_toZero_311_);
lean_closure_set(v___f_320_, 2, v_toNeg_314_);
lean_closure_set(v___f_320_, 3, v_toOne_317_);
v___f_321_ = lean_alloc_closure((void*)(lp_GRH_New_gradedLatticeBasis___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_321_, 0, v_toOne_317_);
v___f_322_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_gluedGram___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_322_, 0, v_s_303_);
lean_closure_set(v___f_322_, 1, v_toOne_317_);
lean_closure_set(v___f_322_, 2, v_q_306_);
v___f_323_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_gluedGram___redArg___lam__2___boxed), 7, 5);
lean_closure_set(v___f_323_, 0, v_s_303_);
lean_closure_set(v___f_323_, 1, v_toZero_311_);
lean_closure_set(v___f_323_, 2, v_toOne_317_);
lean_closure_set(v___f_323_, 3, v_toNeg_314_);
lean_closure_set(v___f_323_, 4, v_p_305_);
v___x_324_ = lean_obj_once(&lp_GRH_New_gradedLatticeBasis___redArg___closed__0, &lp_GRH_New_gradedLatticeBasis___redArg___closed__0_once, _init_lp_GRH_New_gradedLatticeBasis___redArg___closed__0);
v___x_325_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, lean_box(0));
lean_closure_set(v___x_325_, 2, lean_box(0));
lean_closure_set(v___x_325_, 3, v___f_319_);
lean_closure_set(v___x_325_, 4, v___f_320_);
v_C_326_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_gluedGram___redArg___lam__4), 4, 2);
lean_closure_set(v_C_326_, 0, v___x_324_);
lean_closure_set(v_C_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_327_, 0, lean_box(0));
lean_closure_set(v___x_327_, 1, lean_box(0));
lean_closure_set(v___x_327_, 2, lean_box(0));
lean_closure_set(v___x_327_, 3, v___f_321_);
lean_closure_set(v___x_327_, 4, v___f_322_);
v___x_328_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_328_, 0, lean_box(0));
lean_closure_set(v___x_328_, 1, lean_box(0));
lean_closure_set(v___x_328_, 2, v___f_318_);
lean_closure_set(v___x_328_, 3, v_toZero_311_);
lean_closure_set(v___x_328_, 4, v___x_327_);
lean_inc_ref(v_C_326_);
v___x_329_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, lean_box(0));
lean_closure_set(v___x_329_, 2, lean_box(0));
lean_closure_set(v___x_329_, 3, v_C_326_);
v___f_330_ = lean_alloc_closure((void*)(lp_GRH_New_Seesaw_gluedGram___redArg___lam__5), 4, 2);
lean_closure_set(v___f_330_, 0, v___x_324_);
lean_closure_set(v___f_330_, 1, v___f_323_);
v___x_331_ = lp_mathlib_Matrix_fromBlocks___redArg(v___x_328_, v_C_326_, v___x_329_, v___f_330_, v_a_307_, v_a_308_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_gluedGram(lean_object* v_X_332_, lean_object* v_inst_333_, lean_object* v_s_334_, lean_object* v_K_335_, lean_object* v_inst_336_, lean_object* v_p_337_, lean_object* v_q_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lp_GRH_New_Seesaw_gluedGram___redArg(v_inst_333_, v_s_334_, v_inst_336_, v_p_337_, v_q_338_, v_a_339_, v_a_340_);
return v___x_341_;
}
}
static lean_object* _init_lp_GRH_New_Seesaw_stringSign___closed__0(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_lp_GRH_New_Seesaw_stringSign___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&lp_GRH_New_Seesaw_stringSign___closed__0, &lp_GRH_New_Seesaw_stringSign___closed__0_once, _init_lp_GRH_New_Seesaw_stringSign___closed__0);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_lp_GRH_New_Seesaw_stringSign___closed__2(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&lp_GRH_New_Seesaw_stringSign___closed__0, &lp_GRH_New_Seesaw_stringSign___closed__0_once, _init_lp_GRH_New_Seesaw_stringSign___closed__0);
v___x_347_ = lean_int_neg(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_lp_GRH_New_Seesaw_stringSign___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&lp_GRH_New_Seesaw_stringSign___closed__2, &lp_GRH_New_Seesaw_stringSign___closed__2_once, _init_lp_GRH_New_Seesaw_stringSign___closed__2);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_stringSign(lean_object* v_s_350_, lean_object* v_b_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_s_350_, v___x_352_);
v___x_354_ = lean_nat_shiftr(v___x_353_, v___x_352_);
lean_dec(v___x_353_);
v___x_355_ = lean_nat_dec_lt(v_b_351_, v___x_354_);
lean_dec(v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&lp_GRH_New_Seesaw_stringSign___closed__1, &lp_GRH_New_Seesaw_stringSign___closed__1_once, _init_lp_GRH_New_Seesaw_stringSign___closed__1);
return v___x_356_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&lp_GRH_New_Seesaw_stringSign___closed__3, &lp_GRH_New_Seesaw_stringSign___closed__3_once, _init_lp_GRH_New_Seesaw_stringSign___closed__3);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Seesaw_stringSign___boxed(lean_object* v_s_358_, lean_object* v_b_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = lp_GRH_New_Seesaw_stringSign(v_s_358_, v_b_359_);
lean_dec(v_b_359_);
lean_dec(v_s_358_);
return v_res_360_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_PAdicGauge(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_AlgebraicValues(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_TensorChains(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_WeilAction(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Seesaw_AdmissibleCombinations(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_PAdicGauge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_HeckeCharacter_AlgebraicValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_TensorChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_WeilAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
