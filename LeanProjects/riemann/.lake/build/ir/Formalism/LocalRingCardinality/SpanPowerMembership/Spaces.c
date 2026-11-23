// Lean compiler output
// Module: Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataSpaces public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement public import Formalism.FockGram.SymGramPosSemidef public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_stdLat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_stdLat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_Examples_u2082_negLast(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_negLast___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg(lean_object* v_inst_1_, uint8_t v_b_2_){
_start:
{
if (v_b_2_ == 0)
{
lean_object* v___x_3_; lean_object* v_toAddMonoidWithOne_4_; lean_object* v_toOne_5_; 
v___x_3_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_4_ = lean_ctor_get(v___x_3_, 1);
lean_inc_ref(v_toAddMonoidWithOne_4_);
lean_dec_ref(v___x_3_);
v_toOne_5_ = lean_ctor_get(v_toAddMonoidWithOne_4_, 2);
lean_inc(v_toOne_5_);
lean_dec_ref(v_toAddMonoidWithOne_4_);
return v_toOne_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toNeg_8_; lean_object* v___x_9_; lean_object* v_toAddMonoidWithOne_10_; lean_object* v_toOne_11_; lean_object* v___x_12_; 
v___x_6_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_1_);
v___x_7_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_6_);
lean_dec_ref(v___x_6_);
v_toNeg_8_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toNeg_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc_ref(v_toAddMonoidWithOne_10_);
lean_dec_ref(v___x_9_);
v_toOne_11_ = lean_ctor_get(v_toAddMonoidWithOne_10_, 2);
lean_inc(v_toOne_11_);
lean_dec_ref(v_toAddMonoidWithOne_10_);
v___x_12_ = lean_apply_1(v_toNeg_8_, v_toOne_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg___boxed(lean_object* v_inst_13_, lean_object* v_b_14_){
_start:
{
uint8_t v_b_boxed_15_; lean_object* v_res_16_; 
v_b_boxed_15_ = lean_unbox(v_b_14_);
v_res_16_ = lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg(v_inst_13_, v_b_boxed_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn(lean_object* v_A_17_, lean_object* v_inst_18_, uint8_t v_b_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg(v_inst_18_, v_b_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___boxed(lean_object* v_A_21_, lean_object* v_inst_22_, lean_object* v_b_23_){
_start:
{
uint8_t v_b_boxed_24_; lean_object* v_res_25_; 
v_b_boxed_24_ = lean_unbox(v_b_23_);
v_res_25_ = lp_tree_Formalism_BasicNotions_Examples_u2082_sgn(v_A_21_, v_inst_22_, v_b_boxed_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__0(lean_object* v_x_26_, lean_object* v_inst_27_, lean_object* v_neg_28_, lean_object* v_toRing_29_, lean_object* v_toMul_30_, lean_object* v_y_31_, lean_object* v_i_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc_n(v_i_32_, 2);
v___x_33_ = lean_apply_1(v_x_26_, v_i_32_);
v___x_34_ = lean_apply_1(v_inst_27_, v___x_33_);
v___x_35_ = lean_apply_1(v_neg_28_, v_i_32_);
v___x_36_ = lean_unbox(v___x_35_);
v___x_37_ = lp_tree_Formalism_BasicNotions_Examples_u2082_sgn___redArg(v_toRing_29_, v___x_36_);
lean_inc(v_toMul_30_);
v___x_38_ = lean_apply_2(v_toMul_30_, v___x_34_, v___x_37_);
v___x_39_ = lean_apply_1(v_y_31_, v_i_32_);
v___x_40_ = lean_apply_2(v_toMul_30_, v___x_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__1(lean_object* v_inst_41_, lean_object* v_neg_42_, lean_object* v_toRing_43_, lean_object* v_toMul_44_, lean_object* v_N_45_, lean_object* v_toAddCommMonoid_46_, lean_object* v_x_47_, lean_object* v_y_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__0), 7, 6);
lean_closure_set(v___f_49_, 0, v_x_47_);
lean_closure_set(v___f_49_, 1, v_inst_41_);
lean_closure_set(v___f_49_, 2, v_neg_42_);
lean_closure_set(v___f_49_, 3, v_toRing_43_);
lean_closure_set(v___f_49_, 4, v_toMul_44_);
lean_closure_set(v___f_49_, 5, v_y_48_);
v___x_50_ = l_List_finRange(v_N_45_);
v___x_51_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_46_, v___x_50_, v___f_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__1___boxed(lean_object* v_inst_52_, lean_object* v_neg_53_, lean_object* v_toRing_54_, lean_object* v_toMul_55_, lean_object* v_N_56_, lean_object* v_toAddCommMonoid_57_, lean_object* v_x_58_, lean_object* v_y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__1(v_inst_52_, v_neg_53_, v_toRing_54_, v_toMul_55_, v_N_56_, v_toAddCommMonoid_57_, v_x_58_, v_y_59_);
lean_dec_ref(v_toAddCommMonoid_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg(lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_N_63_, lean_object* v_neg_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_toSemiring_67_; lean_object* v_toAddCommMonoid_68_; lean_object* v___x_69_; lean_object* v_toMul_70_; lean_object* v___x_71_; lean_object* v_toRing_72_; lean_object* v___f_73_; lean_object* v___f_74_; 
v___x_65_ = lp_mathlib_Field_toSemifield___redArg(v_inst_61_);
v___x_66_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_65_);
v_toSemiring_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_toSemiring_67_);
lean_dec_ref(v___x_66_);
v_toAddCommMonoid_68_ = lean_ctor_get(v_toSemiring_67_, 0);
lean_inc_ref(v_toAddCommMonoid_68_);
v___x_69_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_67_);
v_toMul_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_toMul_70_);
lean_dec_ref(v___x_69_);
v___x_71_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_61_);
v_toRing_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_toRing_72_);
lean_dec_ref(v___x_71_);
v___f_73_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg___lam__1___boxed), 8, 6);
lean_closure_set(v___f_73_, 0, v_inst_62_);
lean_closure_set(v___f_73_, 1, v_neg_64_);
lean_closure_set(v___f_73_, 2, v_toRing_72_);
lean_closure_set(v___f_73_, 3, v_toMul_70_);
lean_closure_set(v___f_73_, 4, v_N_63_);
lean_closure_set(v___f_73_, 5, v_toAddCommMonoid_68_);
v___f_74_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0), 3, 1);
lean_closure_set(v___f_74_, 0, v___f_73_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm(lean_object* v_E_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_N_78_, lean_object* v_neg_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_tree_Formalism_BasicNotions_Examples_u2082_diagForm___redArg(v_inst_76_, v_inst_77_, v_N_78_, v_neg_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_stdLat(lean_object* v_E_81_, lean_object* v_inst_82_, lean_object* v_N_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_stdLat___boxed(lean_object* v_E_85_, lean_object* v_inst_86_, lean_object* v_N_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_tree_Formalism_BasicNotions_Examples_u2082_stdLat(v_E_85_, v_inst_86_, v_N_87_);
lean_dec(v_N_87_);
lean_dec_ref(v_inst_86_);
return v_res_88_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_BasicNotions_Examples_u2082_negLast(lean_object* v_i_89_){
_start:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(8u);
v___x_91_ = lean_nat_dec_eq(v_i_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_negLast___boxed(lean_object* v_i_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = lp_tree_Formalism_BasicNotions_Examples_u2082_negLast(v_i_92_);
lean_dec(v_i_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___lam__0(lean_object* v_n_95_, lean_object* v_toSemiring_96_, lean_object* v_x_97_, lean_object* v_i_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_nat_dec_lt(v_i_98_, v_n_95_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v_toZero_101_; 
lean_dec(v_i_98_);
lean_dec(v_x_97_);
v___x_100_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_96_);
v_toZero_101_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_toZero_101_);
lean_dec_ref(v___x_100_);
return v_toZero_101_;
}
else
{
lean_object* v___x_102_; 
lean_dec_ref(v_toSemiring_96_);
v___x_102_ = lean_apply_1(v_x_97_, v_i_98_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___lam__0___boxed(lean_object* v_n_103_, lean_object* v_toSemiring_104_, lean_object* v_x_105_, lean_object* v_i_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___lam__0(v_n_103_, v_toSemiring_104_, v_x_105_, v_i_106_);
lean_dec(v_n_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg(lean_object* v_inst_108_, lean_object* v_n_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_toSemiring_112_; lean_object* v___f_113_; 
v___x_110_ = lp_mathlib_Field_toSemifield___redArg(v_inst_108_);
v___x_111_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_110_);
v_toSemiring_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_toSemiring_112_);
lean_dec_ref(v___x_111_);
v___f_113_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_113_, 0, v_n_109_);
lean_closure_set(v___f_113_, 1, v_toSemiring_112_);
return v___f_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg___boxed(lean_object* v_inst_114_, lean_object* v_n_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg(v_inst_114_, v_n_115_);
lean_dec_ref(v_inst_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero(lean_object* v_E_117_, lean_object* v_inst_118_, lean_object* v_n_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___redArg(v_inst_118_, v_n_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_extZero___boxed(lean_object* v_E_121_, lean_object* v_inst_122_, lean_object* v_n_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_Formalism_BasicNotions_Examples_u2082_extZero(v_E_121_, v_inst_122_, v_n_123_);
lean_dec_ref(v_inst_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit___redArg(lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_d_127_, lean_object* v_d_x27_128_){
_start:
{
lean_object* v_toSemiring_129_; lean_object* v___x_130_; lean_object* v_toZero_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_140_; 
v_toSemiring_129_ = lean_ctor_get(v_inst_126_, 0);
lean_inc_ref(v_toSemiring_129_);
lean_dec_ref(v_inst_126_);
v___x_130_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_129_);
v_toZero_131_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_130_, 0);
lean_dec(v_unused_141_);
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_140_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_toZero_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_140_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
lean_inc(v_toZero_131_);
lean_inc_ref(v_inst_125_);
v___x_135_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_135_, 0, lean_box(0));
lean_closure_set(v___x_135_, 1, lean_box(0));
lean_closure_set(v___x_135_, 2, v_inst_125_);
lean_closure_set(v___x_135_, 3, v_toZero_131_);
lean_closure_set(v___x_135_, 4, v_d_127_);
v___x_136_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_136_, 0, lean_box(0));
lean_closure_set(v___x_136_, 1, lean_box(0));
lean_closure_set(v___x_136_, 2, v_inst_125_);
lean_closure_set(v___x_136_, 3, v_toZero_131_);
lean_closure_set(v___x_136_, 4, v_d_x27_128_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_136_);
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_138_ = v___x_133_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit(lean_object* v_n_142_, lean_object* v_A_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_d_147_, lean_object* v_d_x27_148_, lean_object* v_h_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit___redArg(v_inst_145_, v_inst_146_, v_d_147_, v_d_x27_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit___boxed(lean_object* v_n_151_, lean_object* v_A_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_d_156_, lean_object* v_d_x27_157_, lean_object* v_h_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = lp_tree_Formalism_BasicNotions_Examples_u2082_diagUnit(v_n_151_, v_A_152_, v_inst_153_, v_inst_154_, v_inst_155_, v_d_156_, v_d_x27_157_, v_h_158_);
lean_dec(v_inst_153_);
return v_res_159_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataSpaces(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement(uint8_t builtin);
lean_object* initialize_tree_Formalism_FockGram_SymGramPosSemidef(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataSpaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FockGram_SymGramPosSemidef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
