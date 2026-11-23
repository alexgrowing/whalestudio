// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.ClassSumDualLe public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst public import Lemmata.HermitianVanishing.KeyZero
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
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_codRestrict___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_smLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_smLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_invSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_invSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg___lam__0(lean_object* v___x_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toMul_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_1_);
v_toMul_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_toMul_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_1(v___y_3_, v___y_4_);
v___x_8_ = lean_apply_2(v_toMul_6_, v_a_2_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg(lean_object* v_inst_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_toCommRing_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___f_14_; 
v_toCommRing_11_ = lean_ctor_get(v_inst_9_, 0);
v___x_12_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_11_);
v___x_13_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_12_);
v___f_14_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg___lam__0), 4, 2);
lean_closure_set(v___f_14_, 0, v___x_13_);
lean_closure_set(v___f_14_, 1, v_a_10_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg___boxed(lean_object* v_inst_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg(v_inst_15_, v_a_16_);
lean_dec_ref(v_inst_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm(lean_object* v_K_18_, lean_object* v_inst_19_, lean_object* v_D_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___redArg(v_inst_19_, v_a_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm___boxed(lean_object* v_K_23_, lean_object* v_inst_24_, lean_object* v_D_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_sm(v_K_23_, v_inst_24_, v_D_25_, v_a_26_);
lean_dec(v_D_25_);
lean_dec_ref(v_inst_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_smLat(lean_object* v_K_28_, lean_object* v_inst_29_, lean_object* v_D_30_, lean_object* v_a_31_, lean_object* v_A_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_smLat___boxed(lean_object* v_K_34_, lean_object* v_inst_35_, lean_object* v_D_36_, lean_object* v_a_37_, lean_object* v_A_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_smLat(v_K_34_, v_inst_35_, v_D_36_, v_a_37_, v_A_38_);
lean_dec(v_a_37_);
lean_dec(v_D_36_);
lean_dec_ref(v_inst_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_invSub(lean_object* v_K_40_, lean_object* v_inst_41_, lean_object* v_V_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_00_u0393_45_, lean_object* v_inst_46_, lean_object* v_00_u03c1_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_invSub___boxed(lean_object* v_K_49_, lean_object* v_inst_50_, lean_object* v_V_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_00_u0393_54_, lean_object* v_inst_55_, lean_object* v_00_u03c1_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_invSub(v_K_49_, v_inst_50_, v_V_51_, v_inst_52_, v_inst_53_, v_00_u0393_54_, v_inst_55_, v_00_u03c1_56_);
lean_dec(v_00_u03c1_56_);
lean_dec_ref(v_inst_55_);
lean_dec(v_inst_53_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__0(lean_object* v_00_u03c1_58_, lean_object* v_00_u03b4_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_2(v_00_u03c1_58_, v_00_u03b4_59_, v___y_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__1(lean_object* v___x_62_, lean_object* v_inst_63_, lean_object* v___f_64_, lean_object* v_inst_65_, lean_object* v___x_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_356__overap_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_356__overap_68_ = lp_mathlib_Finset_sum___redArg(v___x_62_, v_inst_63_, v___f_64_);
v___x_69_ = lean_apply_1(v___x_356__overap_68_, v___y_67_);
v___x_70_ = lean_apply_2(v_inst_65_, v___x_66_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__1___boxed(lean_object* v___x_71_, lean_object* v_inst_72_, lean_object* v___f_73_, lean_object* v_inst_74_, lean_object* v___x_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__1(v___x_71_, v_inst_72_, v___f_73_, v_inst_74_, v___x_75_, v___y_76_);
lean_dec_ref(v___x_71_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg(lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_00_u03c1_82_){
_start:
{
lean_object* v___x_83_; lean_object* v_toAddMonoid_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_toInv_88_; lean_object* v___x_89_; lean_object* v_toRing_90_; lean_object* v___x_91_; lean_object* v_toAddMonoidWithOne_92_; lean_object* v_toNatCast_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; 
v___x_83_ = lp_mathlib_Field_toSemifield___redArg(v_inst_78_);
v_toAddMonoid_84_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_toAddMonoid_84_);
lean_dec_ref(v_inst_79_);
v___x_85_ = lp_mathlib_Semifield_toCommGroupWithZero___redArg(v___x_83_);
lean_dec_ref(v___x_83_);
v___x_86_ = lp_mathlib_CommGroupWithZero_toDivisionCommMonoid___redArg(v___x_85_);
v___x_87_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v___x_86_);
lean_dec_ref(v___x_86_);
v_toInv_88_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_toInv_88_);
lean_dec_ref(v___x_87_);
v___x_89_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_78_);
v_toRing_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_toRing_90_);
lean_dec_ref(v___x_89_);
v___x_91_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_90_);
v_toAddMonoidWithOne_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_toAddMonoidWithOne_92_);
lean_dec_ref(v___x_91_);
v_toNatCast_93_ = lean_ctor_get(v_toAddMonoidWithOne_92_, 0);
lean_inc(v_toNatCast_93_);
lean_dec_ref(v_toAddMonoidWithOne_92_);
v___f_94_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__0), 3, 1);
lean_closure_set(v___f_94_, 0, v_00_u03c1_82_);
v___x_95_ = l_List_lengthTR___redArg(v_inst_81_);
v___x_96_ = lean_apply_1(v_toNatCast_93_, v___x_95_);
v___x_97_ = lean_apply_1(v_toInv_88_, v___x_96_);
v___x_98_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_84_);
v___f_99_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_99_, 0, v___x_98_);
lean_closure_set(v___f_99_, 1, v_inst_81_);
lean_closure_set(v___f_99_, 2, v___f_94_);
lean_closure_set(v___f_99_, 3, v_inst_80_);
lean_closure_set(v___f_99_, 4, v___x_97_);
v___f_100_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_100_, 0, v___f_99_);
return v___f_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg(lean_object* v_K_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_V_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_00_u0393_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_00_u03c1_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___redArg(v_inst_102_, v_inst_106_, v_inst_107_, v_inst_112_, v_00_u03c1_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg___boxed(lean_object* v_K_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_V_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_00_u0393_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_00_u03c1_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_tree_Formalism_DivisionValues_exponent__index__lattice_avg(v_K_115_, v_inst_116_, v_inst_117_, v_inst_118_, v_V_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_inst_123_, v_00_u0393_124_, v_inst_125_, v_inst_126_, v_00_u03c1_127_);
lean_dec_ref(v_inst_125_);
lean_dec(v_inst_122_);
lean_dec(v_inst_118_);
return v_res_128_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst(uint8_t builtin);
lean_object* initialize_tree_Lemmata_HermitianVanishing_KeyZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_ClassSumDualLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Lemmata_HermitianVanishing_KeyZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
