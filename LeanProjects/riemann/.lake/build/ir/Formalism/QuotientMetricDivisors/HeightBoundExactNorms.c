// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HeightBoundExactNorms
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.Statement public import Formalism.QuotientMetricDivisors.StatementACE public import Formalism.HarderNarasimhan.QuotRealize
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_induction_go___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instSemilatticeInf;
lean_object* lp_mathlib_Finset_inf_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_DivisionValues_chainFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_DivisionValues_chainFun___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_minOver___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_minOver(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__0(lean_object* v_Kj_1_, lean_object* v_j_2_, lean_object* v_f_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_f_3_, v___y_4_);
v___x_6_ = lean_apply_2(v_Kj_1_, v_j_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__1(lean_object* v___y_7_){
_start:
{
lean_inc(v___y_7_);
return v___y_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__1___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__1(v___y_8_);
lean_dec(v___y_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg(lean_object* v_Kj_11_, lean_object* v_i_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___x_15__overap_16_; lean_object* v___x_17_; 
v___f_14_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_chainFun___redArg___lam__0), 4, 1);
lean_closure_set(v___f_14_, 0, v_Kj_11_);
v___f_15_ = ((lean_object*)(lp_tree_Formalism_DivisionValues_chainFun___redArg___closed__0));
v___x_15__overap_16_ = l_Fin_induction_go___redArg(v___f_15_, v___f_14_, v_i_12_);
v___x_17_ = lean_apply_1(v___x_15__overap_16_, v_a_13_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___redArg___boxed(lean_object* v_Kj_18_, lean_object* v_i_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_DivisionValues_chainFun___redArg(v_Kj_18_, v_i_19_, v_a_20_);
lean_dec(v_i_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun(lean_object* v_m_22_, lean_object* v_C_23_, lean_object* v_Kj_24_, lean_object* v_i_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_DivisionValues_chainFun___redArg(v_Kj_24_, v_i_25_, v_a_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainFun___boxed(lean_object* v_m_28_, lean_object* v_C_29_, lean_object* v_Kj_30_, lean_object* v_i_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_Formalism_DivisionValues_chainFun(v_m_28_, v_C_29_, v_Kj_30_, v_i_31_, v_a_32_);
lean_dec(v_i_31_);
lean_dec(v_m_28_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__0(lean_object* v_toOne_34_, lean_object* v_x_35_){
_start:
{
lean_inc(v_toOne_34_);
return v_toOne_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__0___boxed(lean_object* v_toOne_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__0(v_toOne_36_, v_x_37_);
lean_dec(v_x_37_);
lean_dec(v_toOne_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__1(lean_object* v_A_39_, lean_object* v___y_40_, lean_object* v_j_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_apply_2(v_A_39_, v_j_41_, v___y_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__2(lean_object* v_Kj_43_, lean_object* v_j_44_, lean_object* v___y_45_, lean_object* v_j_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_3(v_Kj_43_, v_j_44_, v___y_45_, v_j_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__3(lean_object* v_Kj_48_, lean_object* v_c_49_, lean_object* v_toMul_50_, lean_object* v_toAddCommMonoid_51_, lean_object* v_j_52_, lean_object* v_A_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_56_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__1), 3, 2);
lean_closure_set(v___f_56_, 0, v_A_53_);
lean_closure_set(v___f_56_, 1, v___y_55_);
lean_inc(v_j_52_);
v___f_57_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__2), 4, 3);
lean_closure_set(v___f_57_, 0, v_Kj_48_);
lean_closure_set(v___f_57_, 1, v_j_52_);
lean_closure_set(v___f_57_, 2, v___y_54_);
v___x_58_ = lean_apply_1(v_c_49_, v_j_52_);
v___x_59_ = l_List_finRange(v___x_58_);
v___x_60_ = lp_mathlib_dotProduct___redArg(v___x_59_, v_toMul_50_, v_toAddCommMonoid_51_, v___f_57_, v___f_56_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__3___boxed(lean_object* v_Kj_61_, lean_object* v_c_62_, lean_object* v_toMul_63_, lean_object* v_toAddCommMonoid_64_, lean_object* v_j_65_, lean_object* v_A_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__3(v_Kj_61_, v_c_62_, v_toMul_63_, v_toAddCommMonoid_64_, v_j_65_, v_A_66_, v___y_67_, v___y_68_);
lean_dec_ref(v_toAddCommMonoid_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg(lean_object* v_inst_70_, lean_object* v_m_71_, lean_object* v_c_72_, lean_object* v_Kj_73_, lean_object* v_i_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; lean_object* v_toZero_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_toOne_81_; lean_object* v___x_82_; lean_object* v_toMul_83_; lean_object* v_toAddCommMonoid_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___x_137__overap_94_; lean_object* v___x_95_; 
lean_inc_ref_n(v_inst_70_, 3);
v___x_77_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_inst_70_);
v_toZero_78_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_toZero_78_);
lean_dec_ref(v___x_77_);
v___x_79_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_inst_70_);
v___x_80_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_79_);
v_toOne_81_ = lean_ctor_get(v___x_80_, 2);
lean_inc(v_toOne_81_);
lean_dec_ref(v___x_80_);
v___x_82_ = lp_mathlib_instDistribOfSemiring___redArg(v_inst_70_);
v_toMul_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_toMul_83_);
lean_dec_ref(v___x_82_);
v_toAddCommMonoid_84_ = lean_ctor_get(v_inst_70_, 0);
lean_inc_ref(v_toAddCommMonoid_84_);
lean_dec_ref(v_inst_70_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_m_71_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_nat_mod(v___x_87_, v___x_86_);
lean_dec(v___x_86_);
lean_inc_ref(v_c_72_);
v___x_89_ = lean_apply_1(v_c_72_, v___x_88_);
v___x_90_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_90_, 0, v___x_89_);
v___f_91_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_91_, 0, v_toOne_81_);
v___x_92_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, lean_box(0));
lean_closure_set(v___x_92_, 2, v___x_90_);
lean_closure_set(v___x_92_, 3, v_toZero_78_);
lean_closure_set(v___x_92_, 4, v___f_91_);
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_chainMat___redArg___lam__3___boxed), 8, 4);
lean_closure_set(v___f_93_, 0, v_Kj_73_);
lean_closure_set(v___f_93_, 1, v_c_72_);
lean_closure_set(v___f_93_, 2, v_toMul_83_);
lean_closure_set(v___f_93_, 3, v_toAddCommMonoid_84_);
v___x_137__overap_94_ = l_Fin_induction_go___redArg(v___x_92_, v___f_93_, v_i_74_);
lean_dec_ref(v___x_92_);
v___x_95_ = lean_apply_2(v___x_137__overap_94_, v_a_75_, v_a_76_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___redArg___boxed(lean_object* v_inst_96_, lean_object* v_m_97_, lean_object* v_c_98_, lean_object* v_Kj_99_, lean_object* v_i_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_DivisionValues_chainMat___redArg(v_inst_96_, v_m_97_, v_c_98_, v_Kj_99_, v_i_100_, v_a_101_, v_a_102_);
lean_dec(v_i_100_);
lean_dec(v_m_97_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat(lean_object* v_R_104_, lean_object* v_inst_105_, lean_object* v_m_106_, lean_object* v_c_107_, lean_object* v_Kj_108_, lean_object* v_i_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_tree_Formalism_DivisionValues_chainMat___redArg(v_inst_105_, v_m_106_, v_c_107_, v_Kj_108_, v_i_109_, v_a_110_, v_a_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_chainMat___boxed(lean_object* v_R_113_, lean_object* v_inst_114_, lean_object* v_m_115_, lean_object* v_c_116_, lean_object* v_Kj_117_, lean_object* v_i_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_tree_Formalism_DivisionValues_chainMat(v_R_113_, v_inst_114_, v_m_115_, v_c_116_, v_Kj_117_, v_i_118_, v_a_119_, v_a_120_);
lean_dec(v_i_118_);
lean_dec(v_m_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_minOver___redArg(lean_object* v_inst_122_, lean_object* v_f_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lp_mathlib_Real_instSemilatticeInf;
v___x_125_ = lp_mathlib_Finset_inf_x27___redArg(v___x_124_, v_inst_122_, v_f_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_minOver(lean_object* v_Ix_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_f_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lp_tree_Formalism_DivisionValues_minOver___redArg(v_inst_127_, v_f_129_);
return v___x_130_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_StatementACE(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_QuotRealize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HeightBoundExactNorms(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_StatementACE(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_QuotRealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
