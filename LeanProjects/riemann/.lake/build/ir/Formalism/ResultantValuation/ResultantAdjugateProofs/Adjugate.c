// Lean compiler output
// Module: Formalism.ResultantValuation.ResultantAdjugateProofs.Adjugate
// Imports: public import Init public meta import Init public import Formalism.ResultantValuation.KoszulSecondDifferential
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_updateCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_updateCol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_single___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_adjugate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorF___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_M_4_, lean_object* v_k_5_, lean_object* v_i_6_, lean_object* v_l_7_, lean_object* v_j_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toSub_11_; lean_object* v_toSemiring_12_; lean_object* v___x_13_; lean_object* v_toMul_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_ref_n(v_inst_1_, 4);
v___x_9_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v___x_10_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_9_);
lean_dec_ref(v___x_9_);
v_toSub_11_ = lean_ctor_get(v___x_10_, 2);
lean_inc(v_toSub_11_);
lean_dec_ref(v___x_10_);
v_toSemiring_12_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_12_);
v___x_13_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_12_);
v_toMul_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_n(v_toMul_14_, 2);
lean_dec_ref(v___x_13_);
lean_inc(v_l_7_);
lean_inc(v_k_5_);
lean_inc_n(v_M_4_, 3);
lean_inc_n(v_inst_2_, 3);
lean_inc_ref_n(v_inst_3_, 3);
v___x_15_ = lp_mathlib_Matrix_adjugate___redArg(v_inst_3_, v_inst_2_, v_inst_1_, v_M_4_, v_k_5_, v_l_7_);
lean_inc(v_j_8_);
lean_inc(v_i_6_);
v___x_16_ = lp_mathlib_Matrix_adjugate___redArg(v_inst_3_, v_inst_2_, v_inst_1_, v_M_4_, v_i_6_, v_j_8_);
v___x_17_ = lean_apply_2(v_toMul_14_, v___x_15_, v___x_16_);
v___x_18_ = lp_mathlib_Matrix_adjugate___redArg(v_inst_3_, v_inst_2_, v_inst_1_, v_M_4_, v_i_6_, v_l_7_);
v___x_19_ = lp_mathlib_Matrix_adjugate___redArg(v_inst_3_, v_inst_2_, v_inst_1_, v_M_4_, v_k_5_, v_j_8_);
v___x_20_ = lean_apply_2(v_toMul_14_, v___x_18_, v___x_19_);
v___x_21_ = lean_apply_2(v_toSub_11_, v___x_17_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorF(lean_object* v_R_22_, lean_object* v_inst_23_, lean_object* v_n_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_M_27_, lean_object* v_k_28_, lean_object* v_i_29_, lean_object* v_l_30_, lean_object* v_j_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorF___redArg(v_inst_23_, v_inst_25_, v_inst_26_, v_M_27_, v_k_28_, v_i_29_, v_l_30_, v_j_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg___lam__0(lean_object* v_toZero_33_, lean_object* v_i_34_){
_start:
{
lean_inc(v_toZero_33_);
return v_toZero_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg___lam__0___boxed(lean_object* v_toZero_35_, lean_object* v_i_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg___lam__0(v_toZero_35_, v_i_36_);
lean_dec(v_i_36_);
lean_dec(v_toZero_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg(lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_M_41_, lean_object* v_k_42_, lean_object* v_i_43_, lean_object* v_l_44_, lean_object* v_j_45_){
_start:
{
lean_object* v_toSemiring_46_; lean_object* v___x_47_; lean_object* v_toZero_48_; lean_object* v___x_49_; lean_object* v_toAddMonoidWithOne_50_; lean_object* v_toOne_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_64__overap_57_; lean_object* v___x_58_; 
v_toSemiring_46_ = lean_ctor_get(v_inst_38_, 0);
lean_inc_ref(v_toSemiring_46_);
v___x_47_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_46_);
v_toZero_48_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_toZero_48_);
lean_dec_ref(v___x_47_);
lean_inc_ref(v_inst_38_);
v___x_49_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_38_);
v_toAddMonoidWithOne_50_ = lean_ctor_get(v___x_49_, 1);
lean_inc_ref(v_toAddMonoidWithOne_50_);
lean_dec_ref(v___x_49_);
v_toOne_51_ = lean_ctor_get(v_toAddMonoidWithOne_50_, 2);
lean_inc_n(v_toOne_51_, 2);
lean_dec_ref(v_toAddMonoidWithOne_50_);
v___f_52_ = lean_alloc_closure((void*)(lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_52_, 0, v_toZero_48_);
lean_inc_ref_n(v_inst_40_, 4);
lean_inc_ref(v___f_52_);
v___x_53_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_53_, 0, lean_box(0));
lean_closure_set(v___x_53_, 1, lean_box(0));
lean_closure_set(v___x_53_, 2, v___f_52_);
lean_closure_set(v___x_53_, 3, v_inst_40_);
lean_closure_set(v___x_53_, 4, v_j_45_);
lean_closure_set(v___x_53_, 5, v_toOne_51_);
v___x_54_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_updateCol), 9, 7);
lean_closure_set(v___x_54_, 0, lean_box(0));
lean_closure_set(v___x_54_, 1, lean_box(0));
lean_closure_set(v___x_54_, 2, lean_box(0));
lean_closure_set(v___x_54_, 3, v_inst_40_);
lean_closure_set(v___x_54_, 4, v_M_41_);
lean_closure_set(v___x_54_, 5, v_i_43_);
lean_closure_set(v___x_54_, 6, v___x_53_);
v___x_55_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_55_, 0, lean_box(0));
lean_closure_set(v___x_55_, 1, lean_box(0));
lean_closure_set(v___x_55_, 2, v___f_52_);
lean_closure_set(v___x_55_, 3, v_inst_40_);
lean_closure_set(v___x_55_, 4, v_l_44_);
lean_closure_set(v___x_55_, 5, v_toOne_51_);
v___x_56_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_updateCol), 9, 7);
lean_closure_set(v___x_56_, 0, lean_box(0));
lean_closure_set(v___x_56_, 1, lean_box(0));
lean_closure_set(v___x_56_, 2, lean_box(0));
lean_closure_set(v___x_56_, 3, v_inst_40_);
lean_closure_set(v___x_56_, 4, v___x_54_);
lean_closure_set(v___x_56_, 5, v_k_42_);
lean_closure_set(v___x_56_, 6, v___x_55_);
v___x_64__overap_57_ = lp_mathlib_Matrix_detRowAlternating___redArg(v_inst_40_, v_inst_39_, v_inst_38_);
v___x_58_ = lean_apply_1(v___x_64__overap_57_, v___x_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ(lean_object* v_R_59_, lean_object* v_inst_60_, lean_object* v_n_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_M_64_, lean_object* v_k_65_, lean_object* v_i_66_, lean_object* v_l_67_, lean_object* v_j_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lp_tree_Formalism_ResultantValuation_AdjugateJacobi_minorQ___redArg(v_inst_60_, v_inst_62_, v_inst_63_, v_M_64_, v_k_65_, v_i_66_, v_l_67_, v_j_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg___lam__0(lean_object* v_toOne_70_, lean_object* v_x_71_){
_start:
{
lean_inc(v_toOne_70_);
return v_toOne_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg___lam__0___boxed(lean_object* v_toOne_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg___lam__0(v_toOne_72_, v_x_73_);
lean_dec(v_x_73_);
lean_dec(v_toOne_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg(lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_k_77_, lean_object* v_i_78_, lean_object* v_u_79_, lean_object* v_v_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_toSemiring_83_; lean_object* v___x_84_; lean_object* v_toZero_85_; lean_object* v___x_86_; lean_object* v_toAddMonoidWithOne_87_; lean_object* v_toOne_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_toSemiring_83_ = lean_ctor_get(v_inst_75_, 0);
lean_inc_ref(v_toSemiring_83_);
v___x_84_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_83_);
v_toZero_85_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_toZero_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_75_);
v_toAddMonoidWithOne_87_ = lean_ctor_get(v___x_86_, 1);
lean_inc_ref(v_toAddMonoidWithOne_87_);
lean_dec_ref(v___x_86_);
v_toOne_88_ = lean_ctor_get(v_toAddMonoidWithOne_87_, 2);
lean_inc(v_toOne_88_);
lean_dec_ref(v_toAddMonoidWithOne_87_);
v___f_89_ = lean_alloc_closure((void*)(lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_89_, 0, v_toOne_88_);
lean_inc_ref_n(v_inst_76_, 2);
v___x_90_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_90_, 0, lean_box(0));
lean_closure_set(v___x_90_, 1, lean_box(0));
lean_closure_set(v___x_90_, 2, v_inst_76_);
lean_closure_set(v___x_90_, 3, v_toZero_85_);
lean_closure_set(v___x_90_, 4, v___f_89_);
v___x_91_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_updateCol), 9, 7);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, lean_box(0));
lean_closure_set(v___x_91_, 2, lean_box(0));
lean_closure_set(v___x_91_, 3, v_inst_76_);
lean_closure_set(v___x_91_, 4, v___x_90_);
lean_closure_set(v___x_91_, 5, v_k_77_);
lean_closure_set(v___x_91_, 6, v_u_79_);
v___x_92_ = lp_mathlib_Matrix_updateCol___redArg(v_inst_76_, v___x_91_, v_i_78_, v_v_80_, v_a_81_, v_a_82_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol(lean_object* v_R_93_, lean_object* v_inst_94_, lean_object* v_n_95_, lean_object* v_inst_96_, lean_object* v_k_97_, lean_object* v_i_98_, lean_object* v_u_99_, lean_object* v_v_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_tree_Formalism_ResultantValuation_AdjugateJacobi_twoCol___redArg(v_inst_94_, v_inst_96_, v_k_97_, v_i_98_, v_u_99_, v_v_100_, v_a_101_, v_a_102_);
return v___x_103_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_KoszulSecondDifferential(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_KoszulSecondDifferential(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
