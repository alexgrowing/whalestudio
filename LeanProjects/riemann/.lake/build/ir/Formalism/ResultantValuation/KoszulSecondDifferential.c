// Lean compiler output
// Module: Formalism.ResultantValuation.KoszulSecondDifferential
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_prod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___lam__0(lean_object* v___x_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toMul_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_1_);
v_toMul_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_toMul_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_1(v___y_3_, v___y_4_);
v___x_8_ = lean_apply_2(v_toMul_6_, v_x_2_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___lam__1(lean_object* v___x_9_, lean_object* v_y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; lean_object* v_toMul_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_9_);
v_toMul_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_toMul_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lean_apply_1(v___y_11_, v___y_12_);
v___x_16_ = lean_apply_2(v_toMul_14_, v_y_10_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg(lean_object* v_inst_17_, lean_object* v_x_18_, lean_object* v_y_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; 
v___x_20_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_17_);
v___x_21_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_20_);
lean_inc_ref(v___x_21_);
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___lam__0), 4, 2);
lean_closure_set(v___f_22_, 0, v___x_21_);
lean_closure_set(v___f_22_, 1, v_x_18_);
v___f_23_ = lean_alloc_closure((void*)(lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___lam__1), 4, 2);
lean_closure_set(v___f_23_, 0, v___x_21_);
lean_closure_set(v___f_23_, 1, v_y_19_);
v___x_24_ = lp_mathlib_LinearMap_prod___redArg(v___f_22_, v___f_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg___boxed(lean_object* v_inst_25_, lean_object* v_x_26_, lean_object* v_y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg(v_inst_25_, v_x_26_, v_y_27_);
lean_dec_ref(v_inst_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential(lean_object* v_A_29_, lean_object* v_inst_30_, lean_object* v_r_31_, lean_object* v_x_32_, lean_object* v_y_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___redArg(v_inst_30_, v_x_32_, v_y_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulFirstDifferential___boxed(lean_object* v_A_35_, lean_object* v_inst_36_, lean_object* v_r_37_, lean_object* v_x_38_, lean_object* v_y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_ResultantValuation_koszulFirstDifferential(v_A_35_, v_inst_36_, v_r_37_, v_x_38_, v_y_39_);
lean_dec(v_r_37_);
lean_dec_ref(v_inst_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg___lam__0(lean_object* v___x_41_, lean_object* v___x_42_, lean_object* v_y_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_toSub_47_; lean_object* v___x_48_; lean_object* v_toMul_49_; lean_object* v_fst_50_; lean_object* v_snd_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_toSub_47_ = lean_ctor_get(v___x_41_, 2);
lean_inc(v_toSub_47_);
lean_dec_ref(v___x_41_);
v___x_48_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_42_);
v_toMul_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_n(v_toMul_49_, 2);
lean_dec_ref(v___x_48_);
v_fst_50_ = lean_ctor_get(v___y_45_, 0);
lean_inc(v_fst_50_);
v_snd_51_ = lean_ctor_get(v___y_45_, 1);
lean_inc(v_snd_51_);
lean_dec_ref(v___y_45_);
lean_inc(v___y_46_);
v___x_52_ = lean_apply_1(v_fst_50_, v___y_46_);
v___x_53_ = lean_apply_2(v_toMul_49_, v_y_43_, v___x_52_);
v___x_54_ = lean_apply_1(v_snd_51_, v___y_46_);
v___x_55_ = lean_apply_2(v_toMul_49_, v_x_44_, v___x_54_);
v___x_56_ = lean_apply_2(v_toSub_47_, v___x_53_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg(lean_object* v_inst_57_, lean_object* v_x_58_, lean_object* v_y_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___f_63_; 
v___x_60_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_57_);
v___x_61_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_inst_57_);
v___x_62_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_61_);
v___f_63_ = lean_alloc_closure((void*)(lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg___lam__0), 6, 4);
lean_closure_set(v___f_63_, 0, v___x_60_);
lean_closure_set(v___f_63_, 1, v___x_62_);
lean_closure_set(v___f_63_, 2, v_y_59_);
lean_closure_set(v___f_63_, 3, v_x_58_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg___boxed(lean_object* v_inst_64_, lean_object* v_x_65_, lean_object* v_y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg(v_inst_64_, v_x_65_, v_y_66_);
lean_dec_ref(v_inst_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential(lean_object* v_A_68_, lean_object* v_inst_69_, lean_object* v_r_70_, lean_object* v_x_71_, lean_object* v_y_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___redArg(v_inst_69_, v_x_71_, v_y_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_koszulSecondDifferential___boxed(lean_object* v_A_74_, lean_object* v_inst_75_, lean_object* v_r_76_, lean_object* v_x_77_, lean_object* v_y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Formalism_ResultantValuation_koszulSecondDifferential(v_A_74_, v_inst_75_, v_r_76_, v_x_77_, v_y_78_);
lean_dec(v_r_76_);
lean_dec_ref(v_inst_75_);
return v_res_79_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ResultantValuation_KoszulSecondDifferential(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
