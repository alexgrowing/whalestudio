// Lean compiler output
// Module: New.Spanning.RemainingTerms.FrameCount
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.Basic public import New.Spanning.Unfolding.ReducedPoints
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
lean_object* lp_mathlib_Matrix_conjTranspose___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_00_u03b1_2_, lean_object* v_a_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lp_mathlib_Matrix_conjTranspose___redArg(v_inst_1_, v_00_u03b1_2_, v_a_3_, v_j_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__1(lean_object* v_00_u03b1_6_, lean_object* v_a_7_, lean_object* v_j_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_00_u03b1_6_, v_j_8_, v_a_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__2(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v_j_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_2(v_00_u03b1_10_, v_j_12_, v___y_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__3(lean_object* v_00_u03bc_14_, lean_object* v___y_15_, lean_object* v_j_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_apply_2(v_00_u03bc_14_, v___y_15_, v_j_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__4(lean_object* v_00_u03b1_18_, lean_object* v_00_u03bc_19_, lean_object* v_inst_20_, lean_object* v_toMul_21_, lean_object* v_toAddCommMonoid_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v___f_25_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__2), 3, 2);
lean_closure_set(v___f_25_, 0, v_00_u03b1_18_);
lean_closure_set(v___f_25_, 1, v___y_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__3), 3, 2);
lean_closure_set(v___f_26_, 0, v_00_u03bc_19_);
lean_closure_set(v___f_26_, 1, v___y_23_);
v___x_27_ = lp_mathlib_dotProduct___redArg(v_inst_20_, v_toMul_21_, v_toAddCommMonoid_22_, v___f_26_, v___f_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__4___boxed(lean_object* v_00_u03b1_28_, lean_object* v_00_u03bc_29_, lean_object* v_inst_30_, lean_object* v_toMul_31_, lean_object* v_toAddCommMonoid_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_GRH_New_Filling_skewSolution___redArg___lam__4(v_00_u03b1_28_, v_00_u03bc_29_, v_inst_30_, v_toMul_31_, v_toAddCommMonoid_32_, v___y_33_, v___y_34_);
lean_dec_ref(v_toAddCommMonoid_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__5(lean_object* v_00_u03bc_36_, lean_object* v_j_37_, lean_object* v_j_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_apply_2(v_00_u03bc_36_, v_j_38_, v_j_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__6(lean_object* v_inst_40_, lean_object* v_P_41_, lean_object* v_j_42_, lean_object* v_j_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_mathlib_Matrix_conjTranspose___redArg(v_inst_40_, v_P_41_, v_j_42_, v_j_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__7(lean_object* v_inst_45_, lean_object* v_P_46_, lean_object* v_inst_47_, lean_object* v_toMul_48_, lean_object* v_toAddCommMonoid_49_, lean_object* v___f_50_, lean_object* v_j_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___x_53_; 
v___f_52_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__6), 4, 3);
lean_closure_set(v___f_52_, 0, v_inst_45_);
lean_closure_set(v___f_52_, 1, v_P_46_);
lean_closure_set(v___f_52_, 2, v_j_51_);
v___x_53_ = lp_mathlib_dotProduct___redArg(v_inst_47_, v_toMul_48_, v_toAddCommMonoid_49_, v___f_52_, v___f_50_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__7___boxed(lean_object* v_inst_54_, lean_object* v_P_55_, lean_object* v_inst_56_, lean_object* v_toMul_57_, lean_object* v_toAddCommMonoid_58_, lean_object* v___f_59_, lean_object* v_j_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_GRH_New_Filling_skewSolution___redArg___lam__7(v_inst_54_, v_P_55_, v_inst_56_, v_toMul_57_, v_toAddCommMonoid_58_, v___f_59_, v_j_60_);
lean_dec_ref(v_toAddCommMonoid_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg___lam__8(lean_object* v_00_u03bc_62_, lean_object* v_inst_63_, lean_object* v_P_64_, lean_object* v_inst_65_, lean_object* v_toMul_66_, lean_object* v_toAddCommMonoid_67_, lean_object* v_inst_68_, lean_object* v___f_69_, lean_object* v_j_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; 
v___f_71_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__5), 3, 2);
lean_closure_set(v___f_71_, 0, v_00_u03bc_62_);
lean_closure_set(v___f_71_, 1, v_j_70_);
lean_inc_ref(v_toAddCommMonoid_67_);
lean_inc(v_toMul_66_);
v___f_72_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_72_, 0, v_inst_63_);
lean_closure_set(v___f_72_, 1, v_P_64_);
lean_closure_set(v___f_72_, 2, v_inst_65_);
lean_closure_set(v___f_72_, 3, v_toMul_66_);
lean_closure_set(v___f_72_, 4, v_toAddCommMonoid_67_);
lean_closure_set(v___f_72_, 5, v___f_71_);
v___x_73_ = lp_mathlib_dotProduct___redArg(v_inst_68_, v_toMul_66_, v_toAddCommMonoid_67_, v___f_69_, v___f_72_);
lean_dec_ref(v_toAddCommMonoid_67_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_P_78_, lean_object* v_00_u03bc_79_, lean_object* v_00_u03b1_80_, lean_object* v_00_u03b4_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_toSub_86_; lean_object* v_toSemiring_87_; lean_object* v___x_88_; lean_object* v_toMul_89_; lean_object* v_toAddCommMonoid_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc_ref(v_inst_74_);
v___x_84_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_74_);
v___x_85_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_84_);
lean_dec_ref(v___x_84_);
v_toSub_86_ = lean_ctor_get(v___x_85_, 2);
lean_inc_n(v_toSub_86_, 2);
lean_dec_ref(v___x_85_);
v_toSemiring_87_ = lean_ctor_get(v_inst_74_, 0);
lean_inc_ref_n(v_toSemiring_87_, 2);
lean_dec_ref(v_inst_74_);
v___x_88_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_87_);
v_toMul_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_n(v_toMul_89_, 6);
lean_dec_ref(v___x_88_);
v_toAddCommMonoid_90_ = lean_ctor_get(v_toSemiring_87_, 0);
lean_inc_ref_n(v_toAddCommMonoid_90_, 3);
lean_dec_ref(v_toSemiring_87_);
lean_inc_n(v_a_82_, 2);
lean_inc_n(v_00_u03b1_80_, 3);
lean_inc_n(v_inst_75_, 3);
v___f_91_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__0), 4, 3);
lean_closure_set(v___f_91_, 0, v_inst_75_);
lean_closure_set(v___f_91_, 1, v_00_u03b1_80_);
lean_closure_set(v___f_91_, 2, v_a_82_);
lean_inc_n(v_a_83_, 2);
v___f_92_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__1), 3, 2);
lean_closure_set(v___f_92_, 0, v_00_u03b1_80_);
lean_closure_set(v___f_92_, 1, v_a_83_);
lean_inc(v_00_u03b4_81_);
v___x_93_ = lean_apply_1(v_inst_75_, v_00_u03b4_81_);
lean_inc_n(v_inst_77_, 3);
lean_inc_n(v_00_u03bc_79_, 2);
v___f_94_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_94_, 0, v_00_u03b1_80_);
lean_closure_set(v___f_94_, 1, v_00_u03bc_79_);
lean_closure_set(v___f_94_, 2, v_inst_77_);
lean_closure_set(v___f_94_, 3, v_toMul_89_);
lean_closure_set(v___f_94_, 4, v_toAddCommMonoid_90_);
v___f_95_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_skewSolution___redArg___lam__8), 9, 8);
lean_closure_set(v___f_95_, 0, v_00_u03bc_79_);
lean_closure_set(v___f_95_, 1, v_inst_75_);
lean_closure_set(v___f_95_, 2, v_P_78_);
lean_closure_set(v___f_95_, 3, v_inst_76_);
lean_closure_set(v___f_95_, 4, v_toMul_89_);
lean_closure_set(v___f_95_, 5, v_toAddCommMonoid_90_);
lean_closure_set(v___f_95_, 6, v_inst_77_);
lean_closure_set(v___f_95_, 7, v___f_91_);
v___x_96_ = lp_GRH_New_Filling_skewSolution___redArg___lam__4(v_00_u03b1_80_, v_00_u03bc_79_, v_inst_77_, v_toMul_89_, v_toAddCommMonoid_90_, v_a_82_, v_a_83_);
v___x_97_ = lean_apply_2(v_toMul_89_, v___x_93_, v___x_96_);
v___x_98_ = lp_mathlib_Matrix_conjTranspose___redArg(v_inst_75_, v___f_94_, v_a_82_, v_a_83_);
v___x_99_ = lean_apply_2(v_toMul_89_, v_00_u03b4_81_, v___x_98_);
v___x_100_ = lean_apply_2(v_toSub_86_, v___x_97_, v___x_99_);
v___x_101_ = lp_mathlib_dotProduct___redArg(v_inst_77_, v_toMul_89_, v_toAddCommMonoid_90_, v___f_95_, v___f_92_);
lean_dec_ref(v_toAddCommMonoid_90_);
v___x_102_ = lean_apply_2(v_toSub_86_, v___x_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_skewSolution(lean_object* v_R_103_, lean_object* v_m_104_, lean_object* v_n_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_P_110_, lean_object* v_00_u03bc_111_, lean_object* v_00_u03b1_112_, lean_object* v_00_u03b4_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lp_GRH_New_Filling_skewSolution___redArg(v_inst_106_, v_inst_107_, v_inst_108_, v_inst_109_, v_P_110_, v_00_u03bc_111_, v_00_u03b1_112_, v_00_u03b4_113_, v_a_114_, v_a_115_);
return v___x_116_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_Basic(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_ReducedPoints(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_FrameCount(uint8_t builtin) {
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
res = initialize_GRH_Lib_GLn_SchurModule_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_ReducedPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
