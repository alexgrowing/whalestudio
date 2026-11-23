// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementKT
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
lean_object* lp_mathlib_Complex_instNatCast___lam__0(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_tree_Pi_single___at___00Formalism_REAL_root_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightFunctional___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightFunctional(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightOperator___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightOperator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightOperator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift___redArg(lean_object* v_x_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_3_; 
lean_dec(v_a_2_);
v___x_3_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___f_14_; 
v_head_4_ = lean_ctor_get(v_x_1_, 0);
v_tail_5_ = lean_ctor_get(v_x_1_, 1);
v_fst_6_ = lean_ctor_get(v_head_4_, 0);
v_snd_7_ = lean_ctor_get(v_head_4_, 1);
v___x_8_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_inc_n(v_a_2_, 2);
v___x_9_ = lp_tree_Pi_single___at___00Formalism_REAL_root_spec__0___redArg(v_fst_6_, v___x_8_, v_a_2_);
v___x_10_ = lp_tree_Pi_single___at___00Formalism_REAL_root_spec__0___redArg(v_snd_7_, v___x_8_, v_a_2_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_11_, 0, v___x_10_);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___x_9_);
lean_closure_set(v___f_12_, 1, v___f_11_);
v___x_13_ = lp_tree_Formalism_REAL_wordWeightShift___redArg(v_tail_5_, v_a_2_);
v___f_14_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_14_, 0, v___f_12_);
lean_closure_set(v___f_14_, 1, v___x_13_);
return v___f_14_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift___redArg___boxed(lean_object* v_x_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_REAL_wordWeightShift___redArg(v_x_15_, v_a_16_);
lean_dec(v_x_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift(lean_object* v_m_18_, lean_object* v_x_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_tree_Formalism_REAL_wordWeightShift___redArg(v_x_19_, v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_wordWeightShift___boxed(lean_object* v_m_22_, lean_object* v_x_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_tree_Formalism_REAL_wordWeightShift(v_m_22_, v_x_23_, v_a_24_);
lean_dec(v_x_23_);
lean_dec(v_m_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightFunctional___lam__0(lean_object* v_v_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___f_30_; 
lean_inc(v_a_27_);
v___x_28_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_a_27_);
v___x_29_ = lean_apply_1(v_v_26_, v_a_27_);
v___f_30_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_30_, 0, v___x_28_);
lean_closure_set(v___f_30_, 1, v___x_29_);
return v___f_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightFunctional(lean_object* v_m_31_, lean_object* v_v_32_){
_start:
{
lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_heightFunctional___lam__0), 2, 1);
lean_closure_set(v___f_33_, 0, v_v_32_);
v___x_34_ = l_List_finRange(v_m_31_);
v___x_35_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_34_, v___f_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter___redArg(lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_38_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__1_37_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_head_41_; lean_object* v_tail_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_37_);
v_head_41_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_head_41_);
v_tail_42_ = lean_ctor_get(v_x_36_, 1);
lean_inc(v_tail_42_);
lean_dec_ref_known(v_x_36_, 2);
v___x_43_ = lean_apply_2(v_h__2_38_, v_head_41_, v_tail_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter(lean_object* v_m_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_48_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_47_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_head_51_; lean_object* v_tail_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_47_);
v_head_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_51_);
v_tail_52_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_tail_52_);
lean_dec_ref_known(v_x_46_, 2);
v___x_53_ = lean_apply_2(v_h__2_48_, v_head_51_, v_tail_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter___boxed(lean_object* v_m_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree___private_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight_0__Formalism_REAL_wordWeightShift_match__1_splitter(v_m_54_, v_motive_55_, v_x_56_, v_h__1_57_, v_h__2_58_);
lean_dec(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightOperator___redArg___lam__0(lean_object* v_F_60_, lean_object* v_inst_61_, lean_object* v_a_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
lean_inc_n(v_a_62_, 2);
v___x_64_ = lp_mathlib_Complex_instNatCast___lam__0(v_a_62_);
v___x_65_ = lean_apply_3(v_F_60_, v_a_62_, v_a_62_, v___y_63_);
v___x_66_ = lean_apply_2(v_inst_61_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightOperator___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_n_69_, lean_object* v_F_70_){
_start:
{
lean_object* v_toAddMonoid_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_toAddMonoid_71_ = lean_ctor_get(v_inst_67_, 0);
lean_inc_ref(v_toAddMonoid_71_);
lean_dec_ref(v_inst_67_);
v___f_72_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_heightOperator___redArg___lam__0), 4, 2);
lean_closure_set(v___f_72_, 0, v_F_70_);
lean_closure_set(v___f_72_, 1, v_inst_68_);
v___x_73_ = lp_mathlib_LinearMap_addMonoid___redArg(v_toAddMonoid_71_);
v___x_74_ = l_List_finRange(v_n_69_);
v___x_75_ = lp_mathlib_Finset_sum___redArg(v___x_73_, v___x_74_, v___f_72_);
lean_dec_ref(v___x_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_heightOperator(lean_object* v_V_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_n_79_, lean_object* v_F_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_tree_Formalism_REAL_heightOperator___redArg(v_inst_77_, v_inst_78_, v_n_79_, v_F_80_);
return v___x_81_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementKT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementKT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
