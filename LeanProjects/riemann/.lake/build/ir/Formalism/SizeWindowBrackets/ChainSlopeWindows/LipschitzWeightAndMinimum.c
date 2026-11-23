// Lean compiler output
// Module: Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis public import Formalism.SizeWindowBrackets.ChainSlopeWindows.RiemannHypothesisOfPowerBound public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible public import Formalism.ThickAverageLoss.ThickAverageProofs.Balance public import Formalism.ThickAverageLoss.ThickAverageProofs.ThickAverage public import Formalism.ZetaNonvanishing.GzLipschitz public import Mathlib.NumberTheory.Chebyshev
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
uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_T2_3_, lean_object* v_b_4_, lean_object* v_w_5_, lean_object* v_u0_6_, lean_object* v_j_7_, lean_object* v_00_u03c1_8_){
_start:
{
uint8_t v___x_9_; 
lean_inc_ref(v_00_u03c1_8_);
lean_inc(v_u0_6_);
v___x_9_ = lp_tree_Formalism_D5_instDecidablePredProdE0IsThickAt___aux__1___redArg(v_inst_1_, v_inst_2_, v_T2_3_, v_u0_6_, v_00_u03c1_8_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lp_tree_Formalism_D5_instDecidablePredProdE0InPhi___aux__1___redArg(v_00_u03c1_8_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec_ref(v_00_u03c1_8_);
lean_dec(v_j_7_);
lean_dec(v_u0_6_);
lean_dec(v_w_5_);
v___x_11_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_3(v_w_5_, v_u0_6_, v_j_7_, v_00_u03c1_8_);
return v___x_12_;
}
}
else
{
lean_dec_ref(v_00_u03c1_8_);
lean_dec(v_j_7_);
lean_dec(v_u0_6_);
lean_dec(v_w_5_);
lean_inc(v_b_4_);
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___redArg___boxed(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_T2_15_, lean_object* v_b_16_, lean_object* v_w_17_, lean_object* v_u0_18_, lean_object* v_j_19_, lean_object* v_00_u03c1_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___redArg(v_inst_13_, v_inst_14_, v_T2_15_, v_b_16_, v_w_17_, v_u0_18_, v_j_19_, v_00_u03c1_20_);
lean_dec(v_b_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR(lean_object* v_H_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_m_25_, lean_object* v_T2_26_, lean_object* v_b_27_, lean_object* v_w_28_, lean_object* v_u0_29_, lean_object* v_j_30_, lean_object* v_00_u03c1_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___redArg(v_inst_23_, v_inst_24_, v_T2_26_, v_b_27_, v_w_28_, v_u0_29_, v_j_30_, v_00_u03c1_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___boxed(lean_object* v_H_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_m_36_, lean_object* v_T2_37_, lean_object* v_b_38_, lean_object* v_w_39_, lean_object* v_u0_40_, lean_object* v_j_41_, lean_object* v_00_u03c1_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR(v_H_33_, v_inst_34_, v_inst_35_, v_m_36_, v_T2_37_, v_b_38_, v_w_39_, v_u0_40_, v_j_41_, v_00_u03c1_42_);
lean_dec(v_b_38_);
lean_dec(v_m_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR___redArg(lean_object* v_inst_44_, lean_object* v_TT_45_, lean_object* v_a_46_, lean_object* v_t_47_){
_start:
{
uint8_t v___x_48_; 
lean_inc(v_t_47_);
v___x_48_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v_inst_44_, v_t_47_, v_TT_45_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
lean_dec(v_t_47_);
lean_dec(v_a_46_);
v___x_49_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
v___x_50_ = lean_apply_1(v_a_46_, v_t_47_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR(lean_object* v_H_51_, lean_object* v_inst_52_, lean_object* v_TT_53_, lean_object* v_a_54_, lean_object* v_t_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR___redArg(v_inst_52_, v_TT_53_, v_a_54_, v_t_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg___lam__0(lean_object* v_b_57_, lean_object* v_x_58_){
_start:
{
lean_inc(v_b_57_);
return v_b_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg___lam__0___boxed(lean_object* v_b_59_, lean_object* v_x_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg___lam__0(v_b_59_, v_x_60_);
lean_dec(v_x_60_);
lean_dec(v_b_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_m_64_, lean_object* v_TT_65_, lean_object* v_T2_66_, lean_object* v_a_67_, lean_object* v_b_68_, lean_object* v_w_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_inc(v_b_68_);
v___f_70_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_70_, 0, v_b_68_);
lean_inc(v_TT_65_);
lean_inc_ref(v_inst_63_);
v___x_71_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR), 5, 4);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, v_inst_63_);
lean_closure_set(v___x_71_, 2, v_TT_65_);
lean_closure_set(v___x_71_, 3, v_a_67_);
lean_inc(v_T2_66_);
v___x_72_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR___boxed), 10, 7);
lean_closure_set(v___x_72_, 0, lean_box(0));
lean_closure_set(v___x_72_, 1, v_inst_62_);
lean_closure_set(v___x_72_, 2, v_inst_63_);
lean_closure_set(v___x_72_, 3, v_m_64_);
lean_closure_set(v___x_72_, 4, v_T2_66_);
lean_closure_set(v___x_72_, 5, v_b_68_);
lean_closure_set(v___x_72_, 6, v_w_69_);
v___x_73_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_73_, 0, v_TT_65_);
lean_ctor_set(v___x_73_, 1, v_T2_66_);
lean_ctor_set(v___x_73_, 2, v___x_71_);
lean_ctor_set(v___x_73_, 3, v___f_70_);
lean_ctor_set(v___x_73_, 4, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes(lean_object* v_H_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_m_78_, lean_object* v_TT_79_, lean_object* v_T2_80_, lean_object* v_a_81_, lean_object* v_b_82_, lean_object* v_w_83_, lean_object* v_hb_84_, lean_object* v_ha_85_, lean_object* v_hw_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___redArg(v_inst_75_, v_inst_77_, v_m_78_, v_TT_79_, v_T2_80_, v_a_81_, v_b_82_, v_w_83_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes___boxed(lean_object* v_H_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_m_92_, lean_object* v_TT_93_, lean_object* v_T2_94_, lean_object* v_a_95_, lean_object* v_b_96_, lean_object* v_w_97_, lean_object* v_hb_98_, lean_object* v_ha_99_, lean_object* v_hw_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_nodes(v_H_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_m_92_, v_TT_93_, v_T2_94_, v_a_95_, v_b_96_, v_w_97_, v_hb_98_, v_ha_99_, v_hw_100_);
lean_dec(v_inst_90_);
return v_res_101_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThickAverageLoss_ThickAverageProofs_Balance(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage(uint8_t builtin);
lean_object* initialize_tree_Formalism_ZetaNonvanishing_GzLipschitz(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_Chebyshev(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThickAverageLoss_ThickAverageProofs_Balance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ZetaNonvanishing_GzLipschitz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_Chebyshev(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
