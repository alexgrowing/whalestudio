// Lean compiler output
// Module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.DataArith public import Formalism.FilteredPoleLength.LocalDescentLevels.InvFromBlocksApplyZero public import Formalism.PeriodIntegrals.Transference public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima public import Formalism.SharpRestriction.Divisibility.WeightAlgebra public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairedCharacterCondition
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___redArg___lam__0(lean_object* v_Hm_1_, lean_object* v_f_2_, lean_object* v___y_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; 
v_fst_4_ = lean_ctor_get(v___y_3_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v___y_3_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v___y_3_);
v___x_6_ = lean_apply_3(v_Hm_1_, v_fst_4_, v_f_2_, v_snd_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___redArg(lean_object* v_Hm_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___redArg___lam__0), 3, 1);
lean_closure_set(v___f_8_, 0, v_Hm_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota(lean_object* v_K_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_V_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_N2_15_, lean_object* v_dH_16_, lean_object* v_Hm_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___redArg___lam__0), 3, 1);
lean_closure_set(v___f_18_, 0, v_Hm_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota___boxed(lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_V_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_N2_25_, lean_object* v_dH_26_, lean_object* v_Hm_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__iota(v_K_19_, v_inst_20_, v_inst_21_, v_V_22_, v_inst_23_, v_inst_24_, v_N2_25_, v_dH_26_, v_Hm_27_);
lean_dec(v_dH_26_);
lean_dec(v_N2_25_);
lean_dec(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_20_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___redArg___lam__0(lean_object* v_00_u03c3_29_, lean_object* v_y_30_, lean_object* v_i_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v_00_u03c3_29_);
lean_ctor_set(v___x_32_, 1, v_i_31_);
v___x_33_ = lean_apply_1(v_y_30_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___redArg(lean_object* v_y_34_, lean_object* v_00_u03c3_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_36_, 0, v_00_u03c3_35_);
lean_closure_set(v___f_36_, 1, v_y_34_);
return v___f_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp(lean_object* v_K_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_dH_40_, lean_object* v_y_41_, lean_object* v_00_u03c3_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_43_, 0, v_00_u03c3_42_);
lean_closure_set(v___f_43_, 1, v_y_41_);
return v___f_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp___boxed(lean_object* v_K_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_dH_47_, lean_object* v_y_48_, lean_object* v_00_u03c3_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_tr__comp(v_K_44_, v_inst_45_, v_inst_46_, v_dH_47_, v_y_48_, v_00_u03c3_49_);
lean_dec(v_dH_47_);
lean_dec_ref(v_inst_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg(lean_object* v_add_51_, lean_object* v_wL_52_, lean_object* v_w_u03b8_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_zero_55_; uint8_t v_isZero_56_; 
v_zero_55_ = lean_unsigned_to_nat(0u);
v_isZero_56_ = lean_nat_dec_eq(v_x_54_, v_zero_55_);
if (v_isZero_56_ == 1)
{
lean_dec(v_wL_52_);
lean_dec(v_add_51_);
lean_inc(v_w_u03b8_53_);
return v_w_u03b8_53_;
}
else
{
lean_object* v_one_57_; lean_object* v_n_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_one_57_ = lean_unsigned_to_nat(1u);
v_n_58_ = lean_nat_sub(v_x_54_, v_one_57_);
lean_inc(v_wL_52_);
lean_inc(v_add_51_);
v___x_59_ = lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg(v_add_51_, v_wL_52_, v_w_u03b8_53_, v_n_58_);
lean_dec(v_n_58_);
v___x_60_ = lean_apply_2(v_add_51_, v_wL_52_, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg___boxed(lean_object* v_add_61_, lean_object* v_wL_62_, lean_object* v_w_u03b8_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg(v_add_61_, v_wL_62_, v_w_u03b8_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_w_u03b8_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter(lean_object* v_W_66_, lean_object* v_add_67_, lean_object* v_wL_68_, lean_object* v_w_u03b8_69_, lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___redArg(v_add_67_, v_wL_68_, v_w_u03b8_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter___boxed(lean_object* v_W_72_, lean_object* v_add_73_, lean_object* v_wL_74_, lean_object* v_w_u03b8_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter(v_W_72_, v_add_73_, v_wL_74_, v_w_u03b8_75_, v_x_76_);
lean_dec(v_x_76_);
lean_dec(v_w_u03b8_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___redArg(lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v_zero_81_; uint8_t v_isZero_82_; 
v_zero_81_ = lean_unsigned_to_nat(0u);
v_isZero_82_ = lean_nat_dec_eq(v_x_78_, v_zero_81_);
if (v_isZero_82_ == 1)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_h__2_80_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_apply_1(v_h__1_79_, v___x_83_);
return v___x_84_;
}
else
{
lean_object* v_one_85_; lean_object* v_n_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_79_);
v_one_85_ = lean_unsigned_to_nat(1u);
v_n_86_ = lean_nat_sub(v_x_78_, v_one_85_);
v___x_87_ = lean_apply_1(v_h__2_80_, v_n_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___redArg___boxed(lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___redArg(v_x_88_, v_h__1_89_, v_h__2_90_);
lean_dec(v_x_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter(lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_){
_start:
{
lean_object* v_zero_96_; uint8_t v_isZero_97_; 
v_zero_96_ = lean_unsigned_to_nat(0u);
v_isZero_97_ = lean_nat_dec_eq(v_x_93_, v_zero_96_);
if (v_isZero_97_ == 1)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_h__2_95_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_apply_1(v_h__1_94_, v___x_98_);
return v___x_99_;
}
else
{
lean_object* v_one_100_; lean_object* v_n_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_94_);
v_one_100_ = lean_unsigned_to_nat(1u);
v_n_101_ = lean_nat_sub(v_x_93_, v_one_100_);
v___x_102_ = lean_apply_1(v_h__2_95_, v_n_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter___boxed(lean_object* v_motive_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_tree___private_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit_0__Formalism_MainNotions_Gaps_SizeBoundsAlt_wtIter_match__1_splitter(v_motive_103_, v_x_104_, v_h__1_105_, v_h__2_106_);
lean_dec(v_x_104_);
return v_res_107_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataArith(uint8_t builtin);
lean_object* initialize_tree_Formalism_FilteredPoleLength_LocalDescentLevels_InvFromBlocksApplyZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_Transference(uint8_t builtin);
lean_object* initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PairedCharacterCondition(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LogSupSumLeOfNonvanishingDetLimit(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataArith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FilteredPoleLength_LocalDescentLevels_InvFromBlocksApplyZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_Transference(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PairedCharacterCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
