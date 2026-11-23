// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix___closed__0;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix(lean_object*, lean_object*);
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_mod(v___x_2_, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix(lean_object* v_D_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_host_6_; lean_object* v_g_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_host_6_ = lean_ctor_get(v_D_4_, 1);
lean_inc_ref(v_host_6_);
lean_dec_ref(v_D_4_);
v_g_7_ = lean_ctor_get(v_host_6_, 6);
lean_inc_ref_n(v_g_7_, 2);
lean_dec_ref(v_host_6_);
lean_inc(v_i_5_);
v___x_8_ = lean_apply_1(v_g_7_, v_i_5_);
v___x_9_ = lean_unsigned_to_nat(2u);
v___x_10_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_PullbackSections_kMix___closed__0);
v___x_11_ = l_Fin_sub(v___x_9_, v___x_10_, v_i_5_);
lean_dec(v_i_5_);
v___x_12_ = lean_apply_1(v_g_7_, v___x_11_);
v___x_13_ = lean_nat_pow(v___x_12_, v___x_9_);
lean_dec(v___x_12_);
v___x_14_ = lean_nat_mul(v___x_8_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_8_);
return v___x_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceBoundSplitOfIntegral(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_ChartValueIntegralGood(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IsMixedOver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceBoundSplitOfIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_ChartValueIntegralGood(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
