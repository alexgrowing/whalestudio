// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB___redArg(lean_object* v_G_1_, lean_object* v_A_2_, lean_object* v_ph1_3_, lean_object* v_ph2_4_, lean_object* v_sy_5_, lean_object* v_ad_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_7_, 0, v_G_1_);
lean_ctor_set(v___x_7_, 1, v_A_2_);
lean_ctor_set(v___x_7_, 2, v_ph1_3_);
lean_ctor_set(v___x_7_, 3, v_ph2_4_);
lean_ctor_set(v___x_7_, 4, v_sy_5_);
lean_ctor_set(v___x_7_, 5, v_ad_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB(lean_object* v_R_8_, lean_object* v_inst_9_, lean_object* v_d_10_, lean_object* v_O_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_G_14_, lean_object* v_A_15_, lean_object* v_ph1_16_, lean_object* v_ph2_17_, lean_object* v_sy_18_, lean_object* v_ad_19_, lean_object* v_ha_20_, lean_object* v_hr_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_22_, 0, v_G_14_);
lean_ctor_set(v___x_22_, 1, v_A_15_);
lean_ctor_set(v___x_22_, 2, v_ph1_16_);
lean_ctor_set(v___x_22_, 3, v_ph2_17_);
lean_ctor_set(v___x_22_, 4, v_sy_18_);
lean_ctor_set(v___x_22_, 5, v_ad_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB___boxed(lean_object* v_R_23_, lean_object* v_inst_24_, lean_object* v_d_25_, lean_object* v_O_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_G_29_, lean_object* v_A_30_, lean_object* v_ph1_31_, lean_object* v_ph2_32_, lean_object* v_sy_33_, lean_object* v_ad_34_, lean_object* v_ha_35_, lean_object* v_hr_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_mkFB(v_R_23_, v_inst_24_, v_d_25_, v_O_26_, v_inst_27_, v_inst_28_, v_G_29_, v_A_30_, v_ph1_31_, v_ph2_32_, v_sy_33_, v_ad_34_, v_ha_35_, v_hr_36_);
lean_dec(v_inst_28_);
lean_dec_ref(v_inst_27_);
lean_dec(v_d_25_);
lean_dec_ref(v_inst_24_);
return v_res_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
