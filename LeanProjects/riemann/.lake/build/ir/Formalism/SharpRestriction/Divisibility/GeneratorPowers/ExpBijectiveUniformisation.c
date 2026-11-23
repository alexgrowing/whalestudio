// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3 public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
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
extern lean_object* lp_mathlib_Int_instAddCommMonoid;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___redArg(lean_object* v_b_1_){
_start:
{
lean_inc_ref(v_b_1_);
return v_b_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___redArg___boxed(lean_object* v_b_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___redArg(v_b_2_);
lean_dec_ref(v_b_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast(lean_object* v_X_4_, lean_object* v_Y_5_, lean_object* v_L_6_, lean_object* v_L_x27_7_, lean_object* v_h_8_, lean_object* v_K_9_, lean_object* v_inst_10_, lean_object* v_00_u03c6_11_, lean_object* v_00_u03b5_12_, lean_object* v_b_13_){
_start:
{
lean_inc_ref(v_b_13_);
return v_b_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast___boxed(lean_object* v_X_14_, lean_object* v_Y_15_, lean_object* v_L_16_, lean_object* v_L_x27_17_, lean_object* v_h_18_, lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_00_u03c6_21_, lean_object* v_00_u03b5_22_, lean_object* v_b_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_genCast(v_X_14_, v_Y_15_, v_L_16_, v_L_x27_17_, v_h_18_, v_K_19_, v_inst_20_, v_00_u03c6_21_, v_00_u03b5_22_, v_b_23_);
lean_dec_ref(v_b_23_);
lean_dec_ref(v_00_u03b5_22_);
lean_dec_ref(v_00_u03c6_21_);
lean_dec(v_inst_20_);
lean_dec_ref(v_L_x27_17_);
lean_dec_ref(v_L_16_);
lean_dec_ref(v_Y_15_);
lean_dec_ref(v_X_14_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___redArg___lam__0(lean_object* v_xe_25_, lean_object* v_x_26_, lean_object* v_Q_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_toFun_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_toFun_29_ = lean_ctor_get(v_xe_25_, 0);
lean_inc(v_toFun_29_);
lean_dec_ref(v_xe_25_);
v___x_30_ = lean_apply_2(v_toFun_29_, v_x_26_, v_i_28_);
v___x_31_ = lean_apply_1(v_Q_27_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___redArg(lean_object* v_n_32_, lean_object* v_xe_33_, lean_object* v_Q_34_, lean_object* v_x_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___redArg___lam__0), 4, 3);
lean_closure_set(v___f_36_, 0, v_xe_33_);
lean_closure_set(v___f_36_, 1, v_x_35_);
lean_closure_set(v___f_36_, 2, v_Q_34_);
v___x_37_ = lp_mathlib_Int_instAddCommMonoid;
v___x_38_ = l_List_finRange(v_n_32_);
v___x_39_ = lp_mathlib_Finset_sum___redArg(v___x_37_, v___x_38_, v___f_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ(lean_object* v_X1_40_, lean_object* v_Xn_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_n_44_, lean_object* v_xe_45_, lean_object* v_Q_46_, lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___redArg(v_n_44_, v_xe_45_, v_Q_46_, v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ___boxed(lean_object* v_X1_49_, lean_object* v_Xn_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_xe_54_, lean_object* v_Q_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpBijectiveUniformisation_sumQ(v_X1_49_, v_Xn_50_, v_inst_51_, v_inst_52_, v_n_53_, v_xe_54_, v_Q_55_, v_x_56_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_57_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpBijectiveUniformisation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF(builtin);
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
