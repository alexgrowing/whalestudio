// Lean compiler output
// Module: Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms
// Imports: public import Init public meta import Init public import Formalism.MirabolicMackeyTheory.StatementL public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules public import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
lean_object* lp_mathlib_LinearEquiv_smulOfNeZero___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_restrictScalars___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lp_mathlib_LinearEquiv_smulOfNeZero___redArg(v_inst_1_, v_inst_2_, v_a_3_);
v___x_5_ = lp_mathlib_LinearEquiv_restrictScalars___redArg(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___redArg___boxed(lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___redArg(v_inst_6_, v_inst_7_, v_a_8_);
lean_dec_ref(v_inst_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE(lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_Z_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_ha_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___redArg(v_inst_11_, v_inst_14_, v_a_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE___boxed(lean_object* v_K_20_, lean_object* v_inst_21_, lean_object* v_Z_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_ha_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_scE(v_K_20_, v_inst_21_, v_Z_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_a_27_, v_ha_28_);
lean_dec(v_inst_25_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_21_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_StatementL(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_StatementL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
