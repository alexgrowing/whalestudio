// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
// Imports: public import Init public meta import Init public import Mathlib public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff public import Formalism.LocalToGlobal.UnitaryNorms.CharTied public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_Fr_at___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_Fr_at(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_Fr_at___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_Fr_at___redArg(lean_object* v_f_1_){
_start:
{
lean_object* v_P_2_; lean_object* v_W_3_; lean_object* v_mu0_4_; lean_object* v_eta_5_; lean_object* v_chiPsi_6_; lean_object* v_del_7_; lean_object* v_del_x27_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_15_; 
v_P_2_ = lean_ctor_get(v_f_1_, 0);
v_W_3_ = lean_ctor_get(v_f_1_, 1);
v_mu0_4_ = lean_ctor_get(v_f_1_, 2);
v_eta_5_ = lean_ctor_get(v_f_1_, 3);
v_chiPsi_6_ = lean_ctor_get(v_f_1_, 4);
v_del_7_ = lean_ctor_get(v_f_1_, 5);
v_del_x27_8_ = lean_ctor_get(v_f_1_, 6);
v_isSharedCheck_15_ = !lean_is_exclusive(v_f_1_);
if (v_isSharedCheck_15_ == 0)
{
v___x_10_ = v_f_1_;
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_del_x27_8_);
lean_inc(v_del_7_);
lean_inc(v_chiPsi_6_);
lean_inc(v_eta_5_);
lean_inc(v_mu0_4_);
lean_inc(v_W_3_);
lean_inc(v_P_2_);
lean_dec(v_f_1_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
if (v_isShared_11_ == 0)
{
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_P_2_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_W_3_);
lean_ctor_set(v_reuseFailAlloc_14_, 2, v_mu0_4_);
lean_ctor_set(v_reuseFailAlloc_14_, 3, v_eta_5_);
lean_ctor_set(v_reuseFailAlloc_14_, 4, v_chiPsi_6_);
lean_ctor_set(v_reuseFailAlloc_14_, 5, v_del_7_);
lean_ctor_set(v_reuseFailAlloc_14_, 6, v_del_x27_8_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_Fr_at(lean_object* v_X_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_GlobalTheory_Mem_Top_Fr_at___redArg(v_f_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Mem_Top_Fr_at___boxed(lean_object* v_X_19_, lean_object* v_f_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_GlobalTheory_Mem_Top_Fr_at(v_X_19_, v_f_20_);
lean_dec_ref(v_X_19_);
return v_res_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsRationalUnitaryDeterminantMapRationalUnitaryTo(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SpreadLe(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_Foundations_CdScaleTieIff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharTied(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharUniq(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_FixedCoefficientFieldInComplex(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_HeightFunctions_JointQ(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CmQuadraticFormEqAlternatingForm(uint8_t builtin) {
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
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_SetUnipotentTranslate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsRationalUnitaryDeterminantMapRationalUnitaryTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SpreadLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_Foundations_CdScaleTieIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharTied(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_CharUniq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_FixedCoefficientFieldInComplex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_HeightFunctions_JointQ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
