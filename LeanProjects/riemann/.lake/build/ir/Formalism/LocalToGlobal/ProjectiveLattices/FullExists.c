// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.FullExists
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J___redArg(lean_object* v_T_1_){
_start:
{
lean_object* v_toTop_2_; lean_object* v_cE_3_; lean_object* v_chiW_4_; lean_object* v_x_u2080_5_; lean_object* v_iota_6_; lean_object* v_toCore_7_; lean_object* v___x_8_; 
v_toTop_2_ = lean_ctor_get(v_T_1_, 0);
v_cE_3_ = lean_ctor_get(v_T_1_, 1);
v_chiW_4_ = lean_ctor_get(v_T_1_, 2);
v_x_u2080_5_ = lean_ctor_get(v_T_1_, 3);
v_iota_6_ = lean_ctor_get(v_T_1_, 4);
v_toCore_7_ = lean_ctor_get(v_toTop_2_, 0);
lean_inc(v_iota_6_);
lean_inc_ref(v_x_u2080_5_);
lean_inc_ref(v_chiW_4_);
lean_inc_ref(v_cE_3_);
lean_inc_ref(v_toCore_7_);
v___x_8_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_8_, 0, v_toCore_7_);
lean_ctor_set(v___x_8_, 1, v_cE_3_);
lean_ctor_set(v___x_8_, 2, v_chiW_4_);
lean_ctor_set(v___x_8_, 3, v_x_u2080_5_);
lean_ctor_set(v___x_8_, 4, v_iota_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J___redArg___boxed(lean_object* v_T_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_L2_Pj_Full_J___redArg(v_T_9_);
lean_dec_ref(v_T_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J(lean_object* v_D_11_, lean_object* v_T_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_tree_Formalism_L2_Pj_Full_J___redArg(v_T_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_Full_J___boxed(lean_object* v_D_14_, lean_object* v_T_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_L2_Pj_Full_J(v_D_14_, v_T_15_);
lean_dec_ref(v_T_15_);
lean_dec_ref(v_D_14_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_HasDataCondition(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThClassPins(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ParCanon(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FullExists(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_HasDataCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThClassPins(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ParCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
