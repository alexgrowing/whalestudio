// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.UnFree
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt public import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC___redArg(lean_object* v_z_1_){
_start:
{
lean_inc_ref(v_z_1_);
return v_z_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC___redArg___boxed(lean_object* v_z_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_tree_Formalism_L2_PjFree_toC___redArg(v_z_2_);
lean_dec_ref(v_z_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC(lean_object* v_K_4_, lean_object* v_inst_5_, lean_object* v_00_u03c3_6_, lean_object* v_z_7_){
_start:
{
lean_inc_ref(v_z_7_);
return v_z_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_PjFree_toC___boxed(lean_object* v_K_8_, lean_object* v_inst_9_, lean_object* v_00_u03c3_10_, lean_object* v_z_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_PjFree_toC(v_K_8_, v_inst_9_, v_00_u03c3_10_, v_z_11_);
lean_dec_ref(v_z_11_);
lean_dec_ref(v_00_u03c3_10_);
lean_dec_ref(v_inst_9_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_JFDFree(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnFree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_JFDFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
