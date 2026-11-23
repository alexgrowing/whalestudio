// Lean compiler output
// Module: Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
// Imports: public import Init public meta import Init public import Mathlib public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
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
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_hcharSub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_hcharSub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_upF___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_upF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_upF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_hcharSub(lean_object* v_L_1_, lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_hcharSub___boxed(lean_object* v_L_5_, lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_Formalism_L2_Host_hcharSub(v_L_5_, v_inst_6_, v_inst_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_upF___redArg(lean_object* v_inst_9_){
_start:
{
lean_object* v_algebraMap_10_; lean_object* v___f_11_; 
v_algebraMap_10_ = lean_ctor_get(v_inst_9_, 1);
lean_inc(v_algebraMap_10_);
lean_dec_ref(v_inst_9_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_algebraMap_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_upF(lean_object* v_L_12_, lean_object* v_inst_13_, lean_object* v_F_14_, lean_object* v_inst_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_L2_Host_upF___redArg(v_inst_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Host_upF___boxed(lean_object* v_L_18_, lean_object* v_inst_19_, lean_object* v_F_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_L2_Host_upF(v_L_18_, v_inst_19_, v_F_20_, v_inst_21_, v_inst_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_19_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf(uint8_t builtin) {
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
res = initialize_tree_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
