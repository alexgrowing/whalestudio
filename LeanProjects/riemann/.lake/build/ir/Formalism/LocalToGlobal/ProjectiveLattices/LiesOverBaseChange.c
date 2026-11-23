// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_lamOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_lamOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_lamOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_lamOf___redArg(lean_object* v_la_1_){
_start:
{
return v_la_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_lamOf(lean_object* v_E_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_H_6_, lean_object* v_l_7_, lean_object* v_c_8_, lean_object* v_la_9_){
_start:
{
return v_la_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_lamOf___boxed(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_H_14_, lean_object* v_l_15_, lean_object* v_c_16_, lean_object* v_la_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Pj_lamOf(v_E_10_, v_inst_11_, v_inst_12_, v_inst_13_, v_H_14_, v_l_15_, v_c_16_, v_la_17_);
lean_dec_ref(v_l_15_);
lean_dec_ref(v_H_14_);
lean_dec_ref(v_inst_11_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_LatPAddRight(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_LiesOverBaseChange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_LatPAddRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
