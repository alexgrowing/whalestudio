// Lean compiler output
// Module: Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef public import Formalism.LocalRingCardinality.DataTies
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Theta_isoDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Theta_isoDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Theta_isoDef(lean_object* v_n_1_, lean_object* v_M_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_J_5_, lean_object* v_00_u03c0_6_, lean_object* v_S_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Theta_isoDef___boxed(lean_object* v_n_9_, lean_object* v_M_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_J_13_, lean_object* v_00_u03c0_14_, lean_object* v_S_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_L2_Theta_isoDef(v_n_9_, v_M_10_, v_inst_11_, v_inst_12_, v_J_13_, v_00_u03c0_14_, v_S_15_);
lean_dec(v_S_15_);
lean_dec(v_00_u03c0_14_);
lean_dec_ref(v_J_13_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
lean_dec(v_n_9_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_IsAutFunDef(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataTies(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_DefsReal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_BesselHermitianTheta_IsAutFunDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataTies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
