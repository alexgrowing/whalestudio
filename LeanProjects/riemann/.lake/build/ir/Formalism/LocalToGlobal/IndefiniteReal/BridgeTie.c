// Lean compiler output
// Module: Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.IndefiniteReal.Bridge public import Formalism.LocalToGlobal.Divisibility.CoefMod public import Formalism.LocalToGlobal.Divisibility.DefGroup public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
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
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_IndefR_Bridge_hLat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_IndefR_Bridge_hLat_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_IndefR_Bridge_hLat_spec__0(lean_object* v___x_1_, lean_object* v_s_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_IndefR_Bridge_hLat_spec__0___boxed(lean_object* v___x_4_, lean_object* v_s_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Submodule_span___at___00Formalism_IndefR_Bridge_hLat_spec__0(v___x_4_, v_s_5_);
lean_dec_ref(v___x_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat___redArg(lean_object* v_D_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat___redArg___boxed(lean_object* v_D_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_IndefR_Bridge_hLat___redArg(v_D_9_);
lean_dec_ref(v_D_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat(lean_object* v_D_11_, lean_object* v_V_12_, lean_object* v_h_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Bridge_hLat___boxed(lean_object* v_D_15_, lean_object* v_V_16_, lean_object* v_h_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_IndefR_Bridge_hLat(v_D_15_, v_V_16_, v_h_17_);
lean_dec_ref(v_h_17_);
lean_dec_ref(v_V_16_);
lean_dec_ref(v_D_15_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_Bridge(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefMod(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_BridgeTie(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_Bridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_DefGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
