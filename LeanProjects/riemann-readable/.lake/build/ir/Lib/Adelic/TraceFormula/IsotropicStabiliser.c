// Lean compiler output
// Module: Lib.Adelic.TraceFormula.IsotropicStabiliser
// Imports: public import Init public meta import Init public import Lib.Adelic.Reduction.FirstMinimumShortBases
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
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_spanStabilizer___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer(lean_object* v_E_5_, lean_object* v_n_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_J_11_, lean_object* v_X_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_spanStabilizer___boxed(lean_object* v_E_14_, lean_object* v_n_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_J_20_, lean_object* v_X_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_spanStabilizer(v_E_14_, v_n_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_inst_19_, v_J_20_, v_X_21_);
lean_dec(v_X_21_);
lean_dec(v_J_20_);
lean_dec(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Reduction_FirstMinimumShortBases(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_TraceFormula_IsotropicStabiliser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Adelic_Reduction_FirstMinimumShortBases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
