// Lean compiler output
// Module: Lib.Shimura.HeckeTower.HeckeData
// Imports: public import Init public meta import Init public import Lib.General.NumberTheory.ImaginaryQuadraticField public import Lib.Shimura.Uniformisation.AdelicFrames public import Lib.Weil.Unramified.HeckeGL
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Variety_fixedToEigen___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen(lean_object* v_G_5_, lean_object* v_k_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_K_9_, lean_object* v_H_10_, lean_object* v_inst_11_, lean_object* v_00_u03b9_12_, lean_object* v_J_13_, lean_object* v_00_u03c7_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_fixedToEigen___boxed(lean_object* v_G_16_, lean_object* v_k_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_K_20_, lean_object* v_H_21_, lean_object* v_inst_22_, lean_object* v_00_u03b9_23_, lean_object* v_J_24_, lean_object* v_00_u03c7_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Variety_fixedToEigen(v_G_16_, v_k_17_, v_inst_18_, v_inst_19_, v_K_20_, v_H_21_, v_inst_22_, v_00_u03b9_23_, v_J_24_, v_00_u03c7_25_);
lean_dec(v_00_u03c7_25_);
lean_dec(v_00_u03b9_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_AdelicFrames(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_HeckeGL(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_HeckeTower_HeckeData(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_NumberTheory_ImaginaryQuadraticField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_AdelicFrames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Unramified_HeckeGL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
