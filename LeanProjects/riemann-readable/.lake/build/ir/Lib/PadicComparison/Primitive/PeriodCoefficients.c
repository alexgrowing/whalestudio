// Lean compiler output
// Module: Lib.PadicComparison.Primitive.PeriodCoefficients
// Imports: public import Init public meta import Init public import Lib.Cohomology.TorsionTheories public import Lib.PadicComparison.Descent.AlmostDescent public import Lib.PadicComparison.HodgeTate.GenericFibre public import Lib.PadicHodge.ArtinSchreierSequence
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Variety_PadicTest_nearZeros___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros(lean_object* v_p_5_, lean_object* v_inst_6_, lean_object* v_c_7_, lean_object* v_I_8_, lean_object* v_S_9_, lean_object* v_X_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_00_u03ba_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_PadicTest_nearZeros___boxed(lean_object* v_p_16_, lean_object* v_inst_17_, lean_object* v_c_18_, lean_object* v_I_19_, lean_object* v_S_20_, lean_object* v_X_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_00_u03ba_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_Variety_PadicTest_nearZeros(v_p_16_, v_inst_17_, v_c_18_, v_I_19_, v_S_20_, v_X_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_00_u03ba_25_);
lean_dec_ref(v_00_u03ba_25_);
lean_dec(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_c_18_);
lean_dec(v_p_16_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_TorsionTheories(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_Descent_AlmostDescent(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_HodgeTate_GenericFibre(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_ArtinSchreierSequence(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicComparison_Primitive_PeriodCoefficients(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_TorsionTheories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_Descent_AlmostDescent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_HodgeTate_GenericFibre(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicHodge_ArtinSchreierSequence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
