// Lean compiler output
// Module: Lib.SiegelWeil.OneVector.FinitePlaceDensity
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bruhat.FloorMeasures public import Lib.SiegelWeil.Mass
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
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v_O_2_; 
v_O_2_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_O_2_);
return v_O_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers___redArg___boxed(lean_object* v_inst_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Floors_IntegralPlace_integers___redArg(v_inst_3_);
lean_dec_ref(v_inst_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers(lean_object* v_A_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v_O_9_; 
v_O_9_ = lean_ctor_get(v_inst_6_, 3);
lean_inc(v_O_9_);
return v_O_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_IntegralPlace_integers___boxed(lean_object* v_A_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Floors_IntegralPlace_integers(v_A_10_, v_inst_11_, v_inst_12_, v_inst_13_);
lean_dec_ref(v_inst_13_);
lean_dec(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Mass(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_SiegelWeil_OneVector_FinitePlaceDensity(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_Mass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
