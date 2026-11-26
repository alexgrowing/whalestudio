// Lean compiler output
// Module: Lib.GaloisRep.Pseudocharacter.Pseudorepresentations
// Imports: public import Init public meta import Init public import Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations public import Lib.General.NumberTheory.PadicLimitsValuation
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
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_uniformClosure___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure(lean_object* v_K_5_, lean_object* v_00_u03b9_6_, lean_object* v_inst_7_, lean_object* v_S_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_uniformClosure___boxed(lean_object* v_K_10_, lean_object* v_00_u03b9_11_, lean_object* v_inst_12_, lean_object* v_S_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_uniformClosure(v_K_10_, v_00_u03b9_11_, v_inst_12_, v_S_13_);
lean_dec_ref(v_inst_12_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GaloisRep_Pseudocharacter_SemisimpleRepresentations(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_PadicLimitsValuation(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_Pseudocharacter_Pseudorepresentations(uint8_t builtin) {
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
res = initialize_GRH_Lib_GaloisRep_Pseudocharacter_SemisimpleRepresentations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_PadicLimitsValuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
