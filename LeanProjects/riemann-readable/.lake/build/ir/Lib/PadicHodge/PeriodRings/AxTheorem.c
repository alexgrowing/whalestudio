// Lean compiler output
// Module: Lib.PadicHodge.PeriodRings.AxTheorem
// Imports: public import Init public meta import Init public import Lib.ClassField.Places.ProfiniteGalois public import Lib.General.Algebra.AbsIntegrallyClosed public import Lib.General.Algebra.AdicCompletion
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
lean_object* lp_mathlib_Ideal_quotientMap___redArg(lean_object*);
lean_object* lp_mathlib_Perfection_map___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tiltMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tiltMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tiltMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tiltMap___redArg(lean_object* v_f_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lp_mathlib_Ideal_quotientMap___redArg(v_f_1_);
v___x_3_ = lp_mathlib_Perfection_map___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tiltMap(lean_object* v_p_4_, lean_object* v_inst_5_, lean_object* v_R_6_, lean_object* v_R_x27_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_f_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_GRH_New_Variety_tiltMap___redArg(v_f_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tiltMap___boxed(lean_object* v_p_14_, lean_object* v_inst_15_, lean_object* v_R_16_, lean_object* v_R_x27_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_f_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_Variety_tiltMap(v_p_14_, v_inst_15_, v_R_16_, v_R_x27_17_, v_inst_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_f_22_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
lean_dec(v_p_14_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Places_ProfiniteGalois(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_AbsIntegrallyClosed(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_AdicCompletion(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicHodge_PeriodRings_AxTheorem(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_Places_ProfiniteGalois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_AbsIntegrallyClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_AdicCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
