// Lean compiler output
// Module: New.Determinant.Exchange.ConeImage
// Imports: public import Init public meta import Init public import Lib.Adelic.Witt.SmoothWitt public import Lib.SiegelWeil.Tower.LargeSideConstantTerm public import Lib.Weil.MixedModel.TargetZeroTerm
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
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_maxCompactInf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_maxCompactInf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_maxCompactInf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_maxCompactInf___redArg(lean_object* v_00_u03ba_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v___x_4_; 
v_fst_3_ = lean_ctor_get(v_00_u03ba_1_, 0);
lean_inc(v_fst_3_);
lean_dec_ref(v_00_u03ba_1_);
v___x_4_ = lean_apply_1(v_fst_3_, v_a_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_maxCompactInf(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_r_x27_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_t_x27_11_, lean_object* v_00_u03ba_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_fst_14_; lean_object* v___x_15_; 
v_fst_14_ = lean_ctor_get(v_00_u03ba_12_, 0);
lean_inc(v_fst_14_);
lean_dec_ref(v_00_u03ba_12_);
v___x_15_ = lean_apply_1(v_fst_14_, v_a_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_maxCompactInf___boxed(lean_object* v_E_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_r_x27_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_t_x27_22_, lean_object* v_00_u03ba_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_Exchange_maxCompactInf(v_E_16_, v_inst_17_, v_inst_18_, v_r_x27_19_, v_inst_20_, v_inst_21_, v_t_x27_22_, v_00_u03ba_23_, v_a_24_);
lean_dec_ref(v_t_x27_22_);
lean_dec_ref(v_inst_21_);
lean_dec(v_inst_20_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Witt_SmoothWitt(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_LargeSideConstantTerm(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_MixedModel_TargetZeroTerm(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_Exchange_ConeImage(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Witt_SmoothWitt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_Tower_LargeSideConstantTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_MixedModel_TargetZeroTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
