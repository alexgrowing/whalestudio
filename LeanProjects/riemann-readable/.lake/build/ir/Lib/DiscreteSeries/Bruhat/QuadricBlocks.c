// Lean compiler output
// Module: Lib.DiscreteSeries.Bruhat.QuadricBlocks
// Imports: public import Init public meta import Init public import Mathlib.Probability.Kernel.Composition.MeasureCompProd public import Lib.DiscreteSeries.Bruhat.FloorGroups public import Lib.General.Measure.QuadricDisintegration
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_quadricIndex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_quadricIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_quadricIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_quadricIndex___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_P_3_, lean_object* v_r_4_){
_start:
{
lean_object* v_toSemiring_5_; lean_object* v___x_6_; lean_object* v_skewUnit_7_; lean_object* v_toMul_8_; lean_object* v_toTraceOne_9_; lean_object* v_val_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toSub_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_toSemiring_5_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_5_);
v___x_6_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_5_);
v_skewUnit_7_ = lean_ctor_get(v_P_3_, 1);
lean_inc_ref(v_skewUnit_7_);
v_toMul_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc_n(v_toMul_8_, 2);
lean_dec_ref(v___x_6_);
v_toTraceOne_9_ = lean_ctor_get(v_P_3_, 0);
lean_inc(v_toTraceOne_9_);
lean_dec_ref(v_P_3_);
v_val_10_ = lean_ctor_get(v_skewUnit_7_, 0);
lean_inc(v_val_10_);
lean_dec_ref(v_skewUnit_7_);
v___x_11_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v___x_12_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_11_);
lean_dec_ref(v___x_11_);
v_toSub_13_ = lean_ctor_get(v___x_12_, 2);
lean_inc(v_toSub_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_apply_2(v_toMul_8_, v_toTraceOne_9_, v_val_10_);
v___x_15_ = lean_apply_2(v_toMul_8_, v___x_14_, v_r_4_);
lean_inc(v___x_15_);
v___x_16_ = lean_apply_1(v_inst_2_, v___x_15_);
v___x_17_ = lean_apply_2(v_toSub_13_, v___x_15_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_quadricIndex(lean_object* v_A_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_P_23_, lean_object* v_r_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_GRH_New_Floors_Place_quadricIndex___redArg(v_inst_19_, v_inst_20_, v_P_23_, v_r_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_quadricIndex___boxed(lean_object* v_A_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_P_31_, lean_object* v_r_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_Floors_Place_quadricIndex(v_A_26_, v_inst_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_P_31_, v_r_32_);
lean_dec_ref(v_inst_30_);
return v_res_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Kernel_Composition_MeasureCompProd(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorGroups(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Measure_QuadricDisintegration(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_QuadricBlocks(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Probability_Kernel_Composition_MeasureCompProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Measure_QuadricDisintegration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
