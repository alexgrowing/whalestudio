// Lean compiler output
// Module: Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.SpanNatCastLeComap
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_PreTilt_instCommRing___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_WittVector_teichmullerFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_map___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Ainf_teich___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Ainf_teich(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_map___redArg(lean_object* v_f_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lp_mathlib_Ideal_quotientMap___redArg(v_f_1_);
v___x_3_ = lp_mathlib_Perfection_map___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_map(lean_object* v_p_4_, lean_object* v_inst_5_, lean_object* v_R_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_S_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_f_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_tree_Reformulated_AutPerF_Tilt_map___redArg(v_f_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_map___boxed(lean_object* v_p_14_, lean_object* v_inst_15_, lean_object* v_R_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_S_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_f_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Reformulated_AutPerF_Tilt_map(v_p_14_, v_inst_15_, v_R_16_, v_inst_17_, v_inst_18_, v_S_19_, v_inst_20_, v_inst_21_, v_f_22_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_17_);
lean_dec(v_p_14_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Ainf_teich___redArg(lean_object* v_p_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_inc(v_p_24_);
v___x_26_ = lp_mathlib_PreTilt_instCommRing___redArg(v_inst_25_, v_p_24_);
v___x_27_ = lean_alloc_closure((void*)(lp_mathlib_WittVector_teichmullerFun___boxed), 4, 3);
lean_closure_set(v___x_27_, 0, v_p_24_);
lean_closure_set(v___x_27_, 1, lean_box(0));
lean_closure_set(v___x_27_, 2, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Ainf_teich(lean_object* v_p_28_, lean_object* v_inst_29_, lean_object* v_R_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc(v_p_28_);
v___x_33_ = lp_mathlib_PreTilt_instCommRing___redArg(v_inst_31_, v_p_28_);
v___x_34_ = lean_alloc_closure((void*)(lp_mathlib_WittVector_teichmullerFun___boxed), 4, 3);
lean_closure_set(v___x_34_, 0, v_p_28_);
lean_closure_set(v___x_34_, 1, lean_box(0));
lean_closure_set(v___x_34_, 2, v___x_33_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
