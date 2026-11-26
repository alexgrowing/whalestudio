// Lean compiler output
// Module: Lib.Cohomology.ProjectiveLine.TiltedLineFormula
// Imports: public import Init public meta import Init public import Lib.Cohomology.ProjectiveLine.PerfectLine public import Lib.Cohomology.ProperBaseChange.Theorem
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
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___redArg(uint8_t v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___redArg___boxed(lean_object* v_x_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_){
_start:
{
uint8_t v_x_24__boxed_11_; lean_object* v_res_12_; 
v_x_24__boxed_11_ = lean_unbox(v_x_8_);
v_res_12_ = lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___redArg(v_x_24__boxed_11_, v_h__1_9_, v_h__2_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter(lean_object* v_motive_13_, uint8_t v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (v_x_14_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__2_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__1_15_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter___boxed(lean_object* v_motive_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
uint8_t v_x_35__boxed_25_; lean_object* v_res_26_; 
v_x_35__boxed_25_ = lean_unbox(v_x_22_);
v_res_26_ = lp_GRH___private_Lib_Cohomology_ProjectiveLine_TiltedLineFormula_0__New_Variety_TorsionCoeff_lineDegree_match__1_splitter(v_motive_21_, v_x_35__boxed_25_, v_h__1_23_, v_h__2_24_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_ProjectiveLine_PerfectLine(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_ProperBaseChange_Theorem(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_ProjectiveLine_TiltedLineFormula(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_ProjectiveLine_PerfectLine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_ProperBaseChange_Theorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
