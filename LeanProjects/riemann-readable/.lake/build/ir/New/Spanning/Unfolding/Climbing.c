// Lean compiler output
// Module: New.Spanning.Unfolding.Climbing
// Imports: public import Init public meta import Init public import Lib.Adelic.QuotientMeasure.UnfoldingInStages public import New.Spanning.Unfolding.AmplitudeSums
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
lean_object* l_Sum_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices___redArg___lam__0(lean_object* v_00_U0001d530_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_00_u03f1_3_; 
v_00_u03f1_3_ = lean_ctor_get(v_00_U0001d530_1_, 0);
lean_inc(v_00_u03f1_3_);
return v_00_u03f1_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices___redArg___lam__0___boxed(lean_object* v_00_U0001d530_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GRH_New_Filling_lastIndices___redArg___lam__0(v_00_U0001d530_4_, v_x_5_);
lean_dec_ref(v_00_U0001d530_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices___redArg(lean_object* v_00_U0001d530_7_, lean_object* v_00_u03c1_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_toFun_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_toFun_10_ = lean_ctor_get(v_00_u03c1_8_, 0);
lean_inc(v_toFun_10_);
lean_dec_ref(v_00_u03c1_8_);
v___f_11_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_lastIndices___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_11_, 0, v_00_U0001d530_7_);
v___x_12_ = lean_apply_1(v_toFun_10_, v_a_9_);
lean_inc_ref(v___f_11_);
v___x_13_ = l_Sum_map___redArg(v___f_11_, v___f_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_lastIndices(lean_object* v_W_14_, lean_object* v_00_U0001d530_15_, lean_object* v_00_u03c1_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_GRH_New_Filling_lastIndices___redArg(v_00_U0001d530_15_, v_00_u03c1_16_, v_a_17_);
return v___x_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_QuotientMeasure_UnfoldingInStages(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_AmplitudeSums(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_Climbing(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_QuotientMeasure_UnfoldingInStages(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_AmplitudeSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
