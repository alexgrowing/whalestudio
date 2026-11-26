// Lean compiler output
// Module: New.Spanning.RemainingTerms.FrameParts
// Imports: public import Init public meta import Init public import New.Spanning.RemainingTerms.Data public import New.Spanning.RemainingTerms.FrameCount
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
lean_object* lp_GRH_New_Filling_frameMiddle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toRows_u2081___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_framePartX_u2080___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_framePartX_u2080(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_framePartX_u2080___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_framePartX_u2080___redArg(lean_object* v_00_U0001d530_1_, lean_object* v_00_u03b3_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v_val_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_val_5_ = lean_ctor_get(v_00_u03b3_2_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_00_u03b3_2_);
v___x_6_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_frameMiddle), 5, 3);
lean_closure_set(v___x_6_, 0, v_00_U0001d530_1_);
lean_closure_set(v___x_6_, 1, lean_box(0));
lean_closure_set(v___x_6_, 2, v_val_5_);
v___x_7_ = lp_mathlib_Matrix_toRows_u2081___redArg(v___x_6_, v_a_3_, v_a_4_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_framePartX_u2080(lean_object* v_E_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_00_U0001d530_11_, lean_object* v_S_12_, lean_object* v_00_u03b3_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_GRH_New_Filling_framePartX_u2080___redArg(v_00_U0001d530_11_, v_00_u03b3_13_, v_a_14_, v_a_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_framePartX_u2080___boxed(lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_00_U0001d530_20_, lean_object* v_S_21_, lean_object* v_00_u03b3_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_Filling_framePartX_u2080(v_E_17_, v_inst_18_, v_inst_19_, v_00_U0001d530_20_, v_S_21_, v_00_u03b3_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_S_21_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_Data(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_FrameCount(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_FrameParts(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_RemainingTerms_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_RemainingTerms_FrameCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
