// Lean compiler output
// Module: Lib.DiscreteSeries.Bruhat.FourierKernels
// Imports: public import Init public meta import Init public import Mathlib.Probability.Kernel.Composition.IntegralCompProd public import Lib.DiscreteSeries.Bruhat.FloorMeasures public import Lib.DiscreteSeries.Bruhat.QuadricBlocks
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
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_blockChart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_blockChart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_blockChart___redArg(lean_object* v_e_1_, lean_object* v_p_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; lean_object* v_toFun_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_fst_4_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_p_2_);
v_fst_6_ = lean_ctor_get(v_fst_4_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_fst_4_, 1);
lean_inc(v_snd_7_);
lean_dec(v_fst_4_);
v___x_8_ = lp_mathlib_Equiv_symm___redArg(v_e_1_);
v_toFun_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_toFun_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, lean_box(0));
lean_closure_set(v___x_10_, 2, lean_box(0));
lean_closure_set(v___x_10_, 3, v_fst_6_);
lean_closure_set(v___x_10_, 4, v_snd_7_);
v___x_11_ = lean_apply_1(v_toFun_9_, v_a_3_);
v___x_12_ = l_Sum_elim___redArg(v___x_10_, v_snd_5_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Floors_Place_blockChart(lean_object* v_A_13_, lean_object* v_00_u03ba_14_, lean_object* v_00_u03b9_15_, lean_object* v_B_16_, lean_object* v_00_u03b7_17_, lean_object* v_e_18_, lean_object* v_p_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_GRH_New_Floors_Place_blockChart___redArg(v_e_18_, v_p_19_, v_a_20_);
return v___x_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Kernel_Composition_IntegralCompProd(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_QuadricBlocks(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_FourierKernels(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Probability_Kernel_Composition_IntegralCompProd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_FloorMeasures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_QuadricBlocks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
