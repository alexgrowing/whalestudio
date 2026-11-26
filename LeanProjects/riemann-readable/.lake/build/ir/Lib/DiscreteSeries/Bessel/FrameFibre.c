// Lean compiler output
// Module: Lib.DiscreteSeries.Bessel.FrameFibre
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure public import Lib.DiscreteSeries.Haar.GramFibre
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
lean_object* lp_GRH_New_Shape_isotropicCols(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Shape_definiteCols(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromCols___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_freeCols(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Shape_freeCols(lean_object* v_00_U0001d530_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc_ref(v_00_U0001d530_1_);
v___x_4_ = lean_alloc_closure((void*)(lp_GRH_New_Shape_isotropicCols), 3, 1);
lean_closure_set(v___x_4_, 0, v_00_U0001d530_1_);
v___x_5_ = lean_alloc_closure((void*)(lp_GRH_New_Shape_definiteCols), 3, 1);
lean_closure_set(v___x_5_, 0, v_00_U0001d530_1_);
v___x_6_ = lp_mathlib_Matrix_fromCols___redArg(v___x_4_, v___x_5_, v_a_2_, v_a_3_);
return v___x_6_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Haar_GramFibre(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_FrameFibre(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Haar_GramFibre(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
