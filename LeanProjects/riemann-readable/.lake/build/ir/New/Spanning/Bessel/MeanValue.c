// Lean compiler output
// Module: New.Spanning.Bessel.MeanValue
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bessel.FrameFibre public import Lib.DiscreteSeries.Bruhat.ComplexPlace public import New.Spanning.Bessel.GramSection
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
lean_object* lp_mathlib_Equiv_optionEquivSumPUnit___redArg();
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_finSuccEquiv_x27(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_RealPlace_splitLast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_RealPlace_splitLast___closed__0;
static lean_once_cell_t lp_GRH_New_RealPlace_splitLast___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_RealPlace_splitLast___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_splitLast(lean_object*);
static lean_object* _init_lp_GRH_New_RealPlace_splitLast___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_optionEquivSumPUnit___redArg();
return v___x_1_;
}
}
static lean_object* _init_lp_GRH_New_RealPlace_splitLast___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&lp_GRH_New_RealPlace_splitLast___closed__0, &lp_GRH_New_RealPlace_splitLast___closed__0_once, _init_lp_GRH_New_RealPlace_splitLast___closed__0);
v___x_3_ = lp_mathlib_Equiv_symm___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_splitLast(lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&lp_GRH_New_RealPlace_splitLast___closed__1, &lp_GRH_New_RealPlace_splitLast___closed__1_once, _init_lp_GRH_New_RealPlace_splitLast___closed__1);
lean_inc(v_j_4_);
v___x_6_ = lp_mathlib_finSuccEquiv_x27(v_j_4_, v_j_4_);
v___x_7_ = lp_mathlib_Equiv_symm___redArg(v___x_6_);
v___x_8_ = lp_mathlib_Equiv_trans___redArg(v___x_5_, v___x_7_);
return v___x_8_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_FrameFibre(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_ComplexPlace(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Bessel_GramSection(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Bessel_MeanValue(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bessel_FrameFibre(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_ComplexPlace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Bessel_GramSection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
