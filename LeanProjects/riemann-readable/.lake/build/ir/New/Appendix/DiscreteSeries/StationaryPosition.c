// Lean compiler output
// Module: New.Appendix.DiscreteSeries.StationaryPosition
// Imports: public import Init public meta import Init public import Lib.General.Algebra.ResidueSums public import Lib.Shimura.Uniformisation.HolomorphicFamilies public import New.Appendix.DiscreteSeries.Positions
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_alternatingSignForm(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___f_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_2_, 0, v___x_1_);
return v___f_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0(lean_object* v_x_3_, lean_object* v_y_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; lean_object* v___f_11_; 
v___f_6_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0___closed__0, &lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0___closed__0_once, _init_lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0___closed__0);
v___x_7_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v_i_5_, v___f_6_);
lean_inc(v_i_5_);
v___x_8_ = lean_apply_1(v_x_3_, v_i_5_);
v___x_9_ = lean_apply_1(v_y_4_, v_i_5_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_8_);
lean_closure_set(v___f_10_, 1, v___x_9_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_11_, 0, v___x_7_);
lean_closure_set(v___f_11_, 1, v___f_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_alternatingSignForm(lean_object* v_L_12_, lean_object* v_x_13_, lean_object* v_y_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___f_15_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_alternatingSignForm___lam__0), 3, 2);
lean_closure_set(v___f_15_, 0, v_x_13_);
lean_closure_set(v___f_15_, 1, v_y_14_);
v___x_16_ = l_List_finRange(v_L_12_);
v___x_17_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_16_, v___f_15_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_ResidueSums(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(uint8_t builtin);
lean_object* initialize_GRH_New_Appendix_DiscreteSeries_Positions(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Appendix_DiscreteSeries_StationaryPosition(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Algebra_ResidueSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Appendix_DiscreteSeries_Positions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
