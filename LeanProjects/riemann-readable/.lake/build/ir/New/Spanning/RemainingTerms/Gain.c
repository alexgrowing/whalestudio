// Lean compiler output
// Module: New.Spanning.RemainingTerms.Gain
// Imports: public import Init public meta import Init public import New.Spanning.RemainingTerms.Cut
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
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lp_mathlib_Matrix_col(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Filling_linkSource___redArg();
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Filling_sourceCols___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Filling_sourceCols___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___redArg___lam__0(lean_object* v_y_1_, lean_object* v_a_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_56__overap_5_; lean_object* v___x_6_; 
v___x_4_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_col), 6, 5);
lean_closure_set(v___x_4_, 0, lean_box(0));
lean_closure_set(v___x_4_, 1, lean_box(0));
lean_closure_set(v___x_4_, 2, lean_box(0));
lean_closure_set(v___x_4_, 3, v_y_1_);
lean_closure_set(v___x_4_, 4, v_a_2_);
v___x_56__overap_5_ = lp_GRH_New_Filling_linkSource___redArg();
v___x_6_ = lean_apply_2(v___x_56__overap_5_, v___x_4_, v___y_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___redArg___lam__1(lean_object* v___x_7_, lean_object* v___f_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_toFun_11_; lean_object* v___x_12_; 
v_toFun_11_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_toFun_11_);
lean_dec_ref(v___x_7_);
v___x_12_ = lean_apply_3(v_toFun_11_, v___f_8_, v___y_9_, v___y_10_);
return v___x_12_;
}
}
static lean_object* _init_lp_GRH_New_Filling_sourceCols___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_mathlib_Equiv_refl___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___redArg(lean_object* v_y_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___f_19_; lean_object* v___x_20_; 
v___f_17_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_sourceCols___redArg___lam__0), 3, 1);
lean_closure_set(v___f_17_, 0, v_y_14_);
v___x_18_ = lean_obj_once(&lp_GRH_New_Filling_sourceCols___redArg___closed__0, &lp_GRH_New_Filling_sourceCols___redArg___closed__0_once, _init_lp_GRH_New_Filling_sourceCols___redArg___closed__0);
v___f_19_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_sourceCols___redArg___lam__1), 4, 2);
lean_closure_set(v___f_19_, 0, v___x_18_);
lean_closure_set(v___f_19_, 1, v___f_17_);
v___x_20_ = lp_mathlib_Matrix_transpose___redArg(v___f_19_, v_a_15_, v_a_16_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols(lean_object* v_E_21_, lean_object* v_inst_22_, lean_object* v_00_U0001d530_23_, lean_object* v_00_u03c3_24_, lean_object* v_y_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GRH_New_Filling_sourceCols___redArg(v_y_25_, v_a_26_, v_a_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_sourceCols___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_00_U0001d530_31_, lean_object* v_00_u03c3_32_, lean_object* v_y_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_Filling_sourceCols(v_E_29_, v_inst_30_, v_00_U0001d530_31_, v_00_u03c3_32_, v_y_33_, v_a_34_, v_a_35_);
lean_dec_ref(v_00_U0001d530_31_);
lean_dec_ref(v_inst_30_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_Cut(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_Gain(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_RemainingTerms_Cut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
