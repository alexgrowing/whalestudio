// Lean compiler output
// Module: Lib.GLn.SchurModule.SchurOrthogonality
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes public import Lib.GLn.SchurModule.GramMatrix
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_decreasingPosition___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_decreasingPosition___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_decreasingPosition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_decreasingPosition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_decreasingPosition___redArg___lam__0(lean_object* v_l_1_, lean_object* v_i_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
lean_inc_ref(v_l_1_);
v___x_4_ = lean_apply_1(v_l_1_, v_i_2_);
v___x_5_ = lean_apply_1(v_l_1_, v_a_3_);
v___x_6_ = lean_int_dec_lt(v___x_4_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_decreasingPosition___redArg___lam__0___boxed(lean_object* v_l_7_, lean_object* v_i_8_, lean_object* v_a_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_GRH_New_decreasingPosition___redArg___lam__0(v_l_7_, v_i_8_, v_a_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_decreasingPosition___redArg(lean_object* v_inst_12_, lean_object* v_l_13_, lean_object* v_i_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___f_15_ = lean_alloc_closure((void*)(lp_GRH_New_decreasingPosition___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_15_, 0, v_l_13_);
lean_closure_set(v___f_15_, 1, v_i_14_);
v___x_16_ = lp_mathlib_Multiset_filter___redArg(v___f_15_, v_inst_12_);
v___x_17_ = l_List_lengthTR___redArg(v___x_16_);
lean_dec(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_decreasingPosition(lean_object* v_n_18_, lean_object* v_inst_19_, lean_object* v_l_20_, lean_object* v_i_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_GRH_New_decreasingPosition___redArg(v_inst_19_, v_l_20_, v_i_21_);
return v___x_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_PsiKTypes(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_GramMatrix(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GLn_SchurModule_SchurOrthogonality(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_PsiKTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_SchurModule_GramMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
