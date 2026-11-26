// Lean compiler output
// Module: New.Spanning.Frames.FixedLines
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.BlockEmbeddings public import Lib.General.LinearAlgebra.TensorChains public import New.Spanning.Frames.FiniteShells public import New.Spanning.MainTerm.FillingLevel public import New.Spanning.Unfolding.Climbing
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
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Filling_placeFiber___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Filling_placeFiber___redArg___lam__0(lean_object* v_blk_1_, lean_object* v_inst_2_, lean_object* v_i_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_apply_1(v_blk_1_, v_a_4_);
v___x_6_ = lean_apply_2(v_inst_2_, v___x_5_, v_i_3_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber___redArg___lam__0___boxed(lean_object* v_blk_8_, lean_object* v_inst_9_, lean_object* v_i_10_, lean_object* v_a_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_GRH_New_Filling_placeFiber___redArg___lam__0(v_blk_8_, v_inst_9_, v_i_10_, v_a_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber___redArg(lean_object* v_T_14_, lean_object* v_inst_15_, lean_object* v_blk_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___f_18_; lean_object* v___x_19_; 
v___f_18_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_placeFiber___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_18_, 0, v_blk_16_);
lean_closure_set(v___f_18_, 1, v_inst_15_);
lean_closure_set(v___f_18_, 2, v_i_17_);
v___x_19_ = lp_mathlib_Multiset_filter___redArg(v___f_18_, v_T_14_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber(lean_object* v_E_20_, lean_object* v_inst_21_, lean_object* v_T_22_, lean_object* v_00_u03b9_23_, lean_object* v_inst_24_, lean_object* v_blk_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; 
v___f_27_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_placeFiber___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_27_, 0, v_blk_25_);
lean_closure_set(v___f_27_, 1, v_inst_24_);
lean_closure_set(v___f_27_, 2, v_i_26_);
v___x_28_ = lp_mathlib_Multiset_filter___redArg(v___f_27_, v_T_22_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_placeFiber___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_T_31_, lean_object* v_00_u03b9_32_, lean_object* v_inst_33_, lean_object* v_blk_34_, lean_object* v_i_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_Filling_placeFiber(v_E_29_, v_inst_30_, v_T_31_, v_00_u03b9_32_, v_inst_33_, v_blk_34_, v_i_35_);
lean_dec_ref(v_inst_30_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_TensorChains(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Frames_FiniteShells(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_MainTerm_FillingLevel(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_Climbing(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Frames_FixedLines(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_TensorChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Frames_FiniteShells(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_MainTerm_FillingLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_Climbing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
