// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
// Imports: public import Init public meta import Init public import Formalism.RealPlaceAnalysis.StatementA
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_casKHW__coef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_casKHW__coef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_casKHW__coef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_casKHW__coef___redArg(lean_object* v_00_u03b5_1_, lean_object* v_00_u03bc_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
lean_inc_ref(v_00_u03b5_1_);
lean_inc(v_a_3_);
v___x_16_ = lean_apply_1(v_00_u03b5_1_, v_a_3_);
lean_inc(v_b_4_);
v___x_17_ = lean_apply_1(v_00_u03b5_1_, v_b_4_);
v___x_18_ = lean_unbox(v___x_16_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = lean_unbox(v___x_17_);
if (v___x_19_ == 0)
{
goto v___jp_5_;
}
else
{
lean_object* v___x_20_; 
lean_dec(v_b_4_);
lean_dec(v_a_3_);
lean_dec(v_00_u03bc_2_);
v___x_20_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_20_;
}
}
else
{
uint8_t v___x_21_; 
v___x_21_ = lean_unbox(v___x_17_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_dec(v_b_4_);
lean_dec(v_a_3_);
lean_dec(v_00_u03bc_2_);
v___x_22_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_22_;
}
else
{
goto v___jp_5_;
}
}
v___jp_5_:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_eq(v_a_3_, v_b_4_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_lt(v_a_3_, v_b_4_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec(v_b_4_);
lean_dec(v_a_3_);
lean_dec(v_00_u03bc_2_);
v___x_8_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___f_12_; 
lean_inc(v_00_u03bc_2_);
v___x_9_ = lean_apply_1(v_00_u03bc_2_, v_a_3_);
v___x_10_ = lean_apply_1(v_00_u03bc_2_, v_b_4_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_11_, 0, v___x_10_);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___x_9_);
lean_closure_set(v___f_12_, 1, v___f_11_);
return v___f_12_;
}
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_b_4_);
v___x_13_ = lean_apply_1(v_00_u03bc_2_, v_a_3_);
v___x_14_ = lean_unsigned_to_nat(2u);
v___x_15_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_14_, v___x_13_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_casKHW__coef(lean_object* v_n_23_, lean_object* v_00_u03b5_24_, lean_object* v_00_u03bc_25_, lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_REAL_casKHW__coef___redArg(v_00_u03b5_24_, v_00_u03bc_25_, v_a_26_, v_b_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_casKHW__coef___boxed(lean_object* v_n_29_, lean_object* v_00_u03b5_30_, lean_object* v_00_u03bc_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_REAL_casKHW__coef(v_n_29_, v_00_u03b5_30_, v_00_u03bc_31_, v_a_32_, v_b_33_);
lean_dec(v_n_29_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_RealPlaceAnalysis_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_RealPlaceAnalysis_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
