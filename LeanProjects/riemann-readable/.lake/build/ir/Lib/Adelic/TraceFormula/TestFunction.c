// Lean compiler output
// Module: Lib.Adelic.TraceFormula.TestFunction
// Imports: public import Init public meta import Init public import Lib.Adelic.Adeles.LocalFactors public import Lib.General.LinearAlgebra.IdempotentRadical public import Lib.Weil.Unramified.HeckeGL
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_restrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_TestFunction___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction(lean_object* v_G_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg___lam__0(lean_object* v_g_8_, lean_object* v_toInv_9_, lean_object* v_toMul_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_fst_12_ = lean_ctor_get(v_g_8_, 0);
lean_inc(v_fst_12_);
v_snd_13_ = lean_ctor_get(v_g_8_, 1);
lean_inc(v_snd_13_);
lean_dec_ref(v_g_8_);
v___x_14_ = lean_apply_1(v_toInv_9_, v_fst_12_);
lean_inc(v_toMul_10_);
v___x_15_ = lean_apply_2(v_toMul_10_, v___x_14_, v_x_11_);
v___x_16_ = lean_apply_2(v_toMul_10_, v___x_15_, v_snd_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg___lam__1(lean_object* v_toInv_17_, lean_object* v_toMul_18_, lean_object* v_g_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_199__overap_24_; lean_object* v___x_25_; 
v___f_22_ = lean_alloc_closure((void*)(lp_GRH_New_TestFunction_translate___redArg___lam__0), 4, 3);
lean_closure_set(v___f_22_, 0, v_g_19_);
lean_closure_set(v___f_22_, 1, v_toInv_17_);
lean_closure_set(v___f_22_, 2, v_toMul_18_);
v___f_23_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_funLeft___redArg___lam__0), 3, 1);
lean_closure_set(v___f_23_, 0, v___f_22_);
v___x_199__overap_24_ = lp_mathlib_LinearMap_restrict___redArg(v___f_23_);
v___x_25_ = lean_apply_2(v___x_199__overap_24_, v___y_20_, v___y_21_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg(lean_object* v_inst_26_){
_start:
{
lean_object* v_toMonoid_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_toMul_30_; lean_object* v___x_31_; lean_object* v_toInv_32_; lean_object* v___f_33_; 
v_toMonoid_27_ = lean_ctor_get(v_inst_26_, 0);
v___x_28_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_27_);
v___x_29_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_28_);
v_toMul_30_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_toMul_30_);
lean_dec_ref(v___x_29_);
v___x_31_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_26_);
v_toInv_32_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_toInv_32_);
lean_dec_ref(v___x_31_);
v___f_33_ = lean_alloc_closure((void*)(lp_GRH_New_TestFunction_translate___redArg___lam__1), 5, 2);
lean_closure_set(v___f_33_, 0, v_toInv_32_);
lean_closure_set(v___f_33_, 1, v_toMul_30_);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___redArg___boxed(lean_object* v_inst_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_GRH_New_TestFunction_translate___redArg(v_inst_34_);
lean_dec_ref(v_inst_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate(lean_object* v_G_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_GRH_New_TestFunction_translate___redArg(v_inst_37_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_translate___boxed(lean_object* v_G_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_GRH_New_TestFunction_translate(v_G_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_inst_46_);
lean_dec_ref(v_inst_43_);
return v_res_47_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Adeles_LocalFactors(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_IdempotentRadical(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_HeckeGL(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_TraceFormula_TestFunction(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Adeles_LocalFactors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_IdempotentRadical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Unramified_HeckeGL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
