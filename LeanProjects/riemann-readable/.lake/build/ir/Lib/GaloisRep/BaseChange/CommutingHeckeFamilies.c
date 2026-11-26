// Lean compiler output
// Module: Lib.GaloisRep.BaseChange.CommutingHeckeFamilies
// Imports: public import Init public meta import Init public import Lib.Shimura.HeckeTower.HeckeData public import Lib.Weil.Unramified.SplitHecke
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
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg___lam__0(lean_object* v_toInv_1_, lean_object* v_g_2_, lean_object* v_toMul_3_, lean_object* v_x_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_toInv_1_, v_g_2_);
v___x_6_ = lean_apply_2(v_toMul_3_, v___x_5_, v_x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg___lam__1(lean_object* v_toInv_7_, lean_object* v_toMul_8_, lean_object* v_g_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; 
v___f_12_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_leftTranslation___redArg___lam__0), 4, 3);
lean_closure_set(v___f_12_, 0, v_toInv_7_);
lean_closure_set(v___f_12_, 1, v_g_9_);
lean_closure_set(v___f_12_, 2, v_toMul_8_);
v___x_13_ = lp_mathlib_LinearMap_funLeft___redArg___lam__0(v___f_12_, v___y_10_, v___y_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg(lean_object* v_inst_14_){
_start:
{
lean_object* v_toMonoid_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_toMul_18_; lean_object* v___x_19_; lean_object* v_toInv_20_; lean_object* v___f_21_; 
v_toMonoid_15_ = lean_ctor_get(v_inst_14_, 0);
v___x_16_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_15_);
v___x_17_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_16_);
v_toMul_18_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_toMul_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_14_);
v_toInv_20_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_toInv_20_);
lean_dec_ref(v___x_19_);
v___f_21_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_leftTranslation___redArg___lam__1), 5, 2);
lean_closure_set(v___f_21_, 0, v_toInv_20_);
lean_closure_set(v___f_21_, 1, v_toMul_18_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___redArg___boxed(lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_Variety_leftTranslation___redArg(v_inst_22_);
lean_dec_ref(v_inst_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation(lean_object* v_G_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_GRH_New_Variety_leftTranslation___redArg(v_inst_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_leftTranslation___boxed(lean_object* v_G_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_GRH_New_Variety_leftTranslation(v_G_27_, v_inst_28_);
lean_dec_ref(v_inst_28_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_HeckeTower_HeckeData(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_SplitHecke(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_BaseChange_CommutingHeckeFamilies(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_HeckeTower_HeckeData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Unramified_SplitHecke(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
