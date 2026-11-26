// Lean compiler output
// Module: Lib.Shimura.ThetaNormality.RiemannRelation
// Imports: public import Init public meta import Init public import Lib.Shimura.ThetaModuli.PELThetaTori
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
lean_object* lp_mathlib_AddMonoid_toAddZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_AddZeroClass_toAddZero___redArg(lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_k_2_, lean_object* v_l_3_){
_start:
{
lean_object* v_toCommRing_4_; lean_object* v_toSemiring_5_; lean_object* v_toAddCommMonoid_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toZero_9_; lean_object* v___x_10_; lean_object* v_snd_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_toCommRing_4_ = lean_ctor_get(v_inst_1_, 0);
v_toSemiring_5_ = lean_ctor_get(v_toCommRing_4_, 0);
v_toAddCommMonoid_6_ = lean_ctor_get(v_toSemiring_5_, 0);
v___x_7_ = lp_mathlib_AddMonoid_toAddZeroClass___redArg(v_toAddCommMonoid_6_);
v___x_8_ = lp_mathlib_AddZeroClass_toAddZero___redArg(v___x_7_);
v_toZero_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_toZero_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lean_apply_1(v_k_2_, v_l_3_);
v_snd_11_ = lean_ctor_get(v___x_10_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 0);
lean_dec(v_unused_19_);
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_snd_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v_toZero_9_);
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_toZero_9_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_snd_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg___lam__0___boxed(lean_object* v_inst_20_, lean_object* v_k_21_, lean_object* v_l_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg___lam__0(v_inst_20_, v_k_21_, v_l_22_);
lean_dec_ref(v_inst_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg(lean_object* v_inst_24_, lean_object* v_p_25_, lean_object* v_k_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_28_, 0, v_inst_24_);
lean_closure_set(v___f_28_, 1, v_k_26_);
v___x_29_ = l_Sum_elim___redArg(v___f_28_, v_p_25_, v_a_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs(lean_object* v_E_30_, lean_object* v_K_31_, lean_object* v_inst_32_, lean_object* v_p_33_, lean_object* v_k_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_GRH_New_ThetaTori_ThetaTorus_doubledCoeffs___redArg(v_inst_32_, v_p_33_, v_k_34_, v_a_35_);
return v___x_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ThetaNormality_RiemannRelation(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
