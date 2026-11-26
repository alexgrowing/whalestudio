// Lean compiler output
// Module: Lib.General.Measure.HaarModulus
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.IntegralLattices
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsMapNonUnital___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsMapNonUnital___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsMapNonUnital(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitsMapNonUnital___redArg___lam__0(lean_object* v_toSub_1_, lean_object* v_toOne_2_, lean_object* v_f_3_, lean_object* v_toAdd_4_, lean_object* v_toOne_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_apply_2(v_toSub_1_, v_x_6_, v_toOne_2_);
v___x_8_ = lean_apply_1(v_f_3_, v___x_7_);
v___x_9_ = lean_apply_2(v_toAdd_4_, v_toOne_5_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitsMapNonUnital___redArg(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_f_12_){
_start:
{
lean_object* v_toSemiring_13_; lean_object* v___x_14_; lean_object* v_toAdd_15_; lean_object* v___x_16_; lean_object* v_toAddMonoidWithOne_17_; lean_object* v_toOne_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_toAddMonoidWithOne_21_; lean_object* v_toSub_22_; lean_object* v_toOne_23_; lean_object* v___f_24_; lean_object* v___f_25_; 
v_toSemiring_13_ = lean_ctor_get(v_inst_11_, 0);
lean_inc_ref(v_toSemiring_13_);
v___x_14_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_13_);
v_toAdd_15_ = lean_ctor_get(v___x_14_, 1);
lean_inc(v_toAdd_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_11_);
v_toAddMonoidWithOne_17_ = lean_ctor_get(v___x_16_, 1);
lean_inc_ref(v_toAddMonoidWithOne_17_);
lean_dec_ref(v___x_16_);
v_toOne_18_ = lean_ctor_get(v_toAddMonoidWithOne_17_, 2);
lean_inc(v_toOne_18_);
lean_dec_ref(v_toAddMonoidWithOne_17_);
v___x_19_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_10_);
v___x_20_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_19_);
v_toAddMonoidWithOne_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc_ref(v_toAddMonoidWithOne_21_);
lean_dec_ref(v___x_19_);
v_toSub_22_ = lean_ctor_get(v___x_20_, 2);
lean_inc(v_toSub_22_);
lean_dec_ref(v___x_20_);
v_toOne_23_ = lean_ctor_get(v_toAddMonoidWithOne_21_, 2);
lean_inc(v_toOne_23_);
lean_dec_ref(v_toAddMonoidWithOne_21_);
v___f_24_ = lean_alloc_closure((void*)(lp_GRH_New_unitsMapNonUnital___redArg___lam__0), 6, 5);
lean_closure_set(v___f_24_, 0, v_toSub_22_);
lean_closure_set(v___f_24_, 1, v_toOne_23_);
lean_closure_set(v___f_24_, 2, v_f_12_);
lean_closure_set(v___f_24_, 3, v_toAdd_15_);
lean_closure_set(v___f_24_, 4, v_toOne_18_);
v___f_25_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_25_, 0, v___f_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitsMapNonUnital(lean_object* v_K_26_, lean_object* v_R_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_f_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_GRH_New_unitsMapNonUnital___redArg(v_inst_28_, v_inst_29_, v_f_30_);
return v___x_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_IntegralLattices(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Measure_HaarModulus(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_IntegralLattices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
