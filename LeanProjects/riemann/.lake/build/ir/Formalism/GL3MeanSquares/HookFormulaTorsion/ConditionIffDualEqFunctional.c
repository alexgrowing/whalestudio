// Lean compiler output
// Module: Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.GL3MeanSquares.FourierTransformKernelSurjective
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___lam__0(lean_object* v_c_1_, lean_object* v_toMul_2_, lean_object* v_f_3_, lean_object* v___y_4_){
_start:
{
lean_object* v_val_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_val_5_ = lean_ctor_get(v_c_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_c_1_);
v___x_6_ = lean_apply_1(v_f_3_, v___y_4_);
v___x_7_ = lean_apply_2(v_toMul_2_, v_val_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___lam__1(lean_object* v_c_8_, lean_object* v_toMul_9_, lean_object* v_f_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_inv_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_inv_12_ = lean_ctor_get(v_c_8_, 1);
lean_inc(v_inv_12_);
lean_dec_ref(v_c_8_);
v___x_13_ = lean_apply_1(v_f_10_, v___y_11_);
v___x_14_ = lean_apply_2(v_toMul_9_, v_inv_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg(lean_object* v_inst_15_, lean_object* v_c_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toSemiring_19_; lean_object* v___x_20_; lean_object* v_toMul_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_30_; 
v___x_17_ = lp_mathlib_Field_toSemifield___redArg(v_inst_15_);
v___x_18_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_17_);
v_toSemiring_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_toSemiring_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_19_);
v_toMul_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v___x_20_, 1);
lean_dec(v_unused_31_);
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_toMul_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_28_; 
lean_inc(v_toMul_21_);
lean_inc_ref(v_c_16_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___lam__0), 4, 2);
lean_closure_set(v___f_25_, 0, v_c_16_);
lean_closure_set(v___f_25_, 1, v_toMul_21_);
v___f_26_ = lean_alloc_closure((void*)(lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___lam__1), 4, 2);
lean_closure_set(v___f_26_, 0, v_c_16_);
lean_closure_set(v___f_26_, 1, v_toMul_21_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___f_26_);
lean_ctor_set(v___x_23_, 0, v___f_25_);
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___f_25_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___f_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg___boxed(lean_object* v_inst_32_, lean_object* v_c_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg(v_inst_32_, v_c_33_);
lean_dec_ref(v_inst_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv(lean_object* v_k_35_, lean_object* v_inst_36_, lean_object* v_r_37_, lean_object* v_c_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___redArg(v_inst_36_, v_c_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv___boxed(lean_object* v_k_40_, lean_object* v_inst_41_, lean_object* v_r_42_, lean_object* v_c_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree___private_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional_0__Formalism_HermitianLattices_LocalLatticeBases_unitSmulEquiv(v_k_40_, v_inst_41_, v_r_42_, v_c_43_);
lean_dec(v_r_42_);
lean_dec_ref(v_inst_41_);
return v_res_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_FourierTransformKernelSurjective(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_FourierTransformKernelSurjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
