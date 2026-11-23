// Lean compiler output
// Module: Formalism.HermitianLattices.HermitianLatticesProofs.ThetaBasic
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HermitianLattices.StatementTheta
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
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg___lam__0(lean_object* v_g_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_toLinearMap_3_; lean_object* v___x_4_; 
v_toLinearMap_3_ = lean_ctor_get(v_g_1_, 0);
lean_inc(v_toLinearMap_3_);
lean_dec_ref(v_g_1_);
v___x_4_ = lean_apply_1(v_toLinearMap_3_, v_x_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg___lam__1(lean_object* v_g_5_, lean_object* v_y_6_){
_start:
{
lean_object* v___x_7_; lean_object* v_toLinearMap_8_; lean_object* v___x_9_; 
v___x_7_ = lp_mathlib_LinearEquiv_symm___redArg(v_g_5_);
v_toLinearMap_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_toLinearMap_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = lean_apply_1(v_toLinearMap_8_, v_y_6_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg(lean_object* v_g_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___x_13_; 
lean_inc_ref(v_g_10_);
v___f_11_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_g_10_);
v___f_12_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg___lam__1), 2, 1);
lean_closure_set(v___f_12_, 0, v_g_10_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___f_11_);
lean_ctor_set(v___x_13_, 1, v___f_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv(lean_object* v_K_14_, lean_object* v_V_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_g_23_, lean_object* v_L_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___redArg(v_g_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv___boxed(lean_object* v_K_26_, lean_object* v_V_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_g_35_, lean_object* v_L_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_HermitianLatticesTheory_thetaBasic__eqv(v_K_26_, v_V_27_, v_inst_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_g_35_, v_L_36_);
lean_dec(v_inst_33_);
lean_dec(v_inst_32_);
lean_dec_ref(v_inst_31_);
lean_dec(v_inst_30_);
lean_dec_ref(v_inst_28_);
return v_res_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_StatementTheta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaBasic(uint8_t builtin) {
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
res = initialize_tree_Formalism_HermitianLattices_StatementTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
