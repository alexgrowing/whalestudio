// Lean compiler output
// Module: Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
// Imports: public import Init public meta import Init public import Formalism.ThetaLiftIndependence.Statement public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
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
lean_object* lp_mathlib_LinearEquiv_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg___lam__0(lean_object* v_g_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
lean_inc_ref(v_g_1_);
v___x_3_ = lp_mathlib_LinearEquiv_symm___redArg(v_g_1_);
v___x_4_ = lp_mathlib_LinearEquiv_trans___redArg(v_b_2_, v___x_3_);
v___x_5_ = lp_mathlib_LinearEquiv_trans___redArg(v_g_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg___lam__1(lean_object* v_g_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
lean_inc_ref(v_g_6_);
v___x_8_ = lp_mathlib_LinearEquiv_trans___redArg(v_a_7_, v_g_6_);
v___x_9_ = lp_mathlib_LinearEquiv_symm___redArg(v_g_6_);
v___x_10_ = lp_mathlib_LinearEquiv_trans___redArg(v___x_9_, v___x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg(lean_object* v_g_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
lean_inc_ref(v_g_11_);
v___f_12_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg___lam__0), 2, 1);
lean_closure_set(v___f_12_, 0, v_g_11_);
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg___lam__1), 2, 1);
lean_closure_set(v___f_13_, 0, v_g_11_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___f_13_);
lean_ctor_set(v___x_14_, 1, v___f_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv(lean_object* v_K_15_, lean_object* v_V_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_h_24_, lean_object* v_g_25_, lean_object* v_hg_26_, lean_object* v_M_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___redArg(v_g_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv___boxed(lean_object* v_K_29_, lean_object* v_V_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_h_38_, lean_object* v_g_39_, lean_object* v_hg_40_, lean_object* v_M_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_conjEquiv(v_K_29_, v_V_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_inst_36_, v_inst_37_, v_h_38_, v_g_39_, v_hg_40_, v_M_41_);
lean_dec(v_h_38_);
lean_dec(v_inst_36_);
lean_dec(v_inst_35_);
lean_dec_ref(v_inst_34_);
lean_dec(v_inst_33_);
lean_dec_ref(v_inst_31_);
return v_res_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
