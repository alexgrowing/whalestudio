// Lean compiler output
// Module: Lib.Shimura.ThetaModuli.FlatClosure
// Imports: public import Init public meta import Init public import Lib.General.Algebra.MultivariatePolynomials public import Lib.General.Geometry.GeometricPoints public import Lib.General.LinearAlgebra.MatrixPolynomials
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
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Variety_ThetaNull_leadingExponents___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents(lean_object* v_J_5_, lean_object* v_A_6_, lean_object* v_k_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_00_u03c6_10_, lean_object* v_T_11_, lean_object* v_o_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ThetaNull_leadingExponents___boxed(lean_object* v_J_14_, lean_object* v_A_15_, lean_object* v_k_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_00_u03c6_19_, lean_object* v_T_20_, lean_object* v_o_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GRH_New_Variety_ThetaNull_leadingExponents(v_J_14_, v_A_15_, v_k_16_, v_inst_17_, v_inst_18_, v_00_u03c6_19_, v_T_20_, v_o_21_);
lean_dec_ref(v_o_21_);
lean_dec(v_00_u03c6_19_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
return v_res_22_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Geometry_GeometricPoints(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatrixPolynomials(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_FlatClosure(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Algebra_MultivariatePolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Geometry_GeometricPoints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_MatrixPolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
