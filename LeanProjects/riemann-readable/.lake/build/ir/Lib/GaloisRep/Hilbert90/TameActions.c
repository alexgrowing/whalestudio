// Lean compiler output
// Module: Lib.GaloisRep.Hilbert90.TameActions
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.MatrixPolynomials
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
lean_object* lp_mathlib_Ideal_quotientMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_quotientNatMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_quotientNatMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_quotientNatMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_quotientNatMap___redArg(lean_object* v_00_u03c3_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_Ideal_quotientMap___redArg(v_00_u03c3_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_quotientNatMap(lean_object* v_R_3_, lean_object* v_inst_4_, lean_object* v_00_u03c3_5_, lean_object* v_N_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_mathlib_Ideal_quotientMap___redArg(v_00_u03c3_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_quotientNatMap___boxed(lean_object* v_R_8_, lean_object* v_inst_9_, lean_object* v_00_u03c3_10_, lean_object* v_N_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_quotientNatMap(v_R_8_, v_inst_9_, v_00_u03c3_10_, v_N_11_);
lean_dec(v_N_11_);
lean_dec_ref(v_inst_9_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatrixPolynomials(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_Hilbert90_TameActions(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_MatrixPolynomials(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
