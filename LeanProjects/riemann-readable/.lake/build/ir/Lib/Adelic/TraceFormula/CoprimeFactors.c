// Lean compiler output
// Module: Lib.Adelic.TraceFormula.CoprimeFactors
// Imports: public import Init public meta import Init public import Lib.Adelic.TraceFormula.FibreIntegral public import Lib.General.LinearAlgebra.Eigenvalues
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
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_blockDiagonalGroup___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup(lean_object* v_n_5_, lean_object* v_k_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_00_u03b5_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockDiagonalGroup___boxed(lean_object* v_n_12_, lean_object* v_k_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_00_u03b5_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_blockDiagonalGroup(v_n_12_, v_k_13_, v_inst_14_, v_inst_15_, v_inst_16_, v_00_u03b5_17_);
lean_dec(v_00_u03b5_17_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_15_);
lean_dec(v_inst_14_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_TraceFormula_FibreIntegral(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_TraceFormula_CoprimeFactors(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_TraceFormula_FibreIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
