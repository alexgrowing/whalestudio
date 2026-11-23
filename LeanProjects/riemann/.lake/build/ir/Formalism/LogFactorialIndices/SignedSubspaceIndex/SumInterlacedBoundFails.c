// Lean compiler output
// Module: Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
// Imports: public import Init public meta import Init public import Formalism.LogFactorialIndices.StatementSize
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
static lean_once_cell_t lp_tree_Formalism_LatticeIndexTer_chi___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LatticeIndexTer_chi___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_chi(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_chi___boxed(lean_object*);
static lean_object* _init_lp_tree_Formalism_LatticeIndexTer_chi___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___f_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_2_, 0, v___x_1_);
return v___f_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_chi(lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_nat_dec_eq(v_n_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_6_;
}
else
{
lean_object* v___f_7_; 
v___f_7_ = lean_obj_once(&lp_tree_Formalism_LatticeIndexTer_chi___closed__0, &lp_tree_Formalism_LatticeIndexTer_chi___closed__0_once, _init_lp_tree_Formalism_LatticeIndexTer_chi___closed__0);
return v___f_7_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_chi___boxed(lean_object* v_n_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_LatticeIndexTer_chi(v_n_8_);
lean_dec(v_n_8_);
return v_res_9_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LogFactorialIndices_StatementSize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LogFactorialIndices_StatementSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
