// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.StatementC
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementA
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
lean_object* lp_mathlib_Equiv_prodComm(lean_object*, lean_object*);
lean_object* lp_mathlib_finProdFinEquiv___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_prodComm(lean_box(0), lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg(lean_object* v_r_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg___closed__0, &lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg___closed__0_once, _init_lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg___closed__0);
v___x_4_ = lp_mathlib_finProdFinEquiv___redArg(v_r_2_);
v___x_5_ = lp_mathlib_Equiv_trans___redArg(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx(lean_object* v_r_6_, lean_object* v_n_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_tree_Formalism_GradedWeylDivisibility_cmIdx___redArg(v_r_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_cmIdx___boxed(lean_object* v_r_9_, lean_object* v_n_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_Formalism_GradedWeylDivisibility_cmIdx(v_r_9_, v_n_10_);
lean_dec(v_n_10_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
