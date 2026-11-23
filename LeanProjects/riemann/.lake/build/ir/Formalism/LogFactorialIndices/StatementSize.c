// Lean compiler output
// Module: Formalism.LogFactorialIndices.StatementSize
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_YoungDiagram_rowLen(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_YoungDiagram_colLen(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_hookProd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_hookProd(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_hookProd___lam__0(lean_object* v_00_u03bc_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_fst_3_ = lean_ctor_get(v_x_2_, 0);
lean_inc_n(v_fst_3_, 2);
v_snd_4_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_x_2_);
lean_inc(v_00_u03bc_1_);
v___x_5_ = lp_mathlib_YoungDiagram_rowLen(v_00_u03bc_1_, v_fst_3_);
v___x_6_ = lean_nat_sub(v___x_5_, v_snd_4_);
lean_dec(v___x_5_);
v___x_7_ = lp_mathlib_YoungDiagram_colLen(v_00_u03bc_1_, v_snd_4_);
v___x_8_ = lean_nat_sub(v___x_7_, v_fst_3_);
lean_dec(v_fst_3_);
lean_dec(v___x_7_);
v___x_9_ = lean_nat_add(v___x_6_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_6_);
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_sub(v___x_9_, v___x_10_);
lean_dec(v___x_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeIndexTer_hookProd(lean_object* v_00_u03bc_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; 
lean_inc(v_00_u03bc_12_);
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_LatticeIndexTer_hookProd___lam__0), 2, 1);
lean_closure_set(v___f_13_, 0, v_00_u03bc_12_);
v___x_14_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v_00_u03bc_12_, v___f_13_);
return v___x_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LogFactorialIndices_StatementSize(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
