// Lean compiler output
// Module: Formalism.LatticeLocalGlobal.LatticeLocalGlobalOfGlobal
// Imports: public import Init public meta import Init public import Formalism.LatticeLocalGlobal.Statement
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___lam__0(lean_object* v_v_1_, lean_object* v_B_2_, lean_object* v_i_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_v_1_);
v___x_5_ = lean_apply_1(v_v_1_, v_i_3_);
v___x_6_ = lean_apply_1(v_v_1_, v_j_4_);
v___x_7_ = lean_apply_2(v_B_2_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg(lean_object* v_B_9_, lean_object* v_v_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; lean_object* v_toFun_14_; lean_object* v___f_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___closed__0, &lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___closed__0_once, _init_lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___closed__0);
v_toFun_14_ = lean_ctor_get(v___x_13_, 0);
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg___lam__0), 4, 2);
lean_closure_set(v___f_15_, 0, v_v_10_);
lean_closure_set(v___f_15_, 1, v_B_9_);
lean_inc(v_toFun_14_);
v___x_16_ = lean_apply_3(v_toFun_14_, v___f_15_, v_a_11_, v_a_12_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3(lean_object* v_K_17_, lean_object* v_M_18_, lean_object* v_n_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_00_u03c3_23_, lean_object* v_B_24_, lean_object* v_v_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___redArg(v_B_24_, v_v_25_, v_a_26_, v_a_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3___boxed(lean_object* v_K_29_, lean_object* v_M_30_, lean_object* v_n_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_00_u03c3_35_, lean_object* v_B_36_, lean_object* v_v_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_LatticeLocalGlobalTheory_gram_u03c3(v_K_29_, v_M_30_, v_n_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_00_u03c3_35_, v_B_36_, v_v_37_, v_a_38_, v_a_39_);
lean_dec(v_00_u03c3_35_);
lean_dec(v_inst_34_);
lean_dec_ref(v_inst_33_);
lean_dec_ref(v_inst_32_);
return v_res_40_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeLocalGlobal_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LatticeLocalGlobal_LatticeLocalGlobalOfGlobal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeLocalGlobal_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
