// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.FramesLemmas
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.Frames public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
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
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_diagE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_diagE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0(lean_object* v_toOne_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_inc(v_toOne_1_);
return v_toOne_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0___boxed(lean_object* v_toOne_4_, lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0(v_toOne_4_, v_x_5_, v_x_6_);
lean_dec(v_x_6_);
lean_dec(v_x_5_);
lean_dec(v_toOne_4_);
return v_res_7_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP___redArg(lean_object* v_inst_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; lean_object* v_toRing_13_; lean_object* v___x_14_; lean_object* v_toAddMonoidWithOne_15_; lean_object* v_toOne_16_; lean_object* v___x_17_; lean_object* v_toFun_18_; lean_object* v___f_19_; lean_object* v___x_20_; 
v___x_12_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_9_);
v_toRing_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc_ref(v_toRing_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_13_);
v_toAddMonoidWithOne_15_ = lean_ctor_get(v___x_14_, 1);
lean_inc_ref(v_toAddMonoidWithOne_15_);
lean_dec_ref(v___x_14_);
v_toOne_16_ = lean_ctor_get(v_toAddMonoidWithOne_15_, 2);
lean_inc(v_toOne_16_);
lean_dec_ref(v_toAddMonoidWithOne_15_);
v___x_17_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0, &lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0_once, _init_lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0);
v_toFun_18_ = lean_ctor_get(v___x_17_, 0);
v___f_19_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_19_, 0, v_toOne_16_);
lean_inc(v_toFun_18_);
v___x_20_ = lean_apply_3(v_toFun_18_, v___f_19_, v_a_10_, v_a_11_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_sumP(lean_object* v_K_21_, lean_object* v_inst_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_L2_DIV_sumP___redArg(v_inst_22_, v_a_23_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_diagE___redArg(lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_29_; lean_object* v_toRing_30_; lean_object* v___x_31_; lean_object* v_toAddMonoidWithOne_32_; lean_object* v_toOne_33_; lean_object* v___x_34_; lean_object* v_toFun_35_; lean_object* v___f_36_; lean_object* v___x_37_; 
v___x_29_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_26_);
v_toRing_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref(v_toRing_30_);
lean_dec_ref(v___x_29_);
v___x_31_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_30_);
v_toAddMonoidWithOne_32_ = lean_ctor_get(v___x_31_, 1);
lean_inc_ref(v_toAddMonoidWithOne_32_);
lean_dec_ref(v___x_31_);
v_toOne_33_ = lean_ctor_get(v_toAddMonoidWithOne_32_, 2);
lean_inc(v_toOne_33_);
lean_dec_ref(v_toAddMonoidWithOne_32_);
v___x_34_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0, &lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0_once, _init_lp_tree_Formalism_L2_DIV_sumP___redArg___closed__0);
v_toFun_35_ = lean_ctor_get(v___x_34_, 0);
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_sumP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_36_, 0, v_toOne_33_);
lean_inc(v_toFun_35_);
v___x_37_ = lean_apply_3(v_toFun_35_, v___f_36_, v_a_27_, v_a_28_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_diagE(lean_object* v_K_38_, lean_object* v_inst_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_L2_DIV_diagE___redArg(v_inst_39_, v_a_40_, v_a_41_);
return v___x_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Frames(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_FramesLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Frames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
