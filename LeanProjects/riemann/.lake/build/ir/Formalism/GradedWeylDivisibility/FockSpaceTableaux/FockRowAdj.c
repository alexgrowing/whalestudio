// Lean compiler output
// Module: Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementA public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
static lean_once_cell_t lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg(lean_object* v_g_3_, lean_object* v_v_4_, lean_object* v_w_5_){
_start:
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v_fst_8_; lean_object* v_snd_9_; uint8_t v___x_10_; 
v_fst_6_ = lean_ctor_get(v_v_4_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_v_4_, 1);
lean_inc(v_snd_7_);
lean_dec_ref(v_v_4_);
v_fst_8_ = lean_ctor_get(v_w_5_, 0);
lean_inc(v_fst_8_);
v_snd_9_ = lean_ctor_get(v_w_5_, 1);
lean_inc(v_snd_9_);
lean_dec_ref(v_w_5_);
v___x_10_ = lean_nat_dec_eq(v_snd_7_, v_snd_9_);
lean_dec(v_snd_9_);
lean_dec(v_snd_7_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec(v_fst_8_);
lean_dec(v_fst_6_);
lean_dec_ref(v_g_3_);
v___x_11_ = lean_obj_once(&lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg___closed__0, &lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg___closed__0_once, _init_lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg___closed__0);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_2(v_g_3_, v_fst_6_, v_fst_8_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat(lean_object* v_r_13_, lean_object* v_n_14_, lean_object* v_g_15_, lean_object* v_v_16_, lean_object* v_w_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___redArg(v_g_15_, v_v_16_, v_w_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat___boxed(lean_object* v_r_19_, lean_object* v_n_20_, lean_object* v_g_21_, lean_object* v_v_22_, lean_object* v_w_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_GradedWeylDivisibility_LFocks__rowMat(v_r_19_, v_n_20_, v_g_21_, v_v_22_, v_w_23_);
lean_dec(v_n_20_);
lean_dec(v_r_19_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementA(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj(uint8_t builtin) {
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
res = initialize_tree_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
