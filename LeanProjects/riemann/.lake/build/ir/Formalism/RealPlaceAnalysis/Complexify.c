// Lean compiler output
// Module: Formalism.RealPlaceAnalysis.Complexify
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_REAL_Jm___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_REAL_Jm___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Jm___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Jm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Jm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_UJ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_UJ___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0(lean_object* v_d_3_, lean_object* v_i_4_, lean_object* v_j_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_eq(v_i_4_, v_j_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec(v_i_4_);
lean_dec_ref(v_d_3_);
v___x_7_ = lean_obj_once(&lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___closed__0, &lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___closed__0_once, _init_lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___closed__0);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_d_3_, v_i_4_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___boxed(lean_object* v_d_9_, lean_object* v_i_10_, lean_object* v_j_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0(v_d_9_, v_i_10_, v_j_11_);
lean_dec(v_j_11_);
return v_res_12_;
}
}
static lean_object* _init_lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg(lean_object* v_d_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; lean_object* v_toFun_18_; lean_object* v___f_19_; lean_object* v___x_20_; 
v___x_17_ = lean_obj_once(&lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___closed__0, &lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___closed__0_once, _init_lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___closed__0);
v_toFun_18_ = lean_ctor_get(v___x_17_, 0);
v___f_19_ = lean_alloc_closure((void*)(lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_19_, 0, v_d_14_);
lean_inc(v_toFun_18_);
v___x_20_ = lean_apply_3(v_toFun_18_, v___f_19_, v_a_15_, v_a_16_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0(lean_object* v_n_21_, lean_object* v_d_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg(v_d_22_, v_a_23_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___boxed(lean_object* v_n_26_, lean_object* v_d_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0(v_n_26_, v_d_27_, v_a_28_, v_a_29_);
lean_dec(v_n_26_);
return v_res_30_;
}
}
static lean_object* _init_lp_tree_Formalism_REAL_Jm___lam__0___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_32_ = lp_mathlib_Complex_ofReal(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Jm___lam__0(lean_object* v_00_u03b5_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_apply_1(v_00_u03b5_33_, v_a_34_);
v___x_36_ = lean_unbox(v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; lean_object* v_re_38_; lean_object* v_im_39_; lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___x_42_; 
v___x_37_ = lean_obj_once(&lp_tree_Formalism_REAL_Jm___lam__0___closed__0, &lp_tree_Formalism_REAL_Jm___lam__0___closed__0_once, _init_lp_tree_Formalism_REAL_Jm___lam__0___closed__0);
v_re_38_ = lean_ctor_get(v___x_37_, 0);
v_im_39_ = lean_ctor_get(v___x_37_, 1);
lean_inc(v_re_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_40_, 0, v_re_38_);
lean_inc(v_im_39_);
v___f_41_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_41_, 0, v_im_39_);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___f_40_);
lean_ctor_set(v___x_42_, 1, v___f_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&lp_tree_Formalism_REAL_Jm___lam__0___closed__0, &lp_tree_Formalism_REAL_Jm___lam__0___closed__0_once, _init_lp_tree_Formalism_REAL_Jm___lam__0___closed__0);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Jm(lean_object* v_n_44_, lean_object* v_00_u03b5_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_49_; 
v___f_48_ = lean_alloc_closure((void*)(lp_tree_Formalism_REAL_Jm___lam__0), 2, 1);
lean_closure_set(v___f_48_, 0, v_00_u03b5_45_);
v___x_49_ = lp_tree_Matrix_diagonal___at___00Formalism_REAL_Jm_spec__0___redArg(v___f_48_, v_a_46_, v_a_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_Jm___boxed(lean_object* v_n_50_, lean_object* v_00_u03b5_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_REAL_Jm(v_n_50_, v_00_u03b5_51_, v_a_52_, v_a_53_);
lean_dec(v_n_50_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_UJ(lean_object* v_n_55_, lean_object* v_00_u03b5_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_REAL_UJ___boxed(lean_object* v_n_58_, lean_object* v_00_u03b5_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_REAL_UJ(v_n_58_, v_00_u03b5_59_);
lean_dec_ref(v_00_u03b5_59_);
lean_dec(v_n_58_);
return v_res_60_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_RealPlaceAnalysis_Complexify(uint8_t builtin) {
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
