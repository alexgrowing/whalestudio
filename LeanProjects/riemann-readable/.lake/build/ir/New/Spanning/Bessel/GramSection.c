// Lean compiler output
// Module: New.Spanning.Bessel.GramSection
// Imports: public import Init public meta import Init public import Lib.General.Analysis.HolomorphicIntegrals public import New.Spanning.Bessel.Basic
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lp_mathlib_Fin_snoc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_RealPlace_diagLast___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_RealPlace_diagLast___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_diagLast___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_diagLast___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_RealPlace_diagLast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_RealPlace_diagLast___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_RealPlace_diagLast___closed__0 = (const lean_object*)&lp_GRH_New_RealPlace_diagLast___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_diagLast(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0(lean_object* v_d_3_, lean_object* v_i_4_, lean_object* v_j_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_eq(v_i_4_, v_j_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec(v_i_4_);
lean_dec_ref(v_d_3_);
v___x_7_ = lean_obj_once(&lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___closed__0, &lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___closed__0_once, _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___closed__0);
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
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___boxed(lean_object* v_d_9_, lean_object* v_i_10_, lean_object* v_j_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0(v_d_9_, v_i_10_, v_j_11_);
lean_dec(v_j_11_);
return v_res_12_;
}
}
static lean_object* _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_mathlib_Equiv_refl___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg(lean_object* v_d_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; lean_object* v_toFun_18_; lean_object* v___f_19_; lean_object* v___x_20_; 
v___x_17_ = lean_obj_once(&lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___closed__0, &lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___closed__0_once, _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___closed__0);
v_toFun_18_ = lean_ctor_get(v___x_17_, 0);
v___f_19_ = lean_alloc_closure((void*)(lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_19_, 0, v_d_14_);
lean_inc(v_toFun_18_);
v___x_20_ = lean_apply_3(v_toFun_18_, v___f_19_, v_a_15_, v_a_16_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0(lean_object* v___x_21_, lean_object* v_d_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg(v_d_22_, v_a_23_, v_a_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___boxed(lean_object* v___x_26_, lean_object* v_d_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0(v___x_26_, v_d_27_, v_a_28_, v_a_29_);
lean_dec(v___x_26_);
return v_res_30_;
}
}
static lean_object* _init_lp_GRH_New_RealPlace_diagLast___lam__0___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_32_ = lp_mathlib_Complex_ofReal(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_diagLast___lam__0(lean_object* v_x_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&lp_GRH_New_RealPlace_diagLast___lam__0___closed__0, &lp_GRH_New_RealPlace_diagLast___lam__0___closed__0_once, _init_lp_GRH_New_RealPlace_diagLast___lam__0___closed__0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_diagLast___lam__0___boxed(lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_RealPlace_diagLast___lam__0(v_x_35_);
lean_dec(v_x_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_diagLast(lean_object* v_00_U0001d530_38_, lean_object* v_x_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_00_u03f1_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_00_u03f1_42_ = lean_ctor_get(v_00_U0001d530_38_, 0);
lean_inc(v_00_u03f1_42_);
lean_dec_ref(v_00_U0001d530_38_);
v___f_43_ = ((lean_object*)(lp_GRH_New_RealPlace_diagLast___closed__0));
v___x_44_ = lean_alloc_closure((void*)(lp_mathlib_Fin_snoc___boxed), 5, 4);
lean_closure_set(v___x_44_, 0, v_00_u03f1_42_);
lean_closure_set(v___x_44_, 1, lean_box(0));
lean_closure_set(v___x_44_, 2, v___f_43_);
lean_closure_set(v___x_44_, 3, v_x_39_);
v___x_45_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_diagLast_spec__0___redArg(v___x_44_, v_a_40_, v_a_41_);
return v___x_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Bessel_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Bessel_GramSection(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Analysis_HolomorphicIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Bessel_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
