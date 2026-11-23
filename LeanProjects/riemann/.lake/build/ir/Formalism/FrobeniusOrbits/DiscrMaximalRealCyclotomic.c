// Lean compiler output
// Module: Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
// Imports: public import Init public meta import Init public import Formalism.FrobeniusOrbits.Statement
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
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* lp_tree_Formalism_FrobeniusOrbits_chD(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0(lean_object*);
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_chC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_chC___closed__0;
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_chC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_chC___closed__1;
static lean_once_cell_t lp_tree_Formalism_FrobeniusOrbits_chC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_FrobeniusOrbits_chC___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_chC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_chC___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0(lean_object* v_f_1_, lean_object* v_u_2_){
_start:
{
lean_object* v_val_3_; lean_object* v_inv_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_13_; 
v_val_3_ = lean_ctor_get(v_u_2_, 0);
v_inv_4_ = lean_ctor_get(v_u_2_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v_u_2_);
if (v_isSharedCheck_13_ == 0)
{
v___x_6_ = v_u_2_;
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_inv_4_);
lean_inc(v_val_3_);
lean_dec(v_u_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
lean_inc_ref(v_f_1_);
v___x_8_ = lean_apply_1(v_f_1_, v_val_3_);
v___x_9_ = lean_apply_1(v_f_1_, v_inv_4_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_9_);
lean_ctor_set(v___x_6_, 0, v___x_8_);
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_8_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0(lean_object* v_f_14_){
_start:
{
lean_object* v___f_15_; 
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_15_, 0, v_f_14_);
return v___f_15_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_chC___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lp_mathlib_Complex_commRing;
v___x_17_ = lp_mathlib_Ring_toNonAssocRing___redArg(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_chC___closed__1(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_chC___closed__0, &lp_tree_Formalism_FrobeniusOrbits_chC___closed__0_once, _init_lp_tree_Formalism_FrobeniusOrbits_chC___closed__0);
v___x_19_ = lp_mathlib_Int_castRingHom___redArg(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_lp_tree_Formalism_FrobeniusOrbits_chC___closed__2(void){
_start:
{
lean_object* v___x_20_; lean_object* v___f_21_; 
v___x_20_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_chC___closed__1, &lp_tree_Formalism_FrobeniusOrbits_chC___closed__1_once, _init_lp_tree_Formalism_FrobeniusOrbits_chC___closed__1);
v___f_21_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_21_, 0, v___x_20_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_chC(lean_object* v_e_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; 
v___f_23_ = lean_obj_once(&lp_tree_Formalism_FrobeniusOrbits_chC___closed__2, &lp_tree_Formalism_FrobeniusOrbits_chC___closed__2_once, _init_lp_tree_Formalism_FrobeniusOrbits_chC___closed__2);
v___x_24_ = lp_tree_Formalism_FrobeniusOrbits_chD(v_e_22_);
v___f_25_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_25_, 0, v___x_24_);
lean_closure_set(v___f_25_, 1, v___f_23_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FrobeniusOrbits_chC___boxed(lean_object* v_e_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_FrobeniusOrbits_chC(v_e_26_);
lean_dec(v_e_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___redArg(lean_object* v_f_28_){
_start:
{
lean_inc_ref(v_f_28_);
return v_f_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___redArg___boxed(lean_object* v_f_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___redArg(v_f_29_);
lean_dec_ref(v_f_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0(lean_object* v_f_31_, lean_object* v_map__mul_32_){
_start:
{
lean_inc_ref(v_f_31_);
return v_f_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0___boxed(lean_object* v_f_33_, lean_object* v_map__mul_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_MonoidHom_mk_x27___at___00Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0_spec__0(v_f_33_, v_map__mul_34_);
lean_dec_ref(v_f_33_);
return v_res_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_FrobeniusOrbits_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_FrobeniusOrbits_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
