// Lean compiler output
// Module: Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
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
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_00_u03c7_u2088___lam__0(lean_object*);
static lean_once_cell_t lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__0;
static lean_once_cell_t lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_QuadraticZeta_kroneckerAt(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(8u);
v___x_2_ = lp_mathlib_ZMod_commRing(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__0, &lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__0_once, _init_lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__0);
v___x_4_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_toIntCast_7_; lean_object* v___x_8_; 
v___x_6_ = lean_obj_once(&lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__1, &lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__1_once, _init_lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0___closed__1);
v_toIntCast_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_toIntCast_7_);
v___x_8_ = lean_apply_1(v_toIntCast_7_, v_a_5_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_QuadraticZeta_kroneckerAt(lean_object* v_D_9_, lean_object* v_p_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(2u);
v___x_12_ = lean_nat_dec_eq(v_p_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
v___x_13_ = lp_mathlib___private_Mathlib_NumberTheory_LegendreSymbol_JacobiSymbol_0__fastJacobiSym(v_D_9_, v_p_10_);
lean_dec(v_D_9_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_p_10_);
v___x_14_ = lp_tree_Int_cast___at___00GlobalTheory_QuadraticZeta_kroneckerAt_spec__0(v_D_9_);
v___x_15_ = lp_mathlib_ZMod_00_u03c7_u2088___lam__0(v___x_14_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr(uint8_t builtin) {
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
