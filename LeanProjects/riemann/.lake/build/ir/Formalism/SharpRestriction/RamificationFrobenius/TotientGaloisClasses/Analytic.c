// Lean compiler output
// Module: Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
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
lean_object* lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0___lam__0(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_chQ(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HC_Frame_psC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_psC___closed__0;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_psC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_psC___closed__1;
static lean_once_cell_t lp_tree_Formalism_HC_Frame_psC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HC_Frame_psC___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_psC(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_psC___boxed(lean_object*);
static lean_object* _init_lp_tree_Formalism_HC_Frame_psC___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Complex_commRing;
v___x_2_ = lp_mathlib_Ring_toNonAssocRing___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_psC___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_psC___closed__0, &lp_tree_Formalism_HC_Frame_psC___closed__0_once, _init_lp_tree_Formalism_HC_Frame_psC___closed__0);
v___x_4_ = lp_mathlib_Int_castRingHom___redArg(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_HC_Frame_psC___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___f_6_; 
v___x_5_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_psC___closed__1, &lp_tree_Formalism_HC_Frame_psC___closed__1_once, _init_lp_tree_Formalism_HC_Frame_psC___closed__1);
v___f_6_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_HC_Frame_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_psC(lean_object* v_00_u03c6_7_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_9_; lean_object* v___f_10_; 
v___f_8_ = lean_obj_once(&lp_tree_Formalism_HC_Frame_psC___closed__2, &lp_tree_Formalism_HC_Frame_psC___closed__2_once, _init_lp_tree_Formalism_HC_Frame_psC___closed__2);
v___x_9_ = lp_tree_Formalism_HC_Frame_chQ(v_00_u03c6_7_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_9_);
lean_closure_set(v___f_10_, 1, v___f_8_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HC_Frame_psC___boxed(lean_object* v_00_u03c6_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_HC_Frame_psC(v_00_u03c6_11_);
lean_dec_ref(v_00_u03c6_11_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
