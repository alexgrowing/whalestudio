// Lean compiler output
// Module: Formalism.CyclotomicNorms.NonsquarefreeBounds.TwoMulNumDerangementsLeFactorial
// Imports: public import Init public meta import Init public import Formalism.CyclotomicNorms.DiscardKernel
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
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_powersetCard___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__0(lean_object* v_00_u03c3_1_, lean_object* v_N_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v_toFun_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
v_toFun_5_ = lean_ctor_get(v_00_u03c3_1_, 0);
lean_inc(v_toFun_5_);
lean_dec_ref(v_00_u03c3_1_);
v___x_6_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_6_, 0, v_N_2_);
lean_inc(v_a_4_);
v___x_7_ = lean_apply_1(v_toFun_5_, v_a_4_);
lean_inc(v_a_3_);
lean_inc_ref(v___x_6_);
v___x_8_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_6_, v___x_7_, v_a_3_);
v___x_9_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_6_, v_a_4_, v_a_3_);
if (v___x_8_ == 0)
{
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 1;
return v___x_10_;
}
else
{
return v___x_8_;
}
}
else
{
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__0___boxed(lean_object* v_00_u03c3_11_, lean_object* v_N_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__0(v_00_u03c3_11_, v_N_12_, v_a_13_, v_a_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__1(lean_object* v_00_u03c3_17_, lean_object* v_N_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___f_20_; uint8_t v___x_21_; 
lean_inc(v_N_18_);
v___f_20_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_20_, 0, v_00_u03c3_17_);
lean_closure_set(v___f_20_, 1, v_N_18_);
lean_closure_set(v___f_20_, 2, v_a_19_);
v___x_21_ = l_Nat_decidableForallFin___redArg(v_N_18_, v___f_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__1___boxed(lean_object* v_00_u03c3_22_, lean_object* v_N_23_, lean_object* v_a_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__1(v_00_u03c3_22_, v_N_23_, v_a_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv(lean_object* v_N_27_, lean_object* v_a_28_, lean_object* v_00_u03c3_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc(v_N_27_);
v___f_30_ = lean_alloc_closure((void*)(lp_tree_Formalism_CyclotomicNorms_PermutationFixedPoints_numInv___lam__1___boxed), 3, 2);
lean_closure_set(v___f_30_, 0, v_00_u03c3_29_);
lean_closure_set(v___f_30_, 1, v_N_27_);
v___x_31_ = l_List_finRange(v_N_27_);
v___x_32_ = lp_mathlib_Finset_powersetCard___redArg(v_a_28_, v___x_31_);
v___x_33_ = lp_mathlib_Multiset_filter___redArg(v___f_30_, v___x_32_);
v___x_34_ = l_List_lengthTR___redArg(v___x_33_);
lean_dec(v___x_33_);
return v___x_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_DiscardKernel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_DiscardKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
