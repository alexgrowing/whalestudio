// Lean compiler output
// Module: New.Congruences.Selmer.RootsOfUnity
// Imports: public import Init public meta import Init public import Lib.General.NumberTheory.GaussValuation
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_totient(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00instCommSemiringNNRat_spec__1(lean_object*);
lean_object* l_Rat_inv(lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Nat_cast___at___00New_Selmer_rootRadius_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rootRadius(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rootRadius___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_radiusExponents___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_radiusExponents___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_radiusExponents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_radiusExponents___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Nat_cast___at___00New_Selmer_rootRadius_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_Nat_cast___at___00instCommSemiringNNRat_spec__1(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rootRadius(lean_object* v_00_u2113_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_nat_pow(v_00_u2113_3_, v_h_4_);
v___x_6_ = lp_mathlib_Nat_totient(v___x_5_);
v___x_7_ = lp_mathlib_Nat_cast___at___00instCommSemiringNNRat_spec__1(v___x_6_);
v___x_8_ = l_Rat_inv(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_rootRadius___boxed(lean_object* v_00_u2113_9_, lean_object* v_h_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_New_Selmer_rootRadius(v_00_u2113_9_, v_h_10_);
lean_dec(v_h_10_);
lean_dec(v_00_u2113_9_);
return v_res_11_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Selmer_radiusExponents___lam__0(lean_object* v_00_u2113_12_, lean_object* v_00_u03c1_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lp_GRH_New_Selmer_rootRadius(v_00_u2113_12_, v_a_14_);
v___x_16_ = l_Rat_instDecidableLe(v___x_15_, v_00_u03c1_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_radiusExponents___lam__0___boxed(lean_object* v_00_u2113_17_, lean_object* v_00_u03c1_18_, lean_object* v_a_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = lp_GRH_New_Selmer_radiusExponents___lam__0(v_00_u2113_17_, v_00_u03c1_18_, v_a_19_);
lean_dec(v_a_19_);
lean_dec(v_00_u2113_17_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_radiusExponents(lean_object* v_00_u2113_22_, lean_object* v_00_u03c1_23_, lean_object* v_h_u2080_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_25_ = lean_alloc_closure((void*)(lp_GRH_New_Selmer_radiusExponents___lam__0___boxed), 3, 2);
lean_closure_set(v___f_25_, 0, v_00_u2113_22_);
lean_closure_set(v___f_25_, 1, v_00_u03c1_23_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lp_mathlib_Finset_Icc___at___00Nat_lcmUpto_spec__0(v___x_26_, v_h_u2080_24_);
v___x_28_ = lp_mathlib_Multiset_filter___redArg(v___f_25_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_radiusExponents___boxed(lean_object* v_00_u2113_29_, lean_object* v_00_u03c1_30_, lean_object* v_h_u2080_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_Selmer_radiusExponents(v_00_u2113_29_, v_00_u03c1_30_, v_h_u2080_31_);
lean_dec(v_h_u2080_31_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_GaussValuation(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Selmer_RootsOfUnity(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_NumberTheory_GaussValuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
