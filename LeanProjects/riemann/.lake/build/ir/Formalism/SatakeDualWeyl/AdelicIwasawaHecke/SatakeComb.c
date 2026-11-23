// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
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
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_UG_P_satakeInv___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_UG_P_satakeInv___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v_toDecidableEq_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_toDecidableEq_4_ = lean_ctor_get(v_inst_1_, 5);
lean_inc_ref(v_toDecidableEq_4_);
lean_dec_ref(v_inst_1_);
v___x_5_ = lean_apply_2(v_toDecidableEq_4_, v_a_2_, v_b_3_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_tree_Formalism_UG_P_satakeInv___redArg___lam__0(v_inst_7_, v_a_8_, v_b_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv___redArg___lam__1(lean_object* v_inst_12_, lean_object* v___f_13_, lean_object* v_s_14_, lean_object* v_S_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_toDecidableLT_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_toDecidableLT_17_ = lean_ctor_get(v_inst_12_, 6);
lean_inc_ref(v_toDecidableLT_17_);
lean_dec_ref(v_inst_12_);
v___x_18_ = lean_apply_1(v_toDecidableLT_17_, v_a_16_);
v___x_19_ = lp_mathlib_Multiset_sub___redArg(v___f_13_, v_s_14_, v_S_15_);
v___x_20_ = lp_mathlib_Multiset_filter___redArg(v___x_18_, v___x_19_);
v___x_21_ = l_List_lengthTR___redArg(v___x_20_);
lean_dec(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv___redArg(lean_object* v_inst_22_, lean_object* v_s_23_, lean_object* v_S_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_inc_ref(v_inst_22_);
v___f_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeInv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_25_, 0, v_inst_22_);
lean_inc(v_S_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_satakeInv___redArg___lam__1), 5, 4);
lean_closure_set(v___f_26_, 0, v_inst_22_);
lean_closure_set(v___f_26_, 1, v___f_25_);
lean_closure_set(v___f_26_, 2, v_s_23_);
lean_closure_set(v___f_26_, 3, v_S_24_);
v___x_27_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_28_ = lp_mathlib_Finset_sum___redArg(v___x_27_, v_S_24_, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_satakeInv(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_s_31_, lean_object* v_S_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_UG_P_satakeInv___redArg(v_inst_30_, v_s_31_, v_S_32_);
return v___x_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb(uint8_t builtin) {
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
