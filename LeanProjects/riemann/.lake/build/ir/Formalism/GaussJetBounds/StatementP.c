// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementP
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementM
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
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_idM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg___lam__0(lean_object* v_N0_1_, lean_object* v_N1_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_5_, 0, v_N0_1_);
v___x_6_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_6_, 0, v_N1_2_);
v___x_7_ = l_instDecidableEqProd___redArg(v___x_5_, v___x_6_, v_a_3_, v_b_4_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg___lam__0___boxed(lean_object* v_N0_8_, lean_object* v_N1_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg___lam__0(v_N0_8_, v_N1_9_, v_a_10_, v_b_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg(lean_object* v_inst_14_, lean_object* v_d_15_, lean_object* v_N0_16_, lean_object* v_N1_17_, lean_object* v_x_18_, lean_object* v_y_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___f_20_ = lean_alloc_closure((void*)(lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_20_, 0, v_N0_16_);
lean_closure_set(v___f_20_, 1, v_N1_17_);
v___x_21_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_21_, 0, v_d_15_);
v___x_22_ = l_instDecidableEqProd___redArg(v___x_21_, v___f_20_, v_x_18_, v_y_19_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toSemiring_25_; lean_object* v___x_26_; lean_object* v_toZero_27_; 
v___x_23_ = lp_mathlib_Field_toSemifield___redArg(v_inst_14_);
lean_dec_ref(v_inst_14_);
v___x_24_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_23_);
v_toSemiring_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_toSemiring_25_);
lean_dec_ref(v___x_24_);
v___x_26_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_25_);
v_toZero_27_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_toZero_27_);
lean_dec_ref(v___x_26_);
return v_toZero_27_;
}
else
{
lean_object* v___x_28_; lean_object* v_toRing_29_; lean_object* v___x_30_; lean_object* v_toAddMonoidWithOne_31_; lean_object* v_toOne_32_; 
v___x_28_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_14_);
v_toRing_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc_ref(v_toRing_29_);
lean_dec_ref(v___x_28_);
v___x_30_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_29_);
v_toAddMonoidWithOne_31_ = lean_ctor_get(v___x_30_, 1);
lean_inc_ref(v_toAddMonoidWithOne_31_);
lean_dec_ref(v___x_30_);
v_toOne_32_ = lean_ctor_get(v_toAddMonoidWithOne_31_, 2);
lean_inc(v_toOne_32_);
lean_dec_ref(v_toAddMonoidWithOne_31_);
return v_toOne_32_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_idM(lean_object* v_K_33_, lean_object* v_inst_34_, lean_object* v_d_35_, lean_object* v_N0_36_, lean_object* v_N1_37_, lean_object* v_x_38_, lean_object* v_y_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_tree_Formalism_DworkPowerSeriesWeights_idM___redArg(v_inst_34_, v_d_35_, v_N0_36_, v_N1_37_, v_x_38_, v_y_39_);
return v___x_40_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
