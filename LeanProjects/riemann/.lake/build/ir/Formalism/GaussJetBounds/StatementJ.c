// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementJ
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementI
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
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat___redArg(lean_object* v_inst_1_, lean_object* v_d_2_, lean_object* v_TT_3_, lean_object* v_T_4_, lean_object* v_s_5_, lean_object* v_i_6_, lean_object* v_k_7_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_8_, 0, v_d_2_);
lean_inc(v_s_5_);
v___x_9_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_8_, v_s_5_, v_TT_3_);
if (v___x_9_ == 0)
{
goto v___jp_10_;
}
else
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_nat_dec_eq(v_i_6_, v___x_20_);
if (v___x_21_ == 0)
{
goto v___jp_10_;
}
else
{
uint8_t v___x_22_; 
lean_dec(v_s_5_);
lean_dec(v_T_4_);
v___x_22_ = lean_nat_dec_eq(v_k_7_, v_i_6_);
lean_dec(v_i_6_);
lean_dec(v_k_7_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toSemiring_25_; lean_object* v___x_26_; lean_object* v_toZero_27_; 
v___x_23_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
lean_dec_ref(v_inst_1_);
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
v___x_28_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
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
v___jp_10_:
{
if (v___x_9_ == 0)
{
lean_object* v___x_11_; 
lean_dec_ref(v_inst_1_);
v___x_11_ = lean_apply_3(v_T_4_, v_s_5_, v_i_6_, v_k_7_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_nat_dec_eq(v_k_7_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec_ref(v_inst_1_);
v___x_14_ = lean_apply_3(v_T_4_, v_s_5_, v_i_6_, v_k_7_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v_toSemiring_17_; lean_object* v___x_18_; lean_object* v_toZero_19_; 
lean_dec(v_k_7_);
lean_dec(v_i_6_);
lean_dec(v_s_5_);
lean_dec(v_T_4_);
v___x_15_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
lean_dec_ref(v_inst_1_);
v___x_16_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_15_);
v_toSemiring_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_toSemiring_17_);
lean_dec_ref(v___x_16_);
v___x_18_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_17_);
v_toZero_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_toZero_19_);
lean_dec_ref(v___x_18_);
return v_toZero_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat(lean_object* v_K_33_, lean_object* v_inst_34_, lean_object* v_d_35_, lean_object* v_N0_36_, lean_object* v_TT_37_, lean_object* v_T_38_, lean_object* v_s_39_, lean_object* v_i_40_, lean_object* v_k_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_DworkPowerSeriesWeights_effMat___redArg(v_inst_34_, v_d_35_, v_TT_37_, v_T_38_, v_s_39_, v_i_40_, v_k_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_effMat___boxed(lean_object* v_K_43_, lean_object* v_inst_44_, lean_object* v_d_45_, lean_object* v_N0_46_, lean_object* v_TT_47_, lean_object* v_T_48_, lean_object* v_s_49_, lean_object* v_i_50_, lean_object* v_k_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_tree_Formalism_DworkPowerSeriesWeights_effMat(v_K_43_, v_inst_44_, v_d_45_, v_N0_46_, v_TT_47_, v_T_48_, v_s_49_, v_i_50_, v_k_51_);
lean_dec(v_N0_46_);
return v_res_52_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementJ(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
