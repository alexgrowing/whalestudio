// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementM
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.StatementK
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___redArg(lean_object* v_inst_1_, lean_object* v_d_2_, lean_object* v_TT_3_, lean_object* v_l_4_, lean_object* v_m_5_, lean_object* v_Y_6_, lean_object* v_y_7_){
_start:
{
lean_object* v_fst_8_; lean_object* v_snd_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_fst_8_ = lean_ctor_get(v_y_7_, 0);
v_snd_9_ = lean_ctor_get(v_y_7_, 1);
v___x_10_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_10_, 0, v_d_2_);
lean_inc(v_fst_8_);
v___x_11_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_10_, v_fst_8_, v_TT_3_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_1(v_Y_6_, v_y_7_);
return v___x_12_;
}
else
{
lean_object* v_fst_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_fst_13_ = lean_ctor_get(v_snd_9_, 0);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_dec_eq(v_fst_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_1(v_Y_6_, v_y_7_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toSemiring_19_; lean_object* v_toMonoid_20_; lean_object* v_toNPow_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_17_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_18_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_17_);
v_toSemiring_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_toSemiring_19_);
lean_dec_ref(v___x_18_);
v_toMonoid_20_ = lean_ctor_get(v_toSemiring_19_, 1);
lean_inc_ref(v_toMonoid_20_);
lean_dec_ref(v_toSemiring_19_);
v_toNPow_21_ = lean_ctor_get(v_toMonoid_20_, 2);
lean_inc(v_toNPow_21_);
lean_dec_ref(v_toMonoid_20_);
v___x_22_ = lean_apply_1(v_Y_6_, v_y_7_);
v___x_23_ = lean_nat_pow(v_l_4_, v_m_5_);
v___x_24_ = lean_apply_2(v_toNPow_21_, v___x_23_, v___x_22_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___redArg___boxed(lean_object* v_inst_25_, lean_object* v_d_26_, lean_object* v_TT_27_, lean_object* v_l_28_, lean_object* v_m_29_, lean_object* v_Y_30_, lean_object* v_y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___redArg(v_inst_25_, v_d_26_, v_TT_27_, v_l_28_, v_m_29_, v_Y_30_, v_y_31_);
lean_dec(v_m_29_);
lean_dec(v_l_28_);
lean_dec_ref(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame(lean_object* v_K_33_, lean_object* v_inst_34_, lean_object* v_d_35_, lean_object* v_N0_36_, lean_object* v_TT_37_, lean_object* v_l_38_, lean_object* v_m_39_, lean_object* v_Y_40_, lean_object* v_y_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___redArg(v_inst_34_, v_d_35_, v_TT_37_, v_l_38_, v_m_39_, v_Y_40_, v_y_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_genFrame___boxed(lean_object* v_K_43_, lean_object* v_inst_44_, lean_object* v_d_45_, lean_object* v_N0_46_, lean_object* v_TT_47_, lean_object* v_l_48_, lean_object* v_m_49_, lean_object* v_Y_50_, lean_object* v_y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_tree_Formalism_DworkPowerSeriesWeights_genFrame(v_K_43_, v_inst_44_, v_d_45_, v_N0_46_, v_TT_47_, v_l_48_, v_m_49_, v_Y_50_, v_y_51_);
lean_dec(v_m_49_);
lean_dec(v_l_48_);
lean_dec(v_N0_46_);
lean_dec_ref(v_inst_44_);
return v_res_52_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_StatementK(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_StatementK(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
