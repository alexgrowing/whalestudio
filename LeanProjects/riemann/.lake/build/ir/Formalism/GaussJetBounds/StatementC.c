// Lean compiler output
// Module: Formalism.GaussJetBounds.StatementC
// Imports: public import Init public meta import Init public import Formalism.GaussJetBounds.Statement
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM___redArg(lean_object* v_inst_1_, lean_object* v_d_2_, lean_object* v_x_3_, lean_object* v_z_4_, lean_object* v_y_5_){
_start:
{
lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v_fst_14_; lean_object* v_snd_15_; uint8_t v___x_16_; 
v_fst_12_ = lean_ctor_get(v_y_5_, 0);
lean_inc(v_fst_12_);
v_snd_13_ = lean_ctor_get(v_y_5_, 1);
lean_inc(v_snd_13_);
lean_dec_ref(v_y_5_);
v_fst_14_ = lean_ctor_get(v_z_4_, 0);
lean_inc(v_fst_14_);
v_snd_15_ = lean_ctor_get(v_z_4_, 1);
lean_inc(v_snd_15_);
lean_dec_ref(v_z_4_);
v___x_16_ = lp_mathlib_ZMod_decidableEq(v_d_2_, v_fst_12_, v_fst_14_);
lean_dec(v_fst_12_);
if (v___x_16_ == 0)
{
lean_dec(v_snd_15_);
lean_dec(v_fst_14_);
lean_dec(v_snd_13_);
lean_dec(v_x_3_);
goto v___jp_6_;
}
else
{
lean_object* v_fst_17_; lean_object* v_snd_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_36_; 
v_fst_17_ = lean_ctor_get(v_snd_13_, 0);
v_snd_18_ = lean_ctor_get(v_snd_13_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_snd_13_);
if (v_isSharedCheck_36_ == 0)
{
v___x_20_ = v_snd_13_;
v_isShared_21_ = v_isSharedCheck_36_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_snd_18_);
lean_inc(v_fst_17_);
lean_dec(v_snd_13_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_36_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_35_; 
v_fst_22_ = lean_ctor_get(v_snd_15_, 0);
v_snd_23_ = lean_ctor_get(v_snd_15_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_snd_15_);
if (v_isSharedCheck_35_ == 0)
{
v___x_25_ = v_snd_15_;
v_isShared_26_ = v_isSharedCheck_35_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_inc(v_fst_22_);
lean_dec(v_snd_15_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_35_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_snd_18_, v_snd_23_);
lean_dec(v_snd_23_);
lean_dec(v_snd_18_);
if (v___x_27_ == 0)
{
lean_del_object(v___x_25_);
lean_dec(v_fst_22_);
lean_del_object(v___x_20_);
lean_dec(v_fst_17_);
lean_dec(v_fst_14_);
lean_dec(v_x_3_);
goto v___jp_6_;
}
else
{
lean_object* v___x_29_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_fst_22_);
lean_ctor_set(v___x_25_, 0, v_fst_17_);
v___x_29_ = v___x_25_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_fst_17_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_fst_22_);
v___x_29_ = v_reuseFailAlloc_34_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_31_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___x_29_);
lean_ctor_set(v___x_20_, 0, v_fst_14_);
v___x_31_ = v___x_20_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_fst_14_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_33_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_1(v_x_3_, v___x_31_);
return v___x_32_;
}
}
}
}
}
}
v___jp_6_:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toSemiring_9_; lean_object* v___x_10_; lean_object* v_toZero_11_; 
v___x_7_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_8_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_7_);
v_toSemiring_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc_ref(v_toSemiring_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_9_);
v_toZero_11_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_toZero_11_);
lean_dec_ref(v___x_10_);
return v_toZero_11_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM___redArg___boxed(lean_object* v_inst_37_, lean_object* v_d_38_, lean_object* v_x_39_, lean_object* v_z_40_, lean_object* v_y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_DworkPowerSeriesWeights_frameM___redArg(v_inst_37_, v_d_38_, v_x_39_, v_z_40_, v_y_41_);
lean_dec(v_d_38_);
lean_dec_ref(v_inst_37_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM(lean_object* v_K_43_, lean_object* v_inst_44_, lean_object* v_d_45_, lean_object* v_N0_46_, lean_object* v_N1_47_, lean_object* v_x_48_, lean_object* v_z_49_, lean_object* v_y_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_DworkPowerSeriesWeights_frameM___redArg(v_inst_44_, v_d_45_, v_x_48_, v_z_49_, v_y_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DworkPowerSeriesWeights_frameM___boxed(lean_object* v_K_52_, lean_object* v_inst_53_, lean_object* v_d_54_, lean_object* v_N0_55_, lean_object* v_N1_56_, lean_object* v_x_57_, lean_object* v_z_58_, lean_object* v_y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_DworkPowerSeriesWeights_frameM(v_K_52_, v_inst_53_, v_d_54_, v_N0_55_, v_N1_56_, v_x_57_, v_z_58_, v_y_59_);
lean_dec(v_N1_56_);
lean_dec(v_N0_55_);
lean_dec(v_d_54_);
lean_dec_ref(v_inst_53_);
return v_res_60_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GaussJetBounds_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaussJetBounds_StatementC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GaussJetBounds_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
