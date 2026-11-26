// Lean compiler output
// Module: Lib.CM.Integrality.LogTheta
// Imports: public import Init public meta import Init public import Lib.CM.Integrality.IsogenyIntegrality public import Lib.General.Algebra.SeriesBounds public import Lib.General.NumberTheory.PadicLimitsValuation
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_eulerAddition___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_eulerAddition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_eulerAddition___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_x_u2080_3_, lean_object* v_y_u2080_4_, lean_object* v_x_u2081_5_, lean_object* v_y_u2081_6_, lean_object* v_u_7_){
_start:
{
lean_object* v_toSemiring_8_; lean_object* v___x_9_; lean_object* v_toMonoid_10_; lean_object* v_toMul_11_; lean_object* v_toAdd_12_; lean_object* v_toNPow_13_; lean_object* v___x_14_; lean_object* v_toAddMonoidWithOne_15_; lean_object* v_toNatCast_16_; lean_object* v_toOne_17_; lean_object* v___x_18_; lean_object* v_toSub_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_toSemiring_8_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_8_);
v___x_9_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_8_);
v_toMonoid_10_ = lean_ctor_get(v_toSemiring_8_, 1);
v_toMul_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_n(v_toMul_11_, 13);
v_toAdd_12_ = lean_ctor_get(v___x_9_, 1);
lean_inc_n(v_toAdd_12_, 9);
lean_dec_ref(v___x_9_);
v_toNPow_13_ = lean_ctor_get(v_toMonoid_10_, 2);
lean_inc_n(v_toNPow_13_, 3);
v___x_14_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v_toAddMonoidWithOne_15_ = lean_ctor_get(v___x_14_, 1);
lean_inc_ref(v_toAddMonoidWithOne_15_);
v_toNatCast_16_ = lean_ctor_get(v_toAddMonoidWithOne_15_, 0);
lean_inc(v_toNatCast_16_);
v_toOne_17_ = lean_ctor_get(v_toAddMonoidWithOne_15_, 2);
lean_inc_n(v_toOne_17_, 2);
lean_dec_ref(v_toAddMonoidWithOne_15_);
v___x_18_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_14_);
lean_dec_ref(v___x_14_);
v_toSub_19_ = lean_ctor_get(v___x_18_, 2);
lean_inc(v_toSub_19_);
lean_dec_ref(v___x_18_);
lean_inc_n(v_x_u2081_5_, 2);
lean_inc_n(v_x_u2080_3_, 2);
v___x_20_ = lean_apply_2(v_toMul_11_, v_x_u2080_3_, v_x_u2081_5_);
lean_inc(v_u_7_);
lean_inc_n(v___x_20_, 4);
v___x_21_ = lean_apply_2(v_toMul_11_, v___x_20_, v_u_7_);
v___x_22_ = lean_apply_2(v_toAdd_12_, v_toOne_17_, v___x_21_);
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lean_apply_2(v_toNPow_13_, v___x_23_, v___x_22_);
v___x_25_ = lean_apply_2(v_toAdd_12_, v_toOne_17_, v___x_20_);
lean_inc_n(v_y_u2081_6_, 2);
lean_inc_n(v_y_u2080_4_, 2);
v___x_26_ = lean_apply_2(v_toAdd_12_, v_y_u2080_4_, v_y_u2081_6_);
v___x_27_ = lean_apply_2(v_toMul_11_, v___x_25_, v___x_26_);
v___x_28_ = lean_apply_2(v_toMul_11_, v_y_u2080_4_, v_y_u2081_6_);
lean_inc_n(v_a_2_, 2);
v___x_29_ = lean_apply_2(v_toMul_11_, v_a_2_, v___x_28_);
v___x_30_ = lean_apply_2(v_toSub_19_, v___x_27_, v___x_29_);
v___x_31_ = lean_apply_2(v_toMul_11_, v___x_24_, v___x_30_);
v___x_32_ = lean_unsigned_to_nat(3u);
v___x_33_ = lean_apply_2(v_toNPow_13_, v___x_32_, v_u_7_);
v___x_34_ = lean_apply_1(v_toNatCast_16_, v___x_32_);
v___x_35_ = lean_apply_2(v_toAdd_12_, v___x_34_, v___x_20_);
v___x_36_ = lean_apply_2(v_toAdd_12_, v_x_u2080_3_, v_x_u2081_5_);
v___x_37_ = lean_apply_2(v_toMul_11_, v___x_35_, v___x_36_);
v___x_38_ = lean_apply_2(v_toNPow_13_, v___x_23_, v_a_2_);
v___x_39_ = lean_apply_2(v_toMul_11_, v___x_38_, v___x_20_);
v___x_40_ = lean_apply_2(v_toAdd_12_, v___x_37_, v___x_39_);
v___x_41_ = lean_apply_2(v_toMul_11_, v___x_33_, v___x_40_);
v___x_42_ = lean_apply_2(v_toMul_11_, v_x_u2080_3_, v_y_u2081_6_);
v___x_43_ = lean_apply_2(v_toMul_11_, v_x_u2081_5_, v_y_u2080_4_);
v___x_44_ = lean_apply_2(v_toAdd_12_, v___x_42_, v___x_43_);
v___x_45_ = lean_apply_2(v_toMul_11_, v_a_2_, v___x_20_);
v___x_46_ = lean_apply_2(v_toAdd_12_, v___x_44_, v___x_45_);
v___x_47_ = lean_apply_2(v_toMul_11_, v___x_41_, v___x_46_);
v___x_48_ = lean_apply_2(v_toAdd_12_, v___x_31_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_eulerAddition(lean_object* v_A_49_, lean_object* v_inst_50_, lean_object* v_a_51_, lean_object* v_x_u2080_52_, lean_object* v_y_u2080_53_, lean_object* v_x_u2081_54_, lean_object* v_y_u2081_55_, lean_object* v_u_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_GRH_New_eulerAddition___redArg(v_inst_50_, v_a_51_, v_x_u2080_52_, v_y_u2080_53_, v_x_u2081_54_, v_y_u2081_55_, v_u_56_);
return v___x_57_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_Integrality_IsogenyIntegrality(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_SeriesBounds(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_PadicLimitsValuation(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_CM_Integrality_LogTheta(uint8_t builtin) {
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
res = initialize_GRH_Lib_CM_Integrality_IsogenyIntegrality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_SeriesBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_NumberTheory_PadicLimitsValuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
