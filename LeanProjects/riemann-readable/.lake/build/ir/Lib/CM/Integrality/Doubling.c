// Lean compiler output
// Module: Lib.CM.Integrality.Doubling
// Imports: public import Init public meta import Init public import Lib.CM.Sigma.ThetaSections public import Lib.General.Algebra.IntegralPowerSeries
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_doublingForms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_doublingForms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_doublingForms___redArg(lean_object* v_inst_1_, lean_object* v_c_2_, lean_object* v_w_3_){
_start:
{
lean_object* v_toSemiring_4_; lean_object* v_toMonoid_5_; lean_object* v_toNPow_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_toSub_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_39_; 
v_toSemiring_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toSemiring_4_);
v_toMonoid_5_ = lean_ctor_get(v_toSemiring_4_, 1);
v_toNPow_6_ = lean_ctor_get(v_toMonoid_5_, 2);
lean_inc(v_toNPow_6_);
v___x_7_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_1_);
v___x_8_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_7_);
v_toSub_9_ = lean_ctor_get(v___x_8_, 2);
lean_inc(v_toSub_9_);
lean_dec_ref(v___x_8_);
v_fst_10_ = lean_ctor_get(v_w_3_, 0);
v_snd_11_ = lean_ctor_get(v_w_3_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v_w_3_);
if (v_isSharedCheck_39_ == 0)
{
v___x_13_ = v_w_3_;
v_isShared_14_ = v_isSharedCheck_39_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_snd_11_);
lean_inc(v_fst_10_);
lean_dec(v_w_3_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_39_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_toAddMonoidWithOne_18_; lean_object* v_toMul_19_; lean_object* v_toAdd_20_; lean_object* v_toNatCast_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_15_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_toNPow_6_, 3);
lean_inc_n(v_fst_10_, 2);
v___x_16_ = lean_apply_2(v_toNPow_6_, v___x_15_, v_fst_10_);
v___x_17_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_4_);
v_toAddMonoidWithOne_18_ = lean_ctor_get(v___x_7_, 1);
lean_inc_ref(v_toAddMonoidWithOne_18_);
lean_dec_ref(v___x_7_);
v_toMul_19_ = lean_ctor_get(v___x_17_, 0);
lean_inc_n(v_toMul_19_, 6);
v_toAdd_20_ = lean_ctor_get(v___x_17_, 1);
lean_inc_n(v_toAdd_20_, 2);
lean_dec_ref(v___x_17_);
v_toNatCast_21_ = lean_ctor_get(v_toAddMonoidWithOne_18_, 0);
lean_inc(v_toNatCast_21_);
lean_dec_ref(v_toAddMonoidWithOne_18_);
lean_inc_n(v_snd_11_, 2);
v___x_22_ = lean_apply_2(v_toNPow_6_, v___x_15_, v_snd_11_);
lean_inc(v___x_22_);
lean_inc(v___x_16_);
v___x_23_ = lean_apply_2(v_toSub_9_, v___x_16_, v___x_22_);
v___x_24_ = lean_apply_2(v_toNPow_6_, v___x_15_, v___x_23_);
v___x_25_ = lean_apply_2(v_toMul_19_, v_fst_10_, v_snd_11_);
v___x_26_ = lean_unsigned_to_nat(4u);
v___x_27_ = lean_apply_1(v_toNatCast_21_, v___x_26_);
lean_inc(v___x_27_);
v___x_28_ = lean_apply_2(v_toMul_19_, v___x_27_, v___x_16_);
v___x_29_ = lean_apply_2(v_toNPow_6_, v___x_15_, v_c_2_);
v___x_30_ = lean_apply_2(v_toMul_19_, v___x_29_, v_fst_10_);
v___x_31_ = lean_apply_2(v_toMul_19_, v___x_30_, v_snd_11_);
v___x_32_ = lean_apply_2(v_toAdd_20_, v___x_28_, v___x_31_);
v___x_33_ = lean_apply_2(v_toMul_19_, v___x_27_, v___x_22_);
v___x_34_ = lean_apply_2(v_toAdd_20_, v___x_32_, v___x_33_);
v___x_35_ = lean_apply_2(v_toMul_19_, v___x_25_, v___x_34_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_35_);
lean_ctor_set(v___x_13_, 0, v___x_24_);
v___x_37_ = v___x_13_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_doublingForms(lean_object* v_R_40_, lean_object* v_inst_41_, lean_object* v_c_42_, lean_object* v_w_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_GRH_New_doublingForms___redArg(v_inst_41_, v_c_42_, v_w_43_);
return v___x_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_CM_Sigma_ThetaSections(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_IntegralPowerSeries(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_CM_Integrality_Doubling(uint8_t builtin) {
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
res = initialize_GRH_Lib_CM_Sigma_ThetaSections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_IntegralPowerSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
