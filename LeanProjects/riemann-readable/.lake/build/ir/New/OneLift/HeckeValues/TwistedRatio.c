// Lean compiler output
// Module: New.OneLift.HeckeValues.TwistedRatio
// Imports: public import Init public meta import Init public import Lib.SiegelWeil.Tower.FiniteTateIntegral public import New.Determinant.Twist.FitTwists
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_CriticalPair_lowerPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_CriticalPair_lowerPoint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_CriticalPair_lowerPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_CriticalPair_lowerPoint___redArg(lean_object* v_p_1_, lean_object* v_z_2_){
_start:
{
lean_object* v_character_3_; lean_object* v_negWeight_4_; lean_object* v_tamePart_5_; lean_object* v_z_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_21_; 
v_character_3_ = lean_ctor_get(v_p_1_, 0);
v_negWeight_4_ = lean_ctor_get(v_p_1_, 1);
v_tamePart_5_ = lean_ctor_get(v_p_1_, 2);
v_z_6_ = lean_ctor_get(v_p_1_, 3);
v_isSharedCheck_21_ = !lean_is_exclusive(v_p_1_);
if (v_isSharedCheck_21_ == 0)
{
v___x_8_ = v_p_1_;
v_isShared_9_ = v_isSharedCheck_21_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_z_6_);
lean_inc(v_tamePart_5_);
lean_inc(v_negWeight_4_);
lean_inc(v_character_3_);
lean_dec(v_p_1_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_21_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___y_12_; uint8_t v___x_20_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_20_ = lean_nat_dec_le(v_z_2_, v_z_6_);
if (v___x_20_ == 0)
{
lean_dec(v_z_2_);
v___y_12_ = v_z_6_;
goto v___jp_11_;
}
else
{
lean_dec(v_z_6_);
v___y_12_ = v_z_2_;
goto v___jp_11_;
}
v___jp_11_:
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_le(v___x_10_, v___y_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_15_; 
lean_dec(v___y_12_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 3, v___x_10_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_character_3_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_negWeight_4_);
lean_ctor_set(v_reuseFailAlloc_16_, 2, v_tamePart_5_);
lean_ctor_set(v_reuseFailAlloc_16_, 3, v___x_10_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 3, v___y_12_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_character_3_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_negWeight_4_);
lean_ctor_set(v_reuseFailAlloc_19_, 2, v_tamePart_5_);
lean_ctor_set(v_reuseFailAlloc_19_, 3, v___y_12_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_CriticalPair_lowerPoint(lean_object* v_P_22_, lean_object* v_D_23_, lean_object* v_p_24_, lean_object* v_z_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_GRH_New_Data_CriticalPair_lowerPoint___redArg(v_p_24_, v_z_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_CriticalPair_lowerPoint___boxed(lean_object* v_P_27_, lean_object* v_D_28_, lean_object* v_p_29_, lean_object* v_z_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_GRH_New_Data_CriticalPair_lowerPoint(v_P_27_, v_D_28_, v_p_29_, v_z_30_);
lean_dec_ref(v_D_28_);
lean_dec_ref(v_P_27_);
return v_res_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_FiniteTateIntegral(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Twist_FitTwists(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_OneLift_HeckeValues_TwistedRatio(uint8_t builtin) {
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
res = initialize_GRH_Lib_SiegelWeil_Tower_FiniteTateIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Twist_FitTwists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
