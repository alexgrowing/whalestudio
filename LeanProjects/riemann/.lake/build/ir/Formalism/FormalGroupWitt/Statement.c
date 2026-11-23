// Lean compiler output
// Module: Formalism.FormalGroupWitt.Statement
// Imports: public import Init public meta import Init public import Formalism.TorsionNormIteration.InvIntegralOfClass
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
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat___redArg(lean_object* v_inst_1_, lean_object* v_m_2_, lean_object* v_j_3_, lean_object* v_k_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toAddMonoidWithOne_8_; lean_object* v_toSub_9_; lean_object* v_toOne_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
lean_inc(v_m_2_);
v___x_5_ = lp_mathlib_ZMod_commRing(v_m_2_);
v___x_6_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_5_);
v___x_7_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_6_);
v_toAddMonoidWithOne_8_ = lean_ctor_get(v___x_6_, 1);
lean_inc_ref(v_toAddMonoidWithOne_8_);
lean_dec_ref(v___x_6_);
v_toSub_9_ = lean_ctor_get(v___x_7_, 2);
lean_inc(v_toSub_9_);
lean_dec_ref(v___x_7_);
v_toOne_10_ = lean_ctor_get(v_toAddMonoidWithOne_8_, 2);
lean_inc(v_toOne_10_);
lean_dec_ref(v_toAddMonoidWithOne_8_);
v___x_11_ = lean_apply_2(v_toSub_9_, v_j_3_, v_toOne_10_);
v___x_12_ = lp_mathlib_ZMod_decidableEq(v_m_2_, v_k_4_, v___x_11_);
lean_dec(v___x_11_);
lean_dec(v_m_2_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v_toSemiring_15_; lean_object* v___x_16_; lean_object* v_toZero_17_; 
v___x_13_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
lean_dec_ref(v_inst_1_);
v___x_14_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_13_);
v_toSemiring_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref(v_toSemiring_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_15_);
v_toZero_17_ = lean_ctor_get(v___x_16_, 1);
lean_inc(v_toZero_17_);
lean_dec_ref(v___x_16_);
return v_toZero_17_;
}
else
{
lean_object* v___x_18_; lean_object* v_toRing_19_; lean_object* v___x_20_; lean_object* v_toAddMonoidWithOne_21_; lean_object* v_toOne_22_; 
v___x_18_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v_toRing_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_ref(v_toRing_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_19_);
v_toAddMonoidWithOne_21_ = lean_ctor_get(v___x_20_, 1);
lean_inc_ref(v_toAddMonoidWithOne_21_);
lean_dec_ref(v___x_20_);
v_toOne_22_ = lean_ctor_get(v_toAddMonoidWithOne_21_, 2);
lean_inc(v_toOne_22_);
lean_dec_ref(v_toAddMonoidWithOne_21_);
return v_toOne_22_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat___redArg___boxed(lean_object* v_inst_23_, lean_object* v_m_24_, lean_object* v_j_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_FG_shiftMat___redArg(v_inst_23_, v_m_24_, v_j_25_, v_k_26_);
lean_dec(v_k_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat(lean_object* v_K_28_, lean_object* v_inst_29_, lean_object* v_m_30_, lean_object* v_j_31_, lean_object* v_k_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_FG_shiftMat___redArg(v_inst_29_, v_m_30_, v_j_31_, v_k_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_FG_shiftMat___boxed(lean_object* v_K_34_, lean_object* v_inst_35_, lean_object* v_m_36_, lean_object* v_j_37_, lean_object* v_k_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_FG_shiftMat(v_K_34_, v_inst_35_, v_m_36_, v_j_37_, v_k_38_);
lean_dec(v_k_38_);
return v_res_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_TorsionNormIteration_InvIntegralOfClass(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FormalGroupWitt_Statement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_TorsionNormIteration_InvIntegralOfClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
