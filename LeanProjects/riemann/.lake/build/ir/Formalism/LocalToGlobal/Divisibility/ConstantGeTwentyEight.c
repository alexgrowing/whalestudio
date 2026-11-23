// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement public import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DivInputs_toR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DivInputs_toR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DivInputs_toR___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DivInputs_toR___redArg(lean_object* v_I_1_){
_start:
{
lean_object* v_X0_2_; lean_object* v_ch_3_; lean_object* v_hn_4_; lean_object* v_cb_5_; lean_object* v_eb_6_; lean_object* v_Sy_7_; lean_object* v_LG_8_; lean_object* v_E3_9_; lean_object* v_E2_10_; lean_object* v_gy_11_; lean_object* v_00_u03b7y_12_; lean_object* v_El3_13_; lean_object* v_Q_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_X0_2_ = lean_ctor_get(v_I_1_, 0);
v_ch_3_ = lean_ctor_get(v_I_1_, 1);
v_hn_4_ = lean_ctor_get(v_I_1_, 2);
v_cb_5_ = lean_ctor_get(v_I_1_, 3);
v_eb_6_ = lean_ctor_get(v_I_1_, 4);
v_Sy_7_ = lean_ctor_get(v_I_1_, 5);
v_LG_8_ = lean_ctor_get(v_I_1_, 6);
v_E3_9_ = lean_ctor_get(v_I_1_, 7);
v_E2_10_ = lean_ctor_get(v_I_1_, 8);
v_gy_11_ = lean_ctor_get(v_I_1_, 9);
v_00_u03b7y_12_ = lean_ctor_get(v_I_1_, 10);
v_El3_13_ = lean_ctor_get(v_I_1_, 11);
v_Q_14_ = lean_ctor_get(v_I_1_, 12);
v_isSharedCheck_21_ = !lean_is_exclusive(v_I_1_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v_I_1_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_Q_14_);
lean_inc(v_El3_13_);
lean_inc(v_00_u03b7y_12_);
lean_inc(v_gy_11_);
lean_inc(v_E2_10_);
lean_inc(v_E3_9_);
lean_inc(v_LG_8_);
lean_inc(v_Sy_7_);
lean_inc(v_eb_6_);
lean_inc(v_cb_5_);
lean_inc(v_hn_4_);
lean_inc(v_ch_3_);
lean_inc(v_X0_2_);
lean_dec(v_I_1_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_X0_2_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_ch_3_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_hn_4_);
lean_ctor_set(v_reuseFailAlloc_20_, 3, v_cb_5_);
lean_ctor_set(v_reuseFailAlloc_20_, 4, v_eb_6_);
lean_ctor_set(v_reuseFailAlloc_20_, 5, v_Sy_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 6, v_LG_8_);
lean_ctor_set(v_reuseFailAlloc_20_, 7, v_E3_9_);
lean_ctor_set(v_reuseFailAlloc_20_, 8, v_E2_10_);
lean_ctor_set(v_reuseFailAlloc_20_, 9, v_gy_11_);
lean_ctor_set(v_reuseFailAlloc_20_, 10, v_00_u03b7y_12_);
lean_ctor_set(v_reuseFailAlloc_20_, 11, v_El3_13_);
lean_ctor_set(v_reuseFailAlloc_20_, 12, v_Q_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DivInputs_toR(lean_object* v_K_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_Bs_26_, lean_object* v_Df0_27_, lean_object* v_Df1_28_, lean_object* v_Dc_29_, lean_object* v_Sp_30_, lean_object* v_N_31_, lean_object* v_Pl_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_P_35_, lean_object* v_R_36_, lean_object* v_u_37_, lean_object* v_Nu_38_, lean_object* v_sg_39_, lean_object* v_I_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Formalism_L2_DIV_DivInputs_toR___redArg(v_I_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DivInputs_toR___boxed(lean_object** _args){
lean_object* v_K_42_ = _args[0];
lean_object* v_inst_43_ = _args[1];
lean_object* v_inst_44_ = _args[2];
lean_object* v_inst_45_ = _args[3];
lean_object* v_Bs_46_ = _args[4];
lean_object* v_Df0_47_ = _args[5];
lean_object* v_Df1_48_ = _args[6];
lean_object* v_Dc_49_ = _args[7];
lean_object* v_Sp_50_ = _args[8];
lean_object* v_N_51_ = _args[9];
lean_object* v_Pl_52_ = _args[10];
lean_object* v_inst_53_ = _args[11];
lean_object* v_inst_54_ = _args[12];
lean_object* v_P_55_ = _args[13];
lean_object* v_R_56_ = _args[14];
lean_object* v_u_57_ = _args[15];
lean_object* v_Nu_58_ = _args[16];
lean_object* v_sg_59_ = _args[17];
lean_object* v_I_60_ = _args[18];
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_DIV_DivInputs_toR(v_K_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_Bs_46_, v_Df0_47_, v_Df1_48_, v_Dc_49_, v_Sp_50_, v_N_51_, v_Pl_52_, v_inst_53_, v_inst_54_, v_P_55_, v_R_56_, v_u_57_, v_Nu_58_, v_sg_59_, v_I_60_);
lean_dec(v_sg_59_);
lean_dec(v_u_57_);
lean_dec_ref(v_R_56_);
lean_dec_ref(v_P_55_);
lean_dec_ref(v_inst_54_);
lean_dec(v_inst_53_);
lean_dec_ref(v_N_51_);
lean_dec_ref(v_Sp_50_);
lean_dec_ref(v_Dc_49_);
lean_dec_ref(v_Df1_48_);
lean_dec_ref(v_Df0_47_);
lean_dec_ref(v_Bs_46_);
lean_dec(v_inst_45_);
lean_dec_ref(v_inst_43_);
return v_res_61_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_DivisionHeightBoundStatement(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ConstantGeTwentyEight(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_DivisionHeightBoundStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
