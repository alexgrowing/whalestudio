// Lean compiler output
// Module: Lib.Shimura.GoodReduction.MultiplicativeNorm
// Imports: public import Init public meta import Init public import Lib.General.NumberTheory.SUnitsAndClassNumber public import Lib.Shimura.GoodReduction.GaussSums public import Lib.Shimura.ThetaModuli.PELThetaTori
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
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction___redArg(lean_object* v_F_1_, lean_object* v_a_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_F_1_, v_a_2_, v_x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction(lean_object* v_V_5_, lean_object* v_R_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_L_10_, lean_object* v_B_11_, lean_object* v_F_12_, lean_object* v_00_u03b2_13_, lean_object* v_h_14_, lean_object* v_a_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_apply_2(v_F_12_, v_a_15_, v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction___boxed(lean_object* v_V_18_, lean_object* v_R_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_L_23_, lean_object* v_B_24_, lean_object* v_F_25_, lean_object* v_00_u03b2_26_, lean_object* v_h_27_, lean_object* v_a_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH_New_ThetaTori_IsHermitianAction_torsionAction(v_V_18_, v_R_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_L_23_, v_B_24_, v_F_25_, v_00_u03b2_26_, v_h_27_, v_a_28_, v_x_29_);
lean_dec(v_00_u03b2_26_);
lean_dec_ref(v_B_24_);
lean_dec(v_inst_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_NumberTheory_SUnitsAndClassNumber(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_GoodReduction_GaussSums(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_GoodReduction_MultiplicativeNorm(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_NumberTheory_SUnitsAndClassNumber(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_GoodReduction_GaussSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
