// Lean compiler output
// Module: Lib.Shimura.GoodReduction.GaussSums
// Imports: public import Init public meta import Init public import Lib.Shimura.GoodReduction.TorsionSizes public import Lib.Shimura.Uniformisation.HolomorphicFamilies
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
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice(lean_object* v_V_5_, lean_object* v_R_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_L_10_, lean_object* v_B_11_, lean_object* v_F_12_, lean_object* v_00_u03b2_13_, lean_object* v_x_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_IsHermitianAction_divLattice___boxed(lean_object* v_V_17_, lean_object* v_R_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_L_22_, lean_object* v_B_23_, lean_object* v_F_24_, lean_object* v_00_u03b2_25_, lean_object* v_x_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_ThetaTori_IsHermitianAction_divLattice(v_V_17_, v_R_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_L_22_, v_B_23_, v_F_24_, v_00_u03b2_25_, v_x_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec(v_00_u03b2_25_);
lean_dec(v_F_24_);
lean_dec_ref(v_B_23_);
lean_dec(v_inst_21_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
return v_res_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_GoodReduction_TorsionSizes(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_GoodReduction_GaussSums(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_GoodReduction_TorsionSizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_HolomorphicFamilies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
