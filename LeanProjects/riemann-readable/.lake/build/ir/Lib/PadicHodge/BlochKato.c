// Lean compiler output
// Module: Lib.PadicHodge.BlochKato
// Imports: public import Init public meta import Init public import Lib.PadicHodge.Crystalline.FixedRatios public import Lib.PadicHodge.Crystalline.HodgeTateJumps
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
lean_object* lp_mathlib_MulHom_compLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoidHom_domRestrict___redArg(lean_object*);
lean_object* lp_mathlib_MonoidHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle___redArg(lean_object* v_q_1_){
_start:
{
lean_object* v___f_2_; lean_object* v___x_3_; lean_object* v___f_4_; 
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_MulHom_compLeft___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2_, 0, v_q_1_);
v___x_3_ = lp_mathlib_AddMonoidHom_domRestrict___redArg(v___f_2_);
v___f_4_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4_, 0, v___x_3_);
return v___f_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle(lean_object* v_p_5_, lean_object* v_inst_6_, lean_object* v_00_u0393_7_, lean_object* v_R_8_, lean_object* v_T_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_00_U0001d4a5_17_, lean_object* v_00_u03c1_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_hj_23_, lean_object* v_h_24_, lean_object* v_S_25_, lean_object* v_inst_26_, lean_object* v_V_27_, lean_object* v_q_28_, lean_object* v_m_29_, lean_object* v_e_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___f_34_; 
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_MulHom_compLeft___redArg___lam__0), 3, 1);
lean_closure_set(v___f_32_, 0, v_q_28_);
v___x_33_ = lp_mathlib_AddMonoidHom_domRestrict___redArg(v___f_32_);
v___f_34_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_34_, 0, v___x_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle___boxed(lean_object** _args){
lean_object* v_p_35_ = _args[0];
lean_object* v_inst_36_ = _args[1];
lean_object* v_00_u0393_37_ = _args[2];
lean_object* v_R_38_ = _args[3];
lean_object* v_T_39_ = _args[4];
lean_object* v_inst_40_ = _args[5];
lean_object* v_inst_41_ = _args[6];
lean_object* v_inst_42_ = _args[7];
lean_object* v_inst_43_ = _args[8];
lean_object* v_inst_44_ = _args[9];
lean_object* v_inst_45_ = _args[10];
lean_object* v_inst_46_ = _args[11];
lean_object* v_00_U0001d4a5_47_ = _args[12];
lean_object* v_00_u03c1_48_ = _args[13];
lean_object* v_inst_49_ = _args[14];
lean_object* v_inst_50_ = _args[15];
lean_object* v_inst_51_ = _args[16];
lean_object* v_inst_52_ = _args[17];
lean_object* v_hj_53_ = _args[18];
lean_object* v_h_54_ = _args[19];
lean_object* v_S_55_ = _args[20];
lean_object* v_inst_56_ = _args[21];
lean_object* v_V_57_ = _args[22];
lean_object* v_q_58_ = _args[23];
lean_object* v_m_59_ = _args[24];
lean_object* v_e_60_ = _args[25];
lean_object* v_k_61_ = _args[26];
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_GRH_New_Period_IsPotentiallyCrystalline_reducedCocycle(v_p_35_, v_inst_36_, v_00_u0393_37_, v_R_38_, v_T_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_inst_43_, v_inst_44_, v_inst_45_, v_inst_46_, v_00_U0001d4a5_47_, v_00_u03c1_48_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_, v_hj_53_, v_h_54_, v_S_55_, v_inst_56_, v_V_57_, v_q_58_, v_m_59_, v_e_60_, v_k_61_);
lean_dec(v_m_59_);
lean_dec_ref(v_V_57_);
lean_dec_ref(v_inst_56_);
lean_dec(v_00_u03c1_48_);
lean_dec_ref(v_00_U0001d4a5_47_);
lean_dec(v_inst_45_);
lean_dec(v_inst_44_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_41_);
lean_dec_ref(v_inst_40_);
lean_dec(v_p_35_);
return v_res_62_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Crystalline_FixedRatios(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Crystalline_HodgeTateJumps(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicHodge_BlochKato(uint8_t builtin) {
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
res = initialize_GRH_Lib_PadicHodge_Crystalline_FixedRatios(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicHodge_Crystalline_HodgeTateJumps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
