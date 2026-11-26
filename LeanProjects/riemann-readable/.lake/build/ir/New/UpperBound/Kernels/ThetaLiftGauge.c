// Lean compiler output
// Module: New.UpperBound.Kernels.ThetaLiftGauge
// Imports: public import Init public meta import Init public import Lib.Weil.DualPair.KernelLaws public import New.Derivatives.Vacuum.Divisibility public import New.UpperBound.Kernels.JetConjugatesAndBounds
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
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Kernel_raises___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises(lean_object* v_P_5_, lean_object* v_s_6_, lean_object* v_n_7_, lean_object* v_n_x27_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_00_u03ba_13_, lean_object* v_e_14_, lean_object* v_ea_15_, lean_object* v_K_16_, lean_object* v_p_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_S_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_k_23_, lean_object* v_d_24_, lean_object* v_d_x27_25_, lean_object* v_c_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Kernel_raises___boxed(lean_object** _args){
lean_object* v_P_28_ = _args[0];
lean_object* v_s_29_ = _args[1];
lean_object* v_n_30_ = _args[2];
lean_object* v_n_x27_31_ = _args[3];
lean_object* v_inst_32_ = _args[4];
lean_object* v_inst_33_ = _args[5];
lean_object* v_inst_34_ = _args[6];
lean_object* v_inst_35_ = _args[7];
lean_object* v_00_u03ba_36_ = _args[8];
lean_object* v_e_37_ = _args[9];
lean_object* v_ea_38_ = _args[10];
lean_object* v_K_39_ = _args[11];
lean_object* v_p_40_ = _args[12];
lean_object* v_inst_41_ = _args[13];
lean_object* v_inst_42_ = _args[14];
lean_object* v_S_43_ = _args[15];
lean_object* v_inst_44_ = _args[16];
lean_object* v_inst_45_ = _args[17];
lean_object* v_k_46_ = _args[18];
lean_object* v_d_47_ = _args[19];
lean_object* v_d_x27_48_ = _args[20];
lean_object* v_c_49_ = _args[21];
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_GRH_New_Kernel_raises(v_P_28_, v_s_29_, v_n_30_, v_n_x27_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_00_u03ba_36_, v_e_37_, v_ea_38_, v_K_39_, v_p_40_, v_inst_41_, v_inst_42_, v_S_43_, v_inst_44_, v_inst_45_, v_k_46_, v_d_47_, v_d_x27_48_, v_c_49_);
lean_dec(v_c_49_);
lean_dec_ref(v_d_x27_48_);
lean_dec_ref(v_d_47_);
lean_dec_ref(v_k_46_);
lean_dec(v_inst_45_);
lean_dec_ref(v_inst_44_);
lean_dec(v_inst_42_);
lean_dec(v_p_40_);
lean_dec_ref(v_ea_38_);
lean_dec_ref(v_e_37_);
lean_dec_ref(v_00_u03ba_36_);
lean_dec_ref(v_inst_35_);
lean_dec(v_inst_34_);
lean_dec_ref(v_inst_33_);
lean_dec(v_inst_32_);
lean_dec(v_s_29_);
lean_dec_ref(v_P_28_);
return v_res_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_KernelLaws(uint8_t builtin);
lean_object* initialize_GRH_New_Derivatives_Vacuum_Divisibility(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Kernels_JetConjugatesAndBounds(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Kernels_ThetaLiftGauge(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_DualPair_KernelLaws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Derivatives_Vacuum_Divisibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Kernels_JetConjugatesAndBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
