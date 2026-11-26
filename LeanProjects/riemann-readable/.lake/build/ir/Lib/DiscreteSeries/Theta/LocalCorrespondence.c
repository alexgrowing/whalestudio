// Lean compiler output
// Module: Lib.DiscreteSeries.Theta.LocalCorrespondence
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Rigidity.KernelFixes public import Lib.DiscreteSeries.Theta.CasimirComparison public import Lib.DiscreteSeries.Theta.FockJointHarmonics public import Lib.Weil.Fock.OscillatorPair
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
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerRow___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerRow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerRow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerCol___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerCol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerRow___redArg(lean_object* v_T_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_varEquiv_3_; lean_object* v___x_4_; lean_object* v_toFun_5_; lean_object* v___x_6_; lean_object* v_fst_7_; 
v_varEquiv_3_ = lean_ctor_get(v_T_1_, 3);
lean_inc_ref(v_varEquiv_3_);
lean_dec_ref(v_T_1_);
v___x_4_ = lp_mathlib_Equiv_symm___redArg(v_varEquiv_3_);
v_toFun_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toFun_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lean_apply_1(v_toFun_5_, v_x_2_);
v_fst_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_fst_7_);
lean_dec_ref(v___x_6_);
return v_fst_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerRow(lean_object* v_R_8_, lean_object* v_C_9_, lean_object* v_00_u03b5_10_, lean_object* v_00_u03b5_x27_11_, lean_object* v_00_u03b9_12_, lean_object* v_inst_13_, lean_object* v_T_14_, lean_object* v_s_15_, lean_object* v_w_16_, lean_object* v_t_17_, lean_object* v_x_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_GRH_New_FockDualPair_layerRow___redArg(v_T_14_, v_x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerRow___boxed(lean_object* v_R_20_, lean_object* v_C_21_, lean_object* v_00_u03b5_22_, lean_object* v_00_u03b5_x27_23_, lean_object* v_00_u03b9_24_, lean_object* v_inst_25_, lean_object* v_T_26_, lean_object* v_s_27_, lean_object* v_w_28_, lean_object* v_t_29_, lean_object* v_x_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_GRH_New_FockDualPair_layerRow(v_R_20_, v_C_21_, v_00_u03b5_22_, v_00_u03b5_x27_23_, v_00_u03b9_24_, v_inst_25_, v_T_26_, v_s_27_, v_w_28_, v_t_29_, v_x_30_);
lean_dec_ref(v_t_29_);
lean_dec_ref(v_w_28_);
lean_dec_ref(v_s_27_);
lean_dec(v_inst_25_);
lean_dec_ref(v_00_u03b5_x27_23_);
lean_dec_ref(v_00_u03b5_22_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerCol___redArg(lean_object* v_T_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_varEquiv_34_; lean_object* v___x_35_; lean_object* v_toFun_36_; lean_object* v___x_37_; lean_object* v_snd_38_; 
v_varEquiv_34_ = lean_ctor_get(v_T_32_, 3);
lean_inc_ref(v_varEquiv_34_);
lean_dec_ref(v_T_32_);
v___x_35_ = lp_mathlib_Equiv_symm___redArg(v_varEquiv_34_);
v_toFun_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_toFun_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lean_apply_1(v_toFun_36_, v_x_33_);
v_snd_38_ = lean_ctor_get(v___x_37_, 1);
lean_inc(v_snd_38_);
lean_dec_ref(v___x_37_);
return v_snd_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerCol(lean_object* v_R_39_, lean_object* v_C_40_, lean_object* v_00_u03b5_41_, lean_object* v_00_u03b5_x27_42_, lean_object* v_00_u03b9_43_, lean_object* v_inst_44_, lean_object* v_T_45_, lean_object* v_s_46_, lean_object* v_w_47_, lean_object* v_t_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_GRH_New_FockDualPair_layerCol___redArg(v_T_45_, v_x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_FockDualPair_layerCol___boxed(lean_object* v_R_51_, lean_object* v_C_52_, lean_object* v_00_u03b5_53_, lean_object* v_00_u03b5_x27_54_, lean_object* v_00_u03b9_55_, lean_object* v_inst_56_, lean_object* v_T_57_, lean_object* v_s_58_, lean_object* v_w_59_, lean_object* v_t_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_GRH_New_FockDualPair_layerCol(v_R_51_, v_C_52_, v_00_u03b5_53_, v_00_u03b5_x27_54_, v_00_u03b9_55_, v_inst_56_, v_T_57_, v_s_58_, v_w_59_, v_t_60_, v_x_61_);
lean_dec_ref(v_t_60_);
lean_dec_ref(v_w_59_);
lean_dec_ref(v_s_58_);
lean_dec(v_inst_56_);
lean_dec_ref(v_00_u03b5_x27_54_);
lean_dec_ref(v_00_u03b5_53_);
return v_res_62_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Rigidity_KernelFixes(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_CasimirComparison(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_FockJointHarmonics(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Fock_OscillatorPair(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_LocalCorrespondence(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Rigidity_KernelFixes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Theta_CasimirComparison(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Theta_FockJointHarmonics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Fock_OscillatorPair(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
