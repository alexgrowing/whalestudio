// Lean compiler output
// Module: Lib.Shimura.ThetaModuli.PELThetaTori
// Imports: public import Init public meta import Init public import Lib.Shimura.ThetaModuli.FlatClosure public import Lib.Shimura.ThetaNormality.NormalGeneration public import Lib.Shimura.Uniformisation.AdelicFrames
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
lean_object* lp_GRH_New_Variety_toRealVectors___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint___redArg___lam__0(lean_object* v_toCMType_1_, lean_object* v_y_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_60__overap_5_; lean_object* v___x_6_; 
v___x_60__overap_5_ = lp_GRH_New_Variety_toRealVectors___redArg(v_toCMType_1_);
v___x_6_ = lean_apply_3(v___x_60__overap_5_, v_y_2_, v___y_3_, v___y_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint___redArg(lean_object* v_inst_7_, lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
lean_object* v_realEquiv_10_; lean_object* v_toCMType_11_; lean_object* v_toLinearMap_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
v_realEquiv_10_ = lean_ctor_get(v_x_8_, 1);
lean_inc_ref(v_realEquiv_10_);
lean_dec_ref(v_x_8_);
v_toCMType_11_ = lean_ctor_get(v_inst_7_, 0);
lean_inc_ref(v_toCMType_11_);
lean_dec_ref(v_inst_7_);
v_toLinearMap_12_ = lean_ctor_get(v_realEquiv_10_, 0);
lean_inc(v_toLinearMap_12_);
lean_dec_ref(v_realEquiv_10_);
v___f_13_ = lean_alloc_closure((void*)(lp_GRH_New_ThetaTori_PeriodMap_periodPoint___redArg___lam__0), 4, 2);
lean_closure_set(v___f_13_, 0, v_toCMType_11_);
lean_closure_set(v___f_13_, 1, v_y_9_);
v___x_14_ = lean_apply_1(v_toLinearMap_12_, v___f_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_D_18_, lean_object* v_g_19_, lean_object* v_00_u2113_20_, lean_object* v_V_21_, lean_object* v_inst_22_, lean_object* v_x_23_, lean_object* v_y_24_){
_start:
{
lean_object* v_realEquiv_25_; lean_object* v_toCMType_26_; lean_object* v_toLinearMap_27_; lean_object* v___f_28_; lean_object* v___x_29_; 
v_realEquiv_25_ = lean_ctor_get(v_x_23_, 1);
lean_inc_ref(v_realEquiv_25_);
lean_dec_ref(v_x_23_);
v_toCMType_26_ = lean_ctor_get(v_inst_17_, 0);
lean_inc_ref(v_toCMType_26_);
lean_dec_ref(v_inst_17_);
v_toLinearMap_27_ = lean_ctor_get(v_realEquiv_25_, 0);
lean_inc(v_toLinearMap_27_);
lean_dec_ref(v_realEquiv_25_);
v___f_28_ = lean_alloc_closure((void*)(lp_GRH_New_ThetaTori_PeriodMap_periodPoint___redArg___lam__0), 4, 2);
lean_closure_set(v___f_28_, 0, v_toCMType_26_);
lean_closure_set(v___f_28_, 1, v_y_24_);
v___x_29_ = lean_apply_1(v_toLinearMap_27_, v___f_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_PeriodMap_periodPoint___boxed(lean_object* v_E_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_D_33_, lean_object* v_g_34_, lean_object* v_00_u2113_35_, lean_object* v_V_36_, lean_object* v_inst_37_, lean_object* v_x_38_, lean_object* v_y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_GRH_New_ThetaTori_PeriodMap_periodPoint(v_E_30_, v_inst_31_, v_inst_32_, v_D_33_, v_g_34_, v_00_u2113_35_, v_V_36_, v_inst_37_, v_x_38_, v_y_39_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_00_u2113_35_);
lean_dec_ref(v_g_34_);
lean_dec_ref(v_D_33_);
lean_dec_ref(v_inst_31_);
return v_res_40_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_FlatClosure(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaNormality_NormalGeneration(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Uniformisation_AdelicFrames(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_ThetaModuli_FlatClosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_ThetaNormality_NormalGeneration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Uniformisation_AdelicFrames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
