// Lean compiler output
// Module: Lib.SiegelWeil.Formula.LagrangianZeroTerms
// Imports: public import Init public meta import Init public import Lib.Weil.DualPair.MixedModel public import Lib.Weil.Unramified.HeckeTransfer
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian(lean_object* v_E_5_, lean_object* v_n_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_s_12_, lean_object* v_S_13_, lean_object* v_p_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_P_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian___boxed(lean_object* v_E_19_, lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_s_26_, lean_object* v_S_27_, lean_object* v_p_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_P_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_SiegelWeil_CompleteSplitting_lagrangian(v_E_19_, v_n_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_s_26_, v_S_27_, v_p_28_, v_inst_29_, v_inst_30_, v_P_31_);
lean_dec_ref(v_P_31_);
lean_dec_ref(v_inst_30_);
lean_dec(v_inst_29_);
lean_dec_ref(v_S_27_);
lean_dec_ref(v_s_26_);
lean_dec_ref(v_inst_25_);
lean_dec(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting___redArg(lean_object* v_inst_33_, lean_object* v_00_u03b3_34_){
_start:
{
lean_object* v___x_35_; lean_object* v_toCommSemiring_36_; lean_object* v___x_37_; lean_object* v_toZero_38_; lean_object* v_val_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_35_ = lp_mathlib_Field_toSemifield___redArg(v_inst_33_);
v_toCommSemiring_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_toCommSemiring_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_36_);
v_toZero_38_ = lean_ctor_get(v___x_37_, 1);
lean_inc(v_toZero_38_);
lean_dec_ref(v___x_37_);
v_val_39_ = lean_ctor_get(v_00_u03b3_34_, 0);
v___x_40_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_40_, 0, lean_box(0));
lean_closure_set(v___x_40_, 1, lean_box(0));
lean_closure_set(v___x_40_, 2, lean_box(0));
lean_closure_set(v___x_40_, 3, v_toZero_38_);
lean_inc(v_val_39_);
lean_inc_ref(v___x_40_);
v___x_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
lean_ctor_set(v___x_41_, 2, v_val_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting___redArg___boxed(lean_object* v_inst_42_, lean_object* v_00_u03b3_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_SiegelWeil_isometrySplitting___redArg(v_inst_42_, v_00_u03b3_43_);
lean_dec_ref(v_00_u03b3_43_);
lean_dec_ref(v_inst_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting(lean_object* v_E_45_, lean_object* v_n_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_s_51_, lean_object* v_S_52_, lean_object* v_00_u03b3_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_GRH_New_SiegelWeil_isometrySplitting___redArg(v_inst_47_, v_00_u03b3_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_SiegelWeil_isometrySplitting___boxed(lean_object* v_E_55_, lean_object* v_n_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_s_61_, lean_object* v_S_62_, lean_object* v_00_u03b3_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_SiegelWeil_isometrySplitting(v_E_55_, v_n_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_s_61_, v_S_62_, v_00_u03b3_63_);
lean_dec_ref(v_00_u03b3_63_);
lean_dec_ref(v_S_62_);
lean_dec_ref(v_s_61_);
lean_dec_ref(v_inst_60_);
lean_dec(v_inst_59_);
lean_dec_ref(v_inst_58_);
lean_dec_ref(v_inst_57_);
return v_res_64_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_MixedModel(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_HeckeTransfer(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_SiegelWeil_Formula_LagrangianZeroTerms(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_DualPair_MixedModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Unramified_HeckeTransfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
