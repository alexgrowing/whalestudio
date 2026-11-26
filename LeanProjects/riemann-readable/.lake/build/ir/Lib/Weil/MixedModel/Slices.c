// Lean compiler output
// Module: Lib.Weil.MixedModel.Slices
// Imports: public import Init public meta import Init public import Lib.SiegelWeil.Tower.LineTerms public import Lib.Weil.DualPair.ThetaIntegrals public import Lib.Weil.MixedModel.FockSections public import Lib.Weil.TameGaussSum
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight___redArg(lean_object* v_inst_1_, lean_object* v_00_u03bc_2_, lean_object* v_w_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_4_ = l_List_lengthTR___redArg(v_inst_1_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_shiftr(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = lean_nat_to_int(v___x_6_);
v___x_8_ = lean_apply_1(v_00_u03bc_2_, v_w_3_);
v___x_9_ = lean_int_neg(v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lean_int_add(v___x_7_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_7_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight___redArg___boxed(lean_object* v_inst_11_, lean_object* v_00_u03bc_12_, lean_object* v_w_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Exchange_targetWeight___redArg(v_inst_11_, v_00_u03bc_12_, v_w_13_);
lean_dec(v_inst_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight(lean_object* v_E_15_, lean_object* v_inst_16_, lean_object* v_n_17_, lean_object* v_inst_18_, lean_object* v_00_u03bc_19_, lean_object* v_w_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_21_ = l_List_lengthTR___redArg(v_inst_18_);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_shiftr(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_nat_to_int(v___x_23_);
v___x_25_ = lean_apply_1(v_00_u03bc_19_, v_w_20_);
v___x_26_ = lean_int_neg(v___x_25_);
lean_dec(v___x_25_);
v___x_27_ = lean_int_add(v___x_24_, v___x_26_);
lean_dec(v___x_26_);
lean_dec(v___x_24_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_targetWeight___boxed(lean_object* v_E_28_, lean_object* v_inst_29_, lean_object* v_n_30_, lean_object* v_inst_31_, lean_object* v_00_u03bc_32_, lean_object* v_w_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_GRH_New_Exchange_targetWeight(v_E_28_, v_inst_29_, v_n_30_, v_inst_31_, v_00_u03bc_32_, v_w_33_);
lean_dec(v_inst_31_);
lean_dec_ref(v_inst_29_);
return v_res_34_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_Tower_LineTerms(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_ThetaIntegrals(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_MixedModel_FockSections(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_TameGaussSum(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_MixedModel_Slices(uint8_t builtin) {
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
res = initialize_GRH_Lib_SiegelWeil_Tower_LineTerms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_ThetaIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_MixedModel_FockSections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_TameGaussSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
