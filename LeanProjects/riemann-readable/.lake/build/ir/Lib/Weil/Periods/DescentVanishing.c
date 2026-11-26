// Lean compiler output
// Module: Lib.Weil.Periods.DescentVanishing
// Imports: public import Init public meta import Init public import Lib.Adelic.QuotientMeasure.UnfoldingInStages public import Lib.SiegelWeil.SingularForms.UnimodularCoefficients public import Lib.Weil.DualPair.ThetaIntegrals
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
lean_object* lp_mathlib_Equiv_piComm___redArg();
lean_object* lp_mathlib_Pi_mulAction___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_i_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_3(v_inst_1_, v___y_3_, v___y_4_, v___y_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_i_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___lam__0(v_inst_7_, v_i_8_, v___y_9_, v___y_10_, v___y_11_);
lean_dec(v_i_8_);
return v_res_12_;
}
}
static lean_object* _init_lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_mathlib_Equiv_piComm___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg(lean_object* v_inst_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___f_18_; 
v___f_15_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_15_, 0, v_inst_14_);
v___x_16_ = lean_obj_once(&lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___closed__0, &lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___closed__0_once, _init_lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg___closed__0);
v___x_17_ = lp_mathlib_Pi_mulAction___redArg(v___f_15_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_Equiv_smul___redArg___lam__0), 4, 2);
lean_closure_set(v___f_18_, 0, v___x_16_);
lean_closure_set(v___f_18_, 1, v___x_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall(lean_object* v_m_19_, lean_object* v_p_20_, lean_object* v_M_21_, lean_object* v_R_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___redArg(v_inst_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall___boxed(lean_object* v_m_26_, lean_object* v_p_27_, lean_object* v_M_28_, lean_object* v_R_29_, lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_Space_Splitting_instMulActionMatrixOfForall(v_m_26_, v_p_27_, v_M_28_, v_R_29_, v_inst_30_, v_inst_31_);
lean_dec_ref(v_inst_30_);
return v_res_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_QuotientMeasure_UnfoldingInStages(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_SingularForms_UnimodularCoefficients(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_ThetaIntegrals(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Periods_DescentVanishing(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_QuotientMeasure_UnfoldingInStages(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_SiegelWeil_SingularForms_UnimodularCoefficients(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_ThetaIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
