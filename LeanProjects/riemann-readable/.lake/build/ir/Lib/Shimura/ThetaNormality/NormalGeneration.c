// Lean compiler output
// Module: Lib.Shimura.ThetaNormality.NormalGeneration
// Imports: public import Init public meta import Init public import Lib.Shimura.GoodReduction.TorsionSizes
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
lean_object* lp_mathlib_Submodule_mul___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_ThetaTori_formSpan___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Submodule_mul___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_ThetaTori_formSpan___redArg___closed__0 = (const lean_object*)&lp_GRH_New_ThetaTori_formSpan___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan___redArg(lean_object* v_m_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___f_4_; lean_object* v___x_5_; 
v___x_3_ = lean_box(0);
v___f_4_ = ((lean_object*)(lp_GRH_New_ThetaTori_formSpan___redArg___closed__0));
v___x_5_ = l_npowRec___redArg(v___x_3_, v___f_4_, v_m_2_, v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan___redArg___boxed(lean_object* v_m_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_GRH_New_ThetaTori_formSpan___redArg(v_m_6_);
lean_dec(v_m_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan(lean_object* v_00_u03b9_8_, lean_object* v_R_9_, lean_object* v_A_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_x_14_, lean_object* v_m_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___f_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box(0);
v___f_17_ = ((lean_object*)(lp_GRH_New_ThetaTori_formSpan___redArg___closed__0));
v___x_18_ = l_npowRec___redArg(v___x_16_, v___f_17_, v_m_15_, v___x_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_ThetaTori_formSpan___boxed(lean_object* v_00_u03b9_19_, lean_object* v_R_20_, lean_object* v_A_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_x_25_, lean_object* v_m_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_GRH_New_ThetaTori_formSpan(v_00_u03b9_19_, v_R_20_, v_A_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_x_25_, v_m_26_);
lean_dec(v_m_26_);
lean_dec(v_x_25_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
lean_dec_ref(v_inst_22_);
return v_res_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_GoodReduction_TorsionSizes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_ThetaNormality_NormalGeneration(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
