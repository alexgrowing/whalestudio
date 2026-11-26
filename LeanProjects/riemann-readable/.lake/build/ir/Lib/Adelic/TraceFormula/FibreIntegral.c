// Lean compiler output
// Module: Lib.Adelic.TraceFormula.FibreIntegral
// Imports: public import Init public meta import Init public import Lib.Adelic.TraceFormula.TestFunction public import Lib.DiscreteSeries.Haar.CayleyChart
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
lean_object* lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_TestFunction_translate___redArg(lean_object*);
lean_object* lp_mathlib_MonoidHom_prod___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SMulMemClass_subtype___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_TestFunction_eval___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SMulMemClass_subtype___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_TestFunction_eval___redArg___closed__0 = (const lean_object*)&lp_GRH_New_TestFunction_eval___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_eval___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_eval(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__0 = (const lean_object*)&lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__0_value)} };
static const lean_object* lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__1 = (const lean_object*)&lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_tensor___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_tensor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_tensor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_partialApply___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_partialApply___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_partialApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate___redArg(lean_object* v_inst_1_, lean_object* v_j_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___f_5_; 
v___x_3_ = lp_GRH_New_TestFunction_translate___redArg(v_inst_1_);
lean_inc(v_j_2_);
v___x_4_ = lp_mathlib_MonoidHom_prod___redArg(v_j_2_, v_j_2_);
v___f_5_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5_, 0, v___x_4_);
lean_closure_set(v___f_5_, 1, v___x_3_);
return v___f_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate___redArg___boxed(lean_object* v_inst_6_, lean_object* v_j_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_TestFunction_conjugate___redArg(v_inst_6_, v_j_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate(lean_object* v_G_9_, lean_object* v_00_u0393_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_j_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_GRH_New_TestFunction_conjugate___redArg(v_inst_11_, v_j_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_conjugate___boxed(lean_object* v_G_19_, lean_object* v_00_u0393_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_j_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_TestFunction_conjugate(v_G_19_, v_00_u0393_20_, v_inst_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_inst_25_, v_inst_26_, v_j_27_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_inst_21_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_eval___redArg(lean_object* v_x_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___f_33_; 
v___x_31_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_31_, 0, lean_box(0));
lean_closure_set(v___x_31_, 1, lean_box(0));
lean_closure_set(v___x_31_, 2, v_x_30_);
v___f_32_ = ((lean_object*)(lp_GRH_New_TestFunction_eval___redArg___closed__0));
v___f_33_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_33_, 0, v___f_32_);
lean_closure_set(v___f_33_, 1, v___x_31_);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_eval(lean_object* v_Y_34_, lean_object* v_inst_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_GRH_New_TestFunction_eval___redArg(v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_tensor___redArg___lam__0(lean_object* v_a_41_, lean_object* v_b_42_, lean_object* v_p_43_){
_start:
{
lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_46_; lean_object* v_re_47_; lean_object* v_im_48_; lean_object* v___x_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
v_fst_44_ = lean_ctor_get(v_p_43_, 0);
lean_inc(v_fst_44_);
v_snd_45_ = lean_ctor_get(v_p_43_, 1);
lean_inc(v_snd_45_);
lean_dec_ref(v_p_43_);
v___x_46_ = lean_apply_1(v_a_41_, v_fst_44_);
v_re_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_re_47_);
v_im_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_im_48_);
lean_dec_ref(v___x_46_);
v___x_49_ = lean_apply_1(v_b_42_, v_snd_45_);
v___f_50_ = ((lean_object*)(lp_GRH_New_TestFunction_tensor___redArg___lam__0___closed__1));
v___x_51_ = lp_mathlib_Complex_mulAux___redArg(v___f_50_, v_re_47_, v_im_48_, v___x_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_tensor___redArg(lean_object* v_a_52_, lean_object* v_b_53_){
_start:
{
lean_object* v___f_54_; 
v___f_54_ = lean_alloc_closure((void*)(lp_GRH_New_TestFunction_tensor___redArg___lam__0), 3, 2);
lean_closure_set(v___f_54_, 0, v_a_52_);
lean_closure_set(v___f_54_, 1, v_b_53_);
return v___f_54_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_tensor(lean_object* v_Y_55_, lean_object* v_Z_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v___f_63_; 
v___f_63_ = lean_alloc_closure((void*)(lp_GRH_New_TestFunction_tensor___redArg___lam__0), 3, 2);
lean_closure_set(v___f_63_, 0, v_a_61_);
lean_closure_set(v___f_63_, 1, v_b_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_partialApply___redArg___lam__0(lean_object* v_y_64_, lean_object* v_00_u03a8_65_, lean_object* v_z_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_y_64_);
lean_ctor_set(v___x_67_, 1, v_z_66_);
v___x_68_ = lean_apply_1(v_00_u03a8_65_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_partialApply___redArg(lean_object* v_00_u03a8_69_, lean_object* v_y_70_){
_start:
{
lean_object* v___f_71_; 
v___f_71_ = lean_alloc_closure((void*)(lp_GRH_New_TestFunction_partialApply___redArg___lam__0), 3, 2);
lean_closure_set(v___f_71_, 0, v_y_70_);
lean_closure_set(v___f_71_, 1, v_00_u03a8_69_);
return v___f_71_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TestFunction_partialApply(lean_object* v_Y_72_, lean_object* v_Z_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_00_u03a8_78_, lean_object* v_y_79_){
_start:
{
lean_object* v___f_80_; 
v___f_80_ = lean_alloc_closure((void*)(lp_GRH_New_TestFunction_partialApply___redArg___lam__0), 3, 2);
lean_closure_set(v___f_80_, 0, v_y_79_);
lean_closure_set(v___f_80_, 1, v_00_u03a8_78_);
return v___f_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_TraceFormula_TestFunction(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Haar_CayleyChart(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Adelic_TraceFormula_FibreIntegral(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_TraceFormula_TestFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Haar_CayleyChart(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
