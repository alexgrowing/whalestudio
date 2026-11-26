// Lean compiler output
// Module: New.Appendix.DiscreteSeries.Positions
// Imports: public import Init public meta import Init public import Lib.Adelic.Witt.WittTheorem public import New.Appendix.DiscreteSeries.SteepParameters
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
lean_object* lp_mathlib_Matrix_conjTranspose___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_GRH_New_signMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instMul;
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_formAdjoint___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_formAdjoint___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_initCols___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_initCols___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_initCols___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_DiscreteSeries_initCols___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_initCols___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___closed__1 = (const lean_object*)&lp_GRH_New_DiscreteSeries_initCols___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_00_u03b5_2_, lean_object* v_a_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lp_GRH_New_signMatrix___redArg(v_inst_1_, v_00_u03b5_2_, v_j_4_, v_a_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_00_u03b7_7_, lean_object* v_a_8_, lean_object* v_j_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lp_GRH_New_signMatrix___redArg(v_inst_6_, v_00_u03b7_7_, v_a_8_, v_j_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__2(lean_object* v___f_11_, lean_object* v_A_12_, lean_object* v_j_13_, lean_object* v_j_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_mathlib_Matrix_conjTranspose___redArg(v___f_11_, v_A_12_, v_j_14_, v_j_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__3(lean_object* v___f_16_, lean_object* v_A_17_, lean_object* v_inst_18_, lean_object* v___x_19_, lean_object* v___x_20_, lean_object* v___f_21_, lean_object* v_j_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; 
v___f_23_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__2), 4, 3);
lean_closure_set(v___f_23_, 0, v___f_16_);
lean_closure_set(v___f_23_, 1, v_A_17_);
lean_closure_set(v___f_23_, 2, v_j_22_);
v___x_24_ = lp_mathlib_dotProduct___redArg(v_inst_18_, v___x_19_, v___x_20_, v___f_21_, v___f_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__3___boxed(lean_object* v___f_25_, lean_object* v_A_26_, lean_object* v_inst_27_, lean_object* v___x_28_, lean_object* v___x_29_, lean_object* v___f_30_, lean_object* v_j_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__3(v___f_25_, v_A_26_, v_inst_27_, v___x_28_, v___x_29_, v___f_30_, v_j_31_);
lean_dec_ref(v___x_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint___redArg(lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_00_u03b5_38_, lean_object* v_00_u03b7_39_, lean_object* v_A_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v___f_43_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__0), 4, 3);
lean_closure_set(v___f_43_, 0, v_inst_35_);
lean_closure_set(v___f_43_, 1, v_00_u03b5_38_);
lean_closure_set(v___f_43_, 2, v_a_42_);
v___f_44_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__1), 4, 3);
lean_closure_set(v___f_44_, 0, v_inst_37_);
lean_closure_set(v___f_44_, 1, v_00_u03b7_39_);
lean_closure_set(v___f_44_, 2, v_a_41_);
v___x_45_ = lp_mathlib_Complex_instMul;
v___x_46_ = lp_mathlib_Complex_instAddCommMonoid;
v___f_47_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_formAdjoint___redArg___closed__0));
v___f_48_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_formAdjoint___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_48_, 0, v___f_47_);
lean_closure_set(v___f_48_, 1, v_A_40_);
lean_closure_set(v___f_48_, 2, v_inst_36_);
lean_closure_set(v___f_48_, 3, v___x_45_);
lean_closure_set(v___f_48_, 4, v___x_46_);
lean_closure_set(v___f_48_, 5, v___f_44_);
v___x_49_ = lp_mathlib_dotProduct___redArg(v_inst_34_, v___x_45_, v___x_46_, v___f_48_, v___f_43_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_formAdjoint(lean_object* v_n_50_, lean_object* v_m_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_00_u03b5_56_, lean_object* v_00_u03b7_57_, lean_object* v_A_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_GRH_New_DiscreteSeries_formAdjoint___redArg(v_inst_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_00_u03b5_56_, v_00_u03b7_57_, v_A_58_, v_a_59_, v_a_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__0(lean_object* v___y_62_){
_start:
{
lean_inc(v___y_62_);
return v___y_62_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__0___boxed(lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_DiscreteSeries_initCols___redArg___lam__0(v___y_63_);
lean_dec(v___y_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__1(lean_object* v___y_65_){
_start:
{
lean_inc(v___y_65_);
return v___y_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg___lam__1___boxed(lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_GRH_New_DiscreteSeries_initCols___redArg___lam__1(v___y_66_);
lean_dec(v___y_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___redArg(lean_object* v_v_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; 
v___f_73_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_initCols___redArg___closed__0));
v___f_74_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_initCols___redArg___closed__1));
v___x_75_ = lp_mathlib_Matrix_submatrix___redArg(v_v_70_, v___f_73_, v___f_74_, v_a_71_, v_a_72_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols(lean_object* v_n_76_, lean_object* v_d_77_, lean_object* v_v_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_GRH_New_DiscreteSeries_initCols___redArg(v_v_78_, v_a_79_, v_a_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_initCols___boxed(lean_object* v_n_82_, lean_object* v_d_83_, lean_object* v_v_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_GRH_New_DiscreteSeries_initCols(v_n_82_, v_d_83_, v_v_84_, v_a_85_, v_a_86_);
lean_dec(v_d_83_);
return v_res_87_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Witt_WittTheorem(uint8_t builtin);
lean_object* initialize_GRH_New_Appendix_DiscreteSeries_SteepParameters(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Appendix_DiscreteSeries_Positions(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Witt_WittTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Appendix_DiscreteSeries_SteepParameters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
