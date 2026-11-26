// Lean compiler output
// Module: New.Appendix.DiscreteSeries.MinorSecondOrder
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.MatricesNearIdentity
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
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
extern lean_object* lp_mathlib_Complex_instMul;
extern lean_object* lp_mathlib_Complex_instZero;
lean_object* lp_mathlib_Matrix_trace___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_crossTrace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_crossTrace___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__0_value)} };
static const lean_object* lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__1 = (const lean_object*)&lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_scaleCross___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_scaleCross(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___closed__0, &lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___closed__0_once, _init_lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__0(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__1(lean_object* v_B_7_, lean_object* v___y_8_, lean_object* v_j_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_2(v_B_7_, v_j_9_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__2(lean_object* v_Q_11_, lean_object* v___y_12_, lean_object* v_j_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_Q_11_, v___y_12_, v_j_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__3(lean_object* v_A_15_, lean_object* v_j_16_, lean_object* v_j_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_apply_2(v_A_15_, v_j_17_, v_j_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4(lean_object* v_A_19_, lean_object* v_inst_20_, lean_object* v___x_21_, lean_object* v___x_22_, lean_object* v___f_23_, lean_object* v_j_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_25_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__3), 3, 2);
lean_closure_set(v___f_25_, 0, v_A_19_);
lean_closure_set(v___f_25_, 1, v_j_24_);
v___x_26_ = lp_mathlib_dotProduct___redArg(v_inst_20_, v___x_21_, v___x_22_, v___f_23_, v___f_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4___boxed(lean_object* v_A_27_, lean_object* v_inst_28_, lean_object* v___x_29_, lean_object* v___x_30_, lean_object* v___f_31_, lean_object* v_j_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4(v_A_27_, v_inst_28_, v___x_29_, v___x_30_, v___f_31_, v_j_32_);
lean_dec_ref(v___x_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__5(lean_object* v_inst_34_, lean_object* v___x_35_, lean_object* v___f_36_, lean_object* v_j_37_, lean_object* v_Q_38_, lean_object* v_j_39_){
_start:
{
lean_object* v___x_40_; lean_object* v_re_41_; lean_object* v_im_42_; lean_object* v___x_43_; lean_object* v_re_44_; lean_object* v_im_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_56_; 
lean_inc(v_j_37_);
lean_inc(v_j_39_);
v___x_40_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_34_, v___x_35_, v___f_36_, v_j_39_, v_j_37_);
v_re_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_re_41_);
v_im_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_im_42_);
lean_dec(v___x_40_);
v___x_43_ = lean_apply_2(v_Q_38_, v_j_39_, v_j_37_);
v_re_44_ = lean_ctor_get(v___x_43_, 0);
v_im_45_ = lean_ctor_get(v___x_43_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_56_ == 0)
{
v___x_47_ = v___x_43_;
v_isShared_48_ = v_isSharedCheck_56_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_im_45_);
lean_inc(v_re_44_);
lean_dec(v___x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_56_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_54_; 
v___f_49_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_49_, 0, v_re_44_);
v___f_50_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_50_, 0, v_re_41_);
lean_closure_set(v___f_50_, 1, v___f_49_);
v___f_51_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_51_, 0, v_im_45_);
v___f_52_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_52_, 0, v_im_42_);
lean_closure_set(v___f_52_, 1, v___f_51_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___f_52_);
lean_ctor_set(v___x_47_, 0, v___f_50_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___f_50_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___f_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__6(lean_object* v_inst_57_, lean_object* v___x_58_, lean_object* v___f_59_, lean_object* v_Q_60_, lean_object* v_inst_61_, lean_object* v___x_62_, lean_object* v___x_63_, lean_object* v___f_64_, lean_object* v_j_65_){
_start:
{
lean_object* v___f_66_; lean_object* v___x_67_; 
v___f_66_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__5), 6, 5);
lean_closure_set(v___f_66_, 0, v_inst_57_);
lean_closure_set(v___f_66_, 1, v___x_58_);
lean_closure_set(v___f_66_, 2, v___f_59_);
lean_closure_set(v___f_66_, 3, v_j_65_);
lean_closure_set(v___f_66_, 4, v_Q_60_);
v___x_67_ = lp_mathlib_dotProduct___redArg(v_inst_61_, v___x_62_, v___x_63_, v___f_64_, v___f_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__6___boxed(lean_object* v_inst_68_, lean_object* v___x_69_, lean_object* v___f_70_, lean_object* v_Q_71_, lean_object* v_inst_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v___f_75_, lean_object* v_j_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__6(v_inst_68_, v___x_69_, v___f_70_, v_Q_71_, v_inst_72_, v___x_73_, v___x_74_, v___f_75_, v_j_76_);
lean_dec_ref(v___x_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__7(lean_object* v_B_78_, lean_object* v_Q_79_, lean_object* v_A_80_, lean_object* v_inst_81_, lean_object* v___x_82_, lean_object* v___x_83_, lean_object* v_inst_84_, lean_object* v___x_85_, lean_object* v___f_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; 
v___f_89_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_89_, 0, v_B_78_);
lean_closure_set(v___f_89_, 1, v___y_88_);
lean_inc_ref(v_Q_79_);
v___f_90_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__2), 3, 2);
lean_closure_set(v___f_90_, 0, v_Q_79_);
lean_closure_set(v___f_90_, 1, v___y_87_);
lean_inc_ref_n(v___x_83_, 2);
lean_inc_ref_n(v___x_82_, 2);
lean_inc_n(v_inst_81_, 2);
v___f_91_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_91_, 0, v_A_80_);
lean_closure_set(v___f_91_, 1, v_inst_81_);
lean_closure_set(v___f_91_, 2, v___x_82_);
lean_closure_set(v___f_91_, 3, v___x_83_);
lean_closure_set(v___f_91_, 4, v___f_90_);
v___f_92_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_92_, 0, v_inst_84_);
lean_closure_set(v___f_92_, 1, v___x_85_);
lean_closure_set(v___f_92_, 2, v___f_86_);
lean_closure_set(v___f_92_, 3, v_Q_79_);
lean_closure_set(v___f_92_, 4, v_inst_81_);
lean_closure_set(v___f_92_, 5, v___x_82_);
lean_closure_set(v___f_92_, 6, v___x_83_);
lean_closure_set(v___f_92_, 7, v___f_91_);
v___x_93_ = lp_mathlib_dotProduct___redArg(v_inst_81_, v___x_82_, v___x_83_, v___f_92_, v___f_89_);
lean_dec_ref(v___x_83_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace___redArg(lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_Q_97_, lean_object* v_A_98_, lean_object* v_B_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___x_105_; 
v___f_100_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___closed__0));
v___x_101_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_102_ = lp_mathlib_Complex_instMul;
v___x_103_ = lp_mathlib_Complex_instZero;
lean_inc(v_inst_95_);
v___f_104_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__7), 11, 9);
lean_closure_set(v___f_104_, 0, v_B_99_);
lean_closure_set(v___f_104_, 1, v_Q_97_);
lean_closure_set(v___f_104_, 2, v_A_98_);
lean_closure_set(v___f_104_, 3, v_inst_95_);
lean_closure_set(v___f_104_, 4, v___x_102_);
lean_closure_set(v___f_104_, 5, v___x_101_);
lean_closure_set(v___f_104_, 6, v_inst_96_);
lean_closure_set(v___f_104_, 7, v___x_103_);
lean_closure_set(v___f_104_, 8, v___f_100_);
v___x_105_ = lp_mathlib_Matrix_trace___redArg(v_inst_95_, v___x_101_, v___f_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossTrace(lean_object* v_n_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_Q_109_, lean_object* v_A_110_, lean_object* v_B_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_GRH_New_DiscreteSeries_crossTrace___redArg(v_inst_107_, v_inst_108_, v_Q_109_, v_A_110_, v_B_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__1(lean_object* v_Q_113_, lean_object* v_a_114_, lean_object* v_j_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_apply_2(v_Q_113_, v_a_114_, v_j_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__3(lean_object* v_inst_117_, lean_object* v___x_118_, lean_object* v___f_119_, lean_object* v_a_120_, lean_object* v_Q_121_, lean_object* v_j_122_){
_start:
{
lean_object* v___x_123_; lean_object* v_re_124_; lean_object* v_im_125_; lean_object* v___x_126_; lean_object* v_re_127_; lean_object* v_im_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_139_; 
lean_inc(v_a_120_);
lean_inc(v_j_122_);
v___x_123_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_117_, v___x_118_, v___f_119_, v_j_122_, v_a_120_);
v_re_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_re_124_);
v_im_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_im_125_);
lean_dec(v___x_123_);
v___x_126_ = lean_apply_2(v_Q_121_, v_j_122_, v_a_120_);
v_re_127_ = lean_ctor_get(v___x_126_, 0);
v_im_128_ = lean_ctor_get(v___x_126_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_139_ == 0)
{
v___x_130_ = v___x_126_;
v_isShared_131_ = v_isSharedCheck_139_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_im_128_);
lean_inc(v_re_127_);
lean_dec(v___x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_139_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_137_; 
v___f_132_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_132_, 0, v_re_127_);
v___f_133_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_133_, 0, v_re_124_);
lean_closure_set(v___f_133_, 1, v___f_132_);
v___f_134_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_134_, 0, v_im_128_);
v___f_135_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_135_, 0, v_im_125_);
lean_closure_set(v___f_135_, 1, v___f_134_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___f_135_);
lean_ctor_set(v___x_130_, 0, v___f_133_);
v___x_137_ = v___x_130_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___f_133_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___f_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__0(lean_object* v_Q_140_, lean_object* v_a_141_, lean_object* v_j_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_2(v_Q_140_, v_j_142_, v_a_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__2(lean_object* v_inst_144_, lean_object* v___x_145_, lean_object* v___f_146_, lean_object* v_a_147_, lean_object* v_Q_148_, lean_object* v_j_149_){
_start:
{
lean_object* v___x_150_; lean_object* v_re_151_; lean_object* v_im_152_; lean_object* v___x_153_; lean_object* v_re_154_; lean_object* v_im_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_166_; 
lean_inc(v_j_149_);
lean_inc(v_a_147_);
v___x_150_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_144_, v___x_145_, v___f_146_, v_a_147_, v_j_149_);
v_re_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_re_151_);
v_im_152_ = lean_ctor_get(v___x_150_, 1);
lean_inc(v_im_152_);
lean_dec(v___x_150_);
v___x_153_ = lean_apply_2(v_Q_148_, v_a_147_, v_j_149_);
v_re_154_ = lean_ctor_get(v___x_153_, 0);
v_im_155_ = lean_ctor_get(v___x_153_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_166_ == 0)
{
v___x_157_ = v___x_153_;
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_im_155_);
lean_inc(v_re_154_);
lean_dec(v___x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_164_; 
v___f_159_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_159_, 0, v_re_154_);
v___f_160_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_160_, 0, v_re_151_);
lean_closure_set(v___f_160_, 1, v___f_159_);
v___f_161_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_161_, 0, v_im_155_);
v___f_162_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_162_, 0, v_im_152_);
lean_closure_set(v___f_162_, 1, v___f_161_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___f_162_);
lean_ctor_set(v___x_157_, 0, v___f_160_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___f_160_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___f_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart___redArg(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_Q_169_, lean_object* v_A_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v_re_181_; lean_object* v_im_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v_re_187_; lean_object* v_im_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_197_; 
v___f_173_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___closed__0));
lean_inc(v_a_171_);
lean_inc_ref_n(v_Q_169_, 3);
v___f_174_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__1), 3, 2);
lean_closure_set(v___f_174_, 0, v_Q_169_);
lean_closure_set(v___f_174_, 1, v_a_171_);
v___x_175_ = lp_mathlib_Complex_instMul;
v___x_176_ = lp_mathlib_Complex_instAddCommMonoid;
lean_inc_n(v_inst_167_, 3);
lean_inc_ref(v_A_170_);
v___f_177_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_177_, 0, v_A_170_);
lean_closure_set(v___f_177_, 1, v_inst_167_);
lean_closure_set(v___f_177_, 2, v___x_175_);
lean_closure_set(v___f_177_, 3, v___x_176_);
lean_closure_set(v___f_177_, 4, v___f_174_);
v___x_178_ = lp_mathlib_Complex_instZero;
lean_inc(v_a_172_);
lean_inc_ref(v_inst_168_);
v___f_179_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__3), 6, 5);
lean_closure_set(v___f_179_, 0, v_inst_168_);
lean_closure_set(v___f_179_, 1, v___x_178_);
lean_closure_set(v___f_179_, 2, v___f_173_);
lean_closure_set(v___f_179_, 3, v_a_172_);
lean_closure_set(v___f_179_, 4, v_Q_169_);
v___x_180_ = lp_mathlib_dotProduct___redArg(v_inst_167_, v___x_175_, v___x_176_, v___f_177_, v___f_179_);
v_re_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_re_181_);
v_im_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_im_182_);
lean_dec(v___x_180_);
v___f_183_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__0), 3, 2);
lean_closure_set(v___f_183_, 0, v_Q_169_);
lean_closure_set(v___f_183_, 1, v_a_172_);
v___f_184_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossPart___redArg___lam__2), 6, 5);
lean_closure_set(v___f_184_, 0, v_inst_168_);
lean_closure_set(v___f_184_, 1, v___x_178_);
lean_closure_set(v___f_184_, 2, v___f_173_);
lean_closure_set(v___f_184_, 3, v_a_171_);
lean_closure_set(v___f_184_, 4, v_Q_169_);
v___f_185_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_crossTrace___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_185_, 0, v_A_170_);
lean_closure_set(v___f_185_, 1, v_inst_167_);
lean_closure_set(v___f_185_, 2, v___x_175_);
lean_closure_set(v___f_185_, 3, v___x_176_);
lean_closure_set(v___f_185_, 4, v___f_184_);
v___x_186_ = lp_mathlib_dotProduct___redArg(v_inst_167_, v___x_175_, v___x_176_, v___f_185_, v___f_183_);
v_re_187_ = lean_ctor_get(v___x_186_, 0);
v_im_188_ = lean_ctor_get(v___x_186_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_197_ == 0)
{
v___x_190_ = v___x_186_;
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_im_188_);
lean_inc(v_re_187_);
lean_dec(v___x_186_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_195_; 
v___f_192_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_192_, 0, v_re_181_);
lean_closure_set(v___f_192_, 1, v_re_187_);
v___f_193_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_193_, 0, v_im_182_);
lean_closure_set(v___f_193_, 1, v_im_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v___f_193_);
lean_ctor_set(v___x_190_, 0, v___f_192_);
v___x_195_ = v___x_190_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___f_192_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___f_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_crossPart(lean_object* v_n_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_Q_201_, lean_object* v_A_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lp_GRH_New_DiscreteSeries_crossPart___redArg(v_inst_199_, v_inst_200_, v_Q_201_, v_A_202_, v_a_203_, v_a_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_scaleCross___redArg(lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_Q_211_, lean_object* v_A_212_, lean_object* v_00_u03c4_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; lean_object* v_re_217_; lean_object* v_im_218_; lean_object* v___x_219_; lean_object* v_re_220_; lean_object* v_im_221_; lean_object* v_re_222_; lean_object* v_im_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v_re_226_; lean_object* v_im_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_240_; 
lean_inc_ref(v_A_212_);
lean_inc(v_a_215_);
lean_inc(v_a_214_);
v___x_216_ = lean_apply_2(v_A_212_, v_a_214_, v_a_215_);
v_re_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_re_217_);
v_im_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_im_218_);
lean_dec_ref(v___x_216_);
v___x_219_ = lp_GRH_New_DiscreteSeries_crossPart___redArg(v_inst_209_, v_inst_210_, v_Q_211_, v_A_212_, v_a_214_, v_a_215_);
v_re_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_re_220_);
v_im_221_ = lean_ctor_get(v___x_219_, 1);
lean_inc(v_im_221_);
v_re_222_ = lean_ctor_get(v_00_u03c4_213_, 0);
lean_inc(v_re_222_);
v_im_223_ = lean_ctor_get(v_00_u03c4_213_, 1);
lean_inc(v_im_223_);
lean_dec_ref(v_00_u03c4_213_);
v___f_224_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_scaleCross___redArg___closed__1));
v___x_225_ = lp_mathlib_Complex_mulAux___redArg(v___f_224_, v_re_222_, v_im_223_, v___x_219_);
v_re_226_ = lean_ctor_get(v___x_225_, 0);
v_im_227_ = lean_ctor_get(v___x_225_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_240_ == 0)
{
v___x_229_ = v___x_225_;
v_isShared_230_ = v_isSharedCheck_240_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_im_227_);
lean_inc(v_re_226_);
lean_dec(v___x_225_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_240_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___x_238_; 
v___f_231_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_231_, 0, v_re_220_);
v___f_232_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_232_, 0, v_re_217_);
lean_closure_set(v___f_232_, 1, v___f_231_);
v___f_233_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_233_, 0, v_im_221_);
v___f_234_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_234_, 0, v_im_218_);
lean_closure_set(v___f_234_, 1, v___f_233_);
v___f_235_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_235_, 0, v___f_232_);
lean_closure_set(v___f_235_, 1, v_re_226_);
v___f_236_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_236_, 0, v___f_234_);
lean_closure_set(v___f_236_, 1, v_im_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___f_236_);
lean_ctor_set(v___x_229_, 0, v___f_235_);
v___x_238_ = v___x_229_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___f_235_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___f_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_scaleCross(lean_object* v_n_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_Q_244_, lean_object* v_A_245_, lean_object* v_00_u03c4_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lp_GRH_New_DiscreteSeries_scaleCross___redArg(v_inst_242_, v_inst_243_, v_Q_244_, v_A_245_, v_00_u03c4_246_, v_a_247_, v_a_248_);
return v___x_249_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatricesNearIdentity(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Appendix_DiscreteSeries_MinorSecondOrder(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_MatricesNearIdentity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
