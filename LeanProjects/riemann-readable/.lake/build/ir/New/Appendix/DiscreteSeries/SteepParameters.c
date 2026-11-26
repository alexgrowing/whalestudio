// Lean compiler output
// Module: New.Appendix.DiscreteSeries.SteepParameters
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
extern lean_object* lp_mathlib_Complex_instZero;
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_GRH_New_HCParam_lowestKType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instIntCast___lam__0(lean_object*);
extern lean_object* lp_mathlib_Complex_instMul;
lean_object* lp_mathlib_Matrix_trace___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Complex_instSub___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_sub___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instSub___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__1 = (const lean_object*)&lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_00_u03b5_2_, lean_object* v_l_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lp_GRH_New_HCParam_lowestKType___redArg(v_inst_1_, v_00_u03b5_2_, v_l_3_, v_i_4_);
v___x_6_ = lp_mathlib_Complex_instIntCast___lam__0(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__1(lean_object* v_fst_7_, lean_object* v___y_8_, lean_object* v_j_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_2(v_fst_7_, v_j_9_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__2(lean_object* v_inst_11_, lean_object* v___f_12_, lean_object* v___y_13_, lean_object* v_j_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lp_mathlib_Complex_instZero;
v___x_16_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_11_, v___x_15_, v___f_12_, v___y_13_, v_j_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__3(lean_object* v_fst_17_, lean_object* v_inst_18_, lean_object* v___f_19_, lean_object* v_inst_20_, lean_object* v___x_21_, lean_object* v___x_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v___f_25_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__1), 3, 2);
lean_closure_set(v___f_25_, 0, v_fst_17_);
lean_closure_set(v___f_25_, 1, v___y_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__2), 4, 3);
lean_closure_set(v___f_26_, 0, v_inst_18_);
lean_closure_set(v___f_26_, 1, v___f_19_);
lean_closure_set(v___f_26_, 2, v___y_23_);
v___x_27_ = lp_mathlib_dotProduct___redArg(v_inst_20_, v___x_21_, v___x_22_, v___f_26_, v___f_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__3___boxed(lean_object* v_fst_28_, lean_object* v_inst_29_, lean_object* v___f_30_, lean_object* v_inst_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_HCParam_phase___redArg___lam__3(v_fst_28_, v_inst_29_, v___f_30_, v_inst_31_, v___x_32_, v___x_33_, v___y_34_, v___y_35_);
lean_dec_ref(v___x_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__4(lean_object* v_inst_37_, lean_object* v_00_u03b7_38_, lean_object* v_k_39_, lean_object* v_i_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lp_GRH_New_HCParam_lowestKType___redArg(v_inst_37_, v_00_u03b7_38_, v_k_39_, v_i_40_);
v___x_42_ = lp_mathlib_Complex_instIntCast___lam__0(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__5(lean_object* v_snd_43_, lean_object* v___y_44_, lean_object* v_j_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_apply_2(v_snd_43_, v_j_45_, v___y_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__7(lean_object* v_snd_47_, lean_object* v_inst_48_, lean_object* v___f_49_, lean_object* v_inst_50_, lean_object* v___x_51_, lean_object* v___x_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; 
v___f_55_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__5), 3, 2);
lean_closure_set(v___f_55_, 0, v_snd_47_);
lean_closure_set(v___f_55_, 1, v___y_54_);
v___f_56_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__2), 4, 3);
lean_closure_set(v___f_56_, 0, v_inst_48_);
lean_closure_set(v___f_56_, 1, v___f_49_);
lean_closure_set(v___f_56_, 2, v___y_53_);
v___x_57_ = lp_mathlib_dotProduct___redArg(v_inst_50_, v___x_51_, v___x_52_, v___f_56_, v___f_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg___lam__7___boxed(lean_object* v_snd_58_, lean_object* v_inst_59_, lean_object* v___f_60_, lean_object* v_inst_61_, lean_object* v___x_62_, lean_object* v___x_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_GRH_New_HCParam_phase___redArg___lam__7(v_snd_58_, v_inst_59_, v___f_60_, v_inst_61_, v___x_62_, v___x_63_, v___y_64_, v___y_65_);
lean_dec_ref(v___x_63_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_00_u03b5_71_, lean_object* v_l_72_, lean_object* v_00_u03b7_73_, lean_object* v_k_74_, lean_object* v_x_75_){
_start:
{
lean_object* v___x_76_; lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v_re_83_; lean_object* v_im_84_; lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___x_87_; lean_object* v_re_88_; lean_object* v_im_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_100_; 
v___x_76_ = lp_mathlib_Complex_instAddCommMonoid;
v_fst_77_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_fst_77_);
v_snd_78_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_snd_78_);
lean_dec_ref(v_x_75_);
lean_inc_n(v_inst_67_, 2);
v___f_79_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_79_, 0, v_inst_67_);
lean_closure_set(v___f_79_, 1, v_00_u03b5_71_);
lean_closure_set(v___f_79_, 2, v_l_72_);
v___x_80_ = lp_mathlib_Complex_instMul;
v___f_81_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_81_, 0, v_fst_77_);
lean_closure_set(v___f_81_, 1, v_inst_68_);
lean_closure_set(v___f_81_, 2, v___f_79_);
lean_closure_set(v___f_81_, 3, v_inst_67_);
lean_closure_set(v___f_81_, 4, v___x_80_);
lean_closure_set(v___f_81_, 5, v___x_76_);
v___x_82_ = lp_mathlib_Matrix_trace___redArg(v_inst_67_, v___x_76_, v___f_81_);
v_re_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_re_83_);
v_im_84_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_im_84_);
lean_dec(v___x_82_);
lean_inc_n(v_inst_69_, 2);
v___f_85_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__4), 4, 3);
lean_closure_set(v___f_85_, 0, v_inst_69_);
lean_closure_set(v___f_85_, 1, v_00_u03b7_73_);
lean_closure_set(v___f_85_, 2, v_k_74_);
v___f_86_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_phase___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_86_, 0, v_snd_78_);
lean_closure_set(v___f_86_, 1, v_inst_70_);
lean_closure_set(v___f_86_, 2, v___f_85_);
lean_closure_set(v___f_86_, 3, v_inst_69_);
lean_closure_set(v___f_86_, 4, v___x_80_);
lean_closure_set(v___f_86_, 5, v___x_76_);
v___x_87_ = lp_mathlib_Matrix_trace___redArg(v_inst_69_, v___x_76_, v___f_86_);
v_re_88_ = lean_ctor_get(v___x_87_, 0);
v_im_89_ = lean_ctor_get(v___x_87_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_100_ == 0)
{
v___x_91_ = v___x_87_;
v_isShared_92_ = v_isSharedCheck_100_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_im_89_);
lean_inc(v_re_88_);
lean_dec(v___x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_100_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_98_; 
v___f_93_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_93_, 0, v_re_88_);
v___f_94_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_94_, 0, v_re_83_);
lean_closure_set(v___f_94_, 1, v___f_93_);
v___f_95_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_95_, 0, v_im_89_);
v___f_96_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_96_, 0, v_im_84_);
lean_closure_set(v___f_96_, 1, v___f_95_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___f_96_);
lean_ctor_set(v___x_91_, 0, v___f_94_);
v___x_98_ = v___x_91_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___f_94_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___f_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_phase(lean_object* v_n_101_, lean_object* v_m_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_00_u03b5_107_, lean_object* v_l_108_, lean_object* v_00_u03b7_109_, lean_object* v_k_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_GRH_New_HCParam_phase___redArg(v_inst_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_00_u03b5_107_, v_l_108_, v_00_u03b7_109_, v_k_110_, v_x_111_);
return v___x_112_;
}
}
static lean_object* _init_lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_114_ = lp_mathlib_Complex_ofReal(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___closed__0, &lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___closed__0_once, _init_lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___closed__0);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0___boxed(lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_GRH_New_DiscreteSeries_subOnePair___redArg___lam__0(v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_j_123_, lean_object* v_s_124_){
_start:
{
lean_object* v___x_125_; lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_143_; 
v___x_125_ = lean_apply_1(v_j_123_, v_s_124_);
v_fst_126_ = lean_ctor_get(v___x_125_, 0);
v_snd_127_ = lean_ctor_get(v___x_125_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_143_ == 0)
{
v___x_129_ = v___x_125_;
v_isShared_130_ = v_isSharedCheck_143_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_126_);
lean_dec(v___x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_143_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_val_131_; lean_object* v_val_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v_val_131_ = lean_ctor_get(v_fst_126_, 0);
lean_inc(v_val_131_);
lean_dec(v_fst_126_);
v_val_132_ = lean_ctor_get(v_snd_127_, 0);
lean_inc(v_val_132_);
lean_dec(v_snd_127_);
v___f_133_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__0));
v___f_134_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__1));
v___x_135_ = lp_mathlib_Complex_instZero;
v___x_136_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_136_, 0, lean_box(0));
lean_closure_set(v___x_136_, 1, lean_box(0));
lean_closure_set(v___x_136_, 2, v_inst_121_);
lean_closure_set(v___x_136_, 3, v___x_135_);
lean_closure_set(v___x_136_, 4, v___f_133_);
v___x_137_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_sub___aux__1), 8, 6);
lean_closure_set(v___x_137_, 0, lean_box(0));
lean_closure_set(v___x_137_, 1, lean_box(0));
lean_closure_set(v___x_137_, 2, lean_box(0));
lean_closure_set(v___x_137_, 3, v___f_134_);
lean_closure_set(v___x_137_, 4, v_val_131_);
lean_closure_set(v___x_137_, 5, v___x_136_);
v___x_138_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_138_, 0, lean_box(0));
lean_closure_set(v___x_138_, 1, lean_box(0));
lean_closure_set(v___x_138_, 2, v_inst_122_);
lean_closure_set(v___x_138_, 3, v___x_135_);
lean_closure_set(v___x_138_, 4, v___f_133_);
v___x_139_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_sub___aux__1), 8, 6);
lean_closure_set(v___x_139_, 0, lean_box(0));
lean_closure_set(v___x_139_, 1, lean_box(0));
lean_closure_set(v___x_139_, 2, lean_box(0));
lean_closure_set(v___x_139_, 3, v___f_134_);
lean_closure_set(v___x_139_, 4, v_val_132_);
lean_closure_set(v___x_139_, 5, v___x_138_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_139_);
lean_ctor_set(v___x_129_, 0, v___x_137_);
v___x_141_ = v___x_129_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair(lean_object* v_n_144_, lean_object* v_m_145_, lean_object* v_S_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_00_u03b5_152_, lean_object* v_00_u03b7_153_, lean_object* v_j_154_, lean_object* v_s_155_){
_start:
{
lean_object* v___x_156_; lean_object* v_fst_157_; lean_object* v_snd_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_174_; 
v___x_156_ = lean_apply_1(v_j_154_, v_s_155_);
v_fst_157_ = lean_ctor_get(v___x_156_, 0);
v_snd_158_ = lean_ctor_get(v___x_156_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_174_ == 0)
{
v___x_160_ = v___x_156_;
v_isShared_161_ = v_isSharedCheck_174_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snd_158_);
lean_inc(v_fst_157_);
lean_dec(v___x_156_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_174_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_val_162_; lean_object* v_val_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v_val_162_ = lean_ctor_get(v_fst_157_, 0);
lean_inc(v_val_162_);
lean_dec(v_fst_157_);
v_val_163_ = lean_ctor_get(v_snd_158_, 0);
lean_inc(v_val_163_);
lean_dec(v_snd_158_);
v___f_164_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__0));
v___f_165_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_subOnePair___redArg___closed__1));
v___x_166_ = lp_mathlib_Complex_instZero;
v___x_167_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_167_, 0, lean_box(0));
lean_closure_set(v___x_167_, 1, lean_box(0));
lean_closure_set(v___x_167_, 2, v_inst_148_);
lean_closure_set(v___x_167_, 3, v___x_166_);
lean_closure_set(v___x_167_, 4, v___f_164_);
v___x_168_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_sub___aux__1), 8, 6);
lean_closure_set(v___x_168_, 0, lean_box(0));
lean_closure_set(v___x_168_, 1, lean_box(0));
lean_closure_set(v___x_168_, 2, lean_box(0));
lean_closure_set(v___x_168_, 3, v___f_165_);
lean_closure_set(v___x_168_, 4, v_val_162_);
lean_closure_set(v___x_168_, 5, v___x_167_);
v___x_169_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_169_, 0, lean_box(0));
lean_closure_set(v___x_169_, 1, lean_box(0));
lean_closure_set(v___x_169_, 2, v_inst_150_);
lean_closure_set(v___x_169_, 3, v___x_166_);
lean_closure_set(v___x_169_, 4, v___f_164_);
v___x_170_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_sub___aux__1), 8, 6);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, lean_box(0));
lean_closure_set(v___x_170_, 2, lean_box(0));
lean_closure_set(v___x_170_, 3, v___f_165_);
lean_closure_set(v___x_170_, 4, v_val_163_);
lean_closure_set(v___x_170_, 5, v___x_169_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_170_);
lean_ctor_set(v___x_160_, 0, v___x_168_);
v___x_172_ = v___x_160_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_subOnePair___boxed(lean_object* v_n_175_, lean_object* v_m_176_, lean_object* v_S_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_00_u03b5_183_, lean_object* v_00_u03b7_184_, lean_object* v_j_185_, lean_object* v_s_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = lp_GRH_New_DiscreteSeries_subOnePair(v_n_175_, v_m_176_, v_S_177_, v_inst_178_, v_inst_179_, v_inst_180_, v_inst_181_, v_inst_182_, v_00_u03b5_183_, v_00_u03b7_184_, v_j_185_, v_s_186_);
lean_dec_ref(v_00_u03b7_184_);
lean_dec_ref(v_00_u03b5_183_);
lean_dec_ref(v_inst_182_);
lean_dec(v_inst_180_);
lean_dec(v_inst_178_);
return v_res_187_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_MatricesNearIdentity(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Appendix_DiscreteSeries_SteepParameters(uint8_t builtin) {
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
