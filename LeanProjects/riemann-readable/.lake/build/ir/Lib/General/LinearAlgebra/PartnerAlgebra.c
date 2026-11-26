// Lean compiler output
// Module: Lib.General.LinearAlgebra.PartnerAlgebra
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.ComponentsAndBlockSums public import Lib.General.LinearAlgebra.HermiteForm
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
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___redArg___lam__1(lean_object*);
static const lean_closure_object lp_GRH_New_invLastRows___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_invLastRows___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_invLastRows___redArg___closed__0 = (const lean_object*)&lp_GRH_New_invLastRows___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_invLastRows___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_invLastRows___redArg___closed__1 = (const lean_object*)&lp_GRH_New_invLastRows___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_firstCols___redArg___lam__1(lean_object*);
static const lean_closure_object lp_GRH_New_firstCols___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_firstCols___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_firstCols___redArg___closed__0 = (const lean_object*)&lp_GRH_New_firstCols___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_firstCols___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_firstCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_firstCols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invFirstRows___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invFirstRows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invFirstRows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___redArg___lam__0(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
lean_object* v_toFun_3_; lean_object* v___x_4_; 
v_toFun_3_ = lean_ctor_get(v_e_1_, 0);
lean_inc(v_toFun_3_);
lean_dec_ref(v_e_1_);
v___x_4_ = lean_apply_1(v_toFun_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___redArg___lam__1(lean_object* v_val_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_val_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___redArg(lean_object* v_e_9_, lean_object* v_k_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_inv_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_inv_13_ = lean_ctor_get(v_k_10_, 1);
lean_inc(v_inv_13_);
lean_dec_ref(v_k_10_);
v___f_14_ = lean_alloc_closure((void*)(lp_GRH_New_invLastRows___redArg___lam__0), 2, 1);
lean_closure_set(v___f_14_, 0, v_e_9_);
v___f_15_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__0));
v___x_16_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_16_, 0, lean_box(0));
lean_closure_set(v___x_16_, 1, lean_box(0));
lean_closure_set(v___x_16_, 2, lean_box(0));
lean_closure_set(v___x_16_, 3, v___f_14_);
lean_closure_set(v___x_16_, 4, v___f_15_);
v___x_17_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__1));
v___x_18_ = lp_mathlib_Matrix_submatrix___redArg(v_inv_13_, v___x_16_, v___x_17_, v_a_11_, v_a_12_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows(lean_object* v_R_19_, lean_object* v_a_20_, lean_object* v_b_21_, lean_object* v_n_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_e_26_, lean_object* v_k_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_inv_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_inv_30_ = lean_ctor_get(v_k_27_, 1);
lean_inc(v_inv_30_);
lean_dec_ref(v_k_27_);
v___f_31_ = lean_alloc_closure((void*)(lp_GRH_New_invLastRows___redArg___lam__0), 2, 1);
lean_closure_set(v___f_31_, 0, v_e_26_);
v___f_32_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__0));
v___x_33_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_33_, 0, lean_box(0));
lean_closure_set(v___x_33_, 1, lean_box(0));
lean_closure_set(v___x_33_, 2, lean_box(0));
lean_closure_set(v___x_33_, 3, v___f_31_);
lean_closure_set(v___x_33_, 4, v___f_32_);
v___x_34_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__1));
v___x_35_ = lp_mathlib_Matrix_submatrix___redArg(v_inv_30_, v___x_33_, v___x_34_, v_a_28_, v_a_29_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invLastRows___boxed(lean_object* v_R_36_, lean_object* v_a_37_, lean_object* v_b_38_, lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_e_43_, lean_object* v_k_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_GRH_New_invLastRows(v_R_36_, v_a_37_, v_b_38_, v_n_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_e_43_, v_k_44_, v_a_45_, v_a_46_);
lean_dec_ref(v_inst_42_);
lean_dec(v_inst_41_);
lean_dec_ref(v_inst_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_firstCols___redArg___lam__1(lean_object* v_val_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v_val_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_firstCols___redArg(lean_object* v_e_51_, lean_object* v_k_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_val_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_val_55_ = lean_ctor_get(v_k_52_, 0);
lean_inc(v_val_55_);
lean_dec_ref(v_k_52_);
v___f_56_ = lean_alloc_closure((void*)(lp_GRH_New_invLastRows___redArg___lam__0), 2, 1);
lean_closure_set(v___f_56_, 0, v_e_51_);
v___f_57_ = ((lean_object*)(lp_GRH_New_firstCols___redArg___closed__0));
v___x_58_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__1));
v___x_59_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_59_, 0, lean_box(0));
lean_closure_set(v___x_59_, 1, lean_box(0));
lean_closure_set(v___x_59_, 2, lean_box(0));
lean_closure_set(v___x_59_, 3, v___f_56_);
lean_closure_set(v___x_59_, 4, v___f_57_);
v___x_60_ = lp_mathlib_Matrix_submatrix___redArg(v_val_55_, v___x_58_, v___x_59_, v_a_53_, v_a_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_firstCols(lean_object* v_R_61_, lean_object* v_a_62_, lean_object* v_b_63_, lean_object* v_n_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_e_68_, lean_object* v_k_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_val_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_val_72_ = lean_ctor_get(v_k_69_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v_k_69_);
v___f_73_ = lean_alloc_closure((void*)(lp_GRH_New_invLastRows___redArg___lam__0), 2, 1);
lean_closure_set(v___f_73_, 0, v_e_68_);
v___f_74_ = ((lean_object*)(lp_GRH_New_firstCols___redArg___closed__0));
v___x_75_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__1));
v___x_76_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_76_, 0, lean_box(0));
lean_closure_set(v___x_76_, 1, lean_box(0));
lean_closure_set(v___x_76_, 2, lean_box(0));
lean_closure_set(v___x_76_, 3, v___f_73_);
lean_closure_set(v___x_76_, 4, v___f_74_);
v___x_77_ = lp_mathlib_Matrix_submatrix___redArg(v_val_72_, v___x_75_, v___x_76_, v_a_70_, v_a_71_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_firstCols___boxed(lean_object* v_R_78_, lean_object* v_a_79_, lean_object* v_b_80_, lean_object* v_n_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_e_85_, lean_object* v_k_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_GRH_New_firstCols(v_R_78_, v_a_79_, v_b_80_, v_n_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_e_85_, v_k_86_, v_a_87_, v_a_88_);
lean_dec_ref(v_inst_84_);
lean_dec(v_inst_83_);
lean_dec_ref(v_inst_82_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invFirstRows___redArg(lean_object* v_e_90_, lean_object* v_k_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_inv_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_inv_94_ = lean_ctor_get(v_k_91_, 1);
lean_inc(v_inv_94_);
lean_dec_ref(v_k_91_);
v___f_95_ = lean_alloc_closure((void*)(lp_GRH_New_invLastRows___redArg___lam__0), 2, 1);
lean_closure_set(v___f_95_, 0, v_e_90_);
v___f_96_ = ((lean_object*)(lp_GRH_New_firstCols___redArg___closed__0));
v___x_97_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_97_, 0, lean_box(0));
lean_closure_set(v___x_97_, 1, lean_box(0));
lean_closure_set(v___x_97_, 2, lean_box(0));
lean_closure_set(v___x_97_, 3, v___f_95_);
lean_closure_set(v___x_97_, 4, v___f_96_);
v___x_98_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__1));
v___x_99_ = lp_mathlib_Matrix_submatrix___redArg(v_inv_94_, v___x_97_, v___x_98_, v_a_92_, v_a_93_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invFirstRows(lean_object* v_R_100_, lean_object* v_a_101_, lean_object* v_b_102_, lean_object* v_n_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_e_107_, lean_object* v_k_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_inv_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_inv_111_ = lean_ctor_get(v_k_108_, 1);
lean_inc(v_inv_111_);
lean_dec_ref(v_k_108_);
v___f_112_ = lean_alloc_closure((void*)(lp_GRH_New_invLastRows___redArg___lam__0), 2, 1);
lean_closure_set(v___f_112_, 0, v_e_107_);
v___f_113_ = ((lean_object*)(lp_GRH_New_firstCols___redArg___closed__0));
v___x_114_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_114_, 0, lean_box(0));
lean_closure_set(v___x_114_, 1, lean_box(0));
lean_closure_set(v___x_114_, 2, lean_box(0));
lean_closure_set(v___x_114_, 3, v___f_112_);
lean_closure_set(v___x_114_, 4, v___f_113_);
v___x_115_ = ((lean_object*)(lp_GRH_New_invLastRows___redArg___closed__1));
v___x_116_ = lp_mathlib_Matrix_submatrix___redArg(v_inv_111_, v___x_114_, v___x_115_, v_a_109_, v_a_110_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_invFirstRows___boxed(lean_object* v_R_117_, lean_object* v_a_118_, lean_object* v_b_119_, lean_object* v_n_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_e_124_, lean_object* v_k_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_GRH_New_invFirstRows(v_R_117_, v_a_118_, v_b_119_, v_n_120_, v_inst_121_, v_inst_122_, v_inst_123_, v_e_124_, v_k_125_, v_a_126_, v_a_127_);
lean_dec_ref(v_inst_123_);
lean_dec(v_inst_122_);
lean_dec_ref(v_inst_121_);
return v_res_128_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_ComponentsAndBlockSums(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_HermiteForm(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_LinearAlgebra_PartnerAlgebra(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_ComponentsAndBlockSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_HermiteForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
