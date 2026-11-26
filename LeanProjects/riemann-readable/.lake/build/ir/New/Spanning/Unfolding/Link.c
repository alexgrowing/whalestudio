// Lean compiler output
// Module: New.Spanning.Unfolding.Link
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bruhat.BigCell public import New.Spanning.Unfolding.Terms
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
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_funLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Filling_positiveGram___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__3(lean_object*);
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_linkSource___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_linkSource___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_linkSource___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__2_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Filling_linkSource___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__3 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__3_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__0_value),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__1_value)} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__4 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__4_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__2_value),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__3_value)} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__5 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__5_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__4_value),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__5_value)} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__6 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__6_value;
static const lean_closure_object lp_GRH_New_Filling_linkSource___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_funLeft___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__6_value)} };
static const lean_object* lp_GRH_New_Filling_linkSource___redArg___closed__7 = (const lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__7_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Filling_linkSource___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Filling_linkSource___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Filling_linkTarget___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__2_value),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__1_value)} };
static const lean_object* lp_GRH_New_Filling_linkTarget___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Filling_linkTarget___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__0_value),((lean_object*)&lp_GRH_New_Filling_linkSource___redArg___closed__3_value)} };
static const lean_object* lp_GRH_New_Filling_linkTarget___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_Filling_linkTarget___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__0_value),((lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__1_value)} };
static const lean_object* lp_GRH_New_Filling_linkTarget___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__2_value;
static const lean_closure_object lp_GRH_New_Filling_linkTarget___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_funLeft___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__2_value)} };
static const lean_object* lp_GRH_New_Filling_linkTarget___redArg___closed__3 = (const lean_object*)&lp_GRH_New_Filling_linkTarget___redArg___closed__3_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Filling_linkTarget___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Filling_linkTarget___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Filling_isotropicSpan___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_00_U0001d530_7_, lean_object* v_M_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_isotropicSpan___boxed(lean_object* v_E_10_, lean_object* v_inst_11_, lean_object* v_00_U0001d530_12_, lean_object* v_M_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Filling_isotropicSpan(v_E_10_, v_inst_11_, v_00_U0001d530_12_, v_M_13_);
lean_dec(v_M_13_);
lean_dec_ref(v_00_U0001d530_12_);
lean_dec_ref(v_inst_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic___redArg(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_Filling_commonIsotropic___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic(lean_object* v_E_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_00_U0001d530_22_, lean_object* v_S_23_, lean_object* v_00_u03b3_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_commonIsotropic___boxed(lean_object* v_E_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_00_U0001d530_29_, lean_object* v_S_30_, lean_object* v_00_u03b3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_Filling_commonIsotropic(v_E_26_, v_inst_27_, v_inst_28_, v_00_U0001d530_29_, v_S_30_, v_00_u03b3_31_);
lean_dec_ref(v_00_u03b3_31_);
lean_dec_ref(v_S_30_);
lean_dec_ref(v_00_U0001d530_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
return v_res_32_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Filling_positiveGram___redArg___lam__0(lean_object* v_00_U0001d530_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_decEqIndex_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_decEqIndex_36_ = lean_ctor_get(v_00_U0001d530_33_, 2);
lean_inc_ref(v_decEqIndex_36_);
lean_dec_ref(v_00_U0001d530_33_);
v___x_37_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_38_ = l_instDecidableEqSum_decEq___redArg(v_decEqIndex_36_, v___x_37_, v_a_34_, v_b_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__0___boxed(lean_object* v_00_U0001d530_39_, lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lp_GRH_New_Filling_positiveGram___redArg___lam__0(v_00_U0001d530_39_, v_a_40_, v_b_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__1(lean_object* v_toOne_44_, lean_object* v_x_45_){
_start:
{
lean_inc(v_toOne_44_);
return v_toOne_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__1___boxed(lean_object* v_toOne_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_Filling_positiveGram___redArg___lam__1(v_toOne_46_, v_x_47_);
lean_dec(v_x_47_);
lean_dec(v_toOne_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg___lam__2(lean_object* v_S_49_, lean_object* v_toNatCast_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_N_52_; lean_object* v___x_53_; 
v_N_52_ = lean_ctor_get(v_S_49_, 0);
lean_inc(v_N_52_);
lean_dec_ref(v_S_49_);
v___x_53_ = lean_apply_1(v_toNatCast_50_, v_N_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___redArg(lean_object* v_inst_54_, lean_object* v_00_U0001d530_55_, lean_object* v_S_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; lean_object* v_toCommSemiring_60_; lean_object* v___x_61_; lean_object* v_toZero_62_; lean_object* v___x_63_; lean_object* v_toRing_64_; lean_object* v___x_65_; lean_object* v_toAddMonoidWithOne_66_; lean_object* v_toNatCast_67_; lean_object* v_toOne_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_59_ = lp_mathlib_Field_toSemifield___redArg(v_inst_54_);
v_toCommSemiring_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_toCommSemiring_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_60_);
v_toZero_62_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_toZero_62_);
lean_dec_ref(v___x_61_);
v___x_63_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_54_);
v_toRing_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_toRing_64_);
lean_dec_ref(v___x_63_);
v___x_65_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_64_);
v_toAddMonoidWithOne_66_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_toAddMonoidWithOne_66_);
lean_dec_ref(v___x_65_);
v_toNatCast_67_ = lean_ctor_get(v_toAddMonoidWithOne_66_, 0);
lean_inc(v_toNatCast_67_);
v_toOne_68_ = lean_ctor_get(v_toAddMonoidWithOne_66_, 2);
lean_inc(v_toOne_68_);
lean_dec_ref(v_toAddMonoidWithOne_66_);
v___f_69_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_positiveGram___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_69_, 0, v_00_U0001d530_55_);
v___f_70_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_positiveGram___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_70_, 0, v_toOne_68_);
v___f_71_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_positiveGram___redArg___lam__2), 3, 2);
lean_closure_set(v___f_71_, 0, v_S_56_);
lean_closure_set(v___f_71_, 1, v_toNatCast_67_);
v___x_72_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_72_, 0, lean_box(0));
lean_closure_set(v___x_72_, 1, lean_box(0));
lean_closure_set(v___x_72_, 2, lean_box(0));
lean_closure_set(v___x_72_, 3, v___f_70_);
lean_closure_set(v___x_72_, 4, v___f_71_);
v___x_73_ = lp_mathlib_Matrix_diagonal___redArg(v___f_69_, v_toZero_62_, v___x_72_, v_a_57_, v_a_58_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram(lean_object* v_E_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_00_U0001d530_77_, lean_object* v_S_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_GRH_New_Filling_positiveGram___redArg(v_inst_75_, v_00_U0001d530_77_, v_S_78_, v_a_79_, v_a_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_positiveGram___boxed(lean_object* v_E_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_00_U0001d530_85_, lean_object* v_S_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_GRH_New_Filling_positiveGram(v_E_82_, v_inst_83_, v_inst_84_, v_00_U0001d530_85_, v_S_86_, v_a_87_, v_a_88_);
lean_dec_ref(v_inst_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__0(lean_object* v_val_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v_val_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__1(lean_object* v_val_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_val_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__2(lean_object* v_val_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_val_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___lam__3(lean_object* v_val_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_val_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg(){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = ((lean_object*)(lp_GRH_New_Filling_linkSource___redArg___closed__7));
return v___f_114_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___redArg___boxed(lean_object* v___dummy_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_GRH_New_Filling_linkSource___redArg();
return v_res_116_;
}
}
static lean_object* _init_lp_GRH_New_Filling_linkSource___closed__0(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lp_GRH_New_Filling_linkSource___redArg();
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource(lean_object* v_E_118_, lean_object* v_inst_119_, lean_object* v_00_U0001d530_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_once(&lp_GRH_New_Filling_linkSource___closed__0, &lp_GRH_New_Filling_linkSource___closed__0_once, _init_lp_GRH_New_Filling_linkSource___closed__0);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkSource___boxed(lean_object* v_E_122_, lean_object* v_inst_123_, lean_object* v_00_U0001d530_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_GRH_New_Filling_linkSource(v_E_122_, v_inst_123_, v_00_U0001d530_124_);
lean_dec_ref(v_00_U0001d530_124_);
lean_dec_ref(v_inst_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget___redArg(){
_start:
{
lean_object* v___f_138_; 
v___f_138_ = ((lean_object*)(lp_GRH_New_Filling_linkTarget___redArg___closed__3));
return v___f_138_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget___redArg___boxed(lean_object* v___dummy_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_GRH_New_Filling_linkTarget___redArg();
return v_res_140_;
}
}
static lean_object* _init_lp_GRH_New_Filling_linkTarget___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lp_GRH_New_Filling_linkTarget___redArg();
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget(lean_object* v_E_142_, lean_object* v_inst_143_, lean_object* v_00_U0001d530_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&lp_GRH_New_Filling_linkTarget___closed__0, &lp_GRH_New_Filling_linkTarget___closed__0_once, _init_lp_GRH_New_Filling_linkTarget___closed__0);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_linkTarget___boxed(lean_object* v_E_146_, lean_object* v_inst_147_, lean_object* v_00_U0001d530_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_GRH_New_Filling_linkTarget(v_E_146_, v_inst_147_, v_00_U0001d530_148_);
lean_dec_ref(v_00_U0001d530_148_);
lean_dec_ref(v_inst_147_);
return v_res_149_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bruhat_BigCell(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Unfolding_Terms(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Unfolding_Link(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bruhat_BigCell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Unfolding_Terms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
