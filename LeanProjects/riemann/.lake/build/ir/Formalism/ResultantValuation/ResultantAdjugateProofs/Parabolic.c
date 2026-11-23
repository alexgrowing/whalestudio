// Lean compiler output
// Module: Formalism.ResultantValuation.ResultantAdjugateProofs.Parabolic
// Imports: public import Init public meta import Init public import Formalism.ResultantValuation.SubspaceCount
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
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_toLin___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_GeneralLinearGroup_generalLinearEquiv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_firstBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_firstBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___closed__0 = (const lean_object*)&lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_firstBlock(lean_object* v_F_1_, lean_object* v_inst_2_, lean_object* v_r_3_, lean_object* v_t_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_firstBlock___boxed(lean_object* v_F_6_, lean_object* v_inst_7_, lean_object* v_r_8_, lean_object* v_t_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_firstBlock(v_F_6_, v_inst_7_, v_r_8_, v_t_9_);
lean_dec(v_t_9_);
lean_dec(v_r_8_);
lean_dec_ref(v_inst_7_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___lam__0(lean_object* v_g_11_, lean_object* v_W_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___lam__0___boxed(lean_object* v_g_14_, lean_object* v_W_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___lam__0(v_g_14_, v_W_15_);
lean_dec_ref(v_g_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act(lean_object* v_F_18_, lean_object* v_inst_19_, lean_object* v_r_20_, lean_object* v_t_21_){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = ((lean_object*)(lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___closed__0));
return v___f_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_act___boxed(lean_object* v_F_23_, lean_object* v_inst_24_, lean_object* v_r_25_, lean_object* v_t_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_act(v_F_23_, v_inst_24_, v_r_25_, v_t_26_);
lean_dec(v_t_26_);
lean_dec(v_r_25_);
lean_dec_ref(v_inst_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___lam__0(lean_object* v_toAddCommMonoid_28_, lean_object* v_i_29_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_28_);
return v_toAddCommMonoid_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_30_, lean_object* v_i_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___lam__0(v_toAddCommMonoid_30_, v_i_31_);
lean_dec(v_i_31_);
lean_dec_ref(v_toAddCommMonoid_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg(lean_object* v_inst_33_, lean_object* v_r_34_, lean_object* v_t_35_, lean_object* v_g_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v_toSemiring_39_; lean_object* v_toAddCommMonoid_40_; lean_object* v_toCommRing_41_; lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v_toFun_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_toFun_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_37_ = lp_mathlib_Field_toSemifield___redArg(v_inst_33_);
v___x_38_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_37_);
v_toSemiring_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_toSemiring_39_);
lean_dec_ref(v___x_38_);
v_toAddCommMonoid_40_ = lean_ctor_get(v_toSemiring_39_, 0);
v_toCommRing_41_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toCommRing_41_);
lean_dec_ref(v_inst_33_);
lean_inc_ref(v_toAddCommMonoid_40_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_42_, 0, v_toAddCommMonoid_40_);
v___x_43_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_42_);
v___x_44_ = lean_nat_add(v_r_34_, v_t_35_);
lean_inc(v___x_44_);
v___x_45_ = l_List_finRange(v___x_44_);
v___x_46_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_46_, 0, v___x_44_);
v___x_47_ = lp_mathlib_Matrix_GeneralLinearGroup_toLin___redArg(v___x_46_, v___x_45_, v_toCommRing_41_);
v_toFun_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_toFun_48_);
lean_dec_ref(v___x_47_);
v___x_49_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_39_);
v___x_50_ = lp_mathlib_Pi_Function_module___redArg(v___x_49_);
v___x_51_ = lp_mathlib_LinearMap_GeneralLinearGroup_generalLinearEquiv___redArg(v_toSemiring_39_, v___x_43_, v___x_50_);
v_toFun_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_toFun_52_);
lean_dec_ref(v___x_51_);
v___x_53_ = lean_apply_1(v_toFun_48_, v_g_36_);
v___x_54_ = lean_apply_1(v_toFun_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg___boxed(lean_object* v_inst_55_, lean_object* v_r_56_, lean_object* v_t_57_, lean_object* v_g_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg(v_inst_55_, v_r_56_, v_t_57_, v_g_58_);
lean_dec(v_t_57_);
lean_dec(v_r_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv(lean_object* v_F_60_, lean_object* v_inst_61_, lean_object* v_r_62_, lean_object* v_t_63_, lean_object* v_g_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___redArg(v_inst_61_, v_r_62_, v_t_63_, v_g_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv___boxed(lean_object* v_F_66_, lean_object* v_inst_67_, lean_object* v_r_68_, lean_object* v_t_69_, lean_object* v_g_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_ResultantValuation_ParabolicCounting_lequiv(v_F_66_, v_inst_67_, v_r_68_, v_t_69_, v_g_70_);
lean_dec(v_t_69_);
lean_dec(v_r_68_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_ResultantValuation_SubspaceCount(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ResultantValuation_SubspaceCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
