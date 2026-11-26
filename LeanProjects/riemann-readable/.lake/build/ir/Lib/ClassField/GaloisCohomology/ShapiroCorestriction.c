// Lean compiler output
// Module: Lib.ClassField.GaloisCohomology.ShapiroCorestriction
// Imports: public import Init public meta import Init public import Lib.General.Groups.ProfiniteCharacters
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
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_Function_eval(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_pairMapH2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteModule_shapiroH2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteModule_shapiroH2___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteModule_shapiroH2___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___redArg___lam__0(lean_object* v_toOne_1_, lean_object* v_f_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_f_2_, v___y_3_, v_toOne_1_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___redArg(lean_object* v_inst_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_toOne_7_; lean_object* v___f_8_; 
v___x_6_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_5_);
v_toOne_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_toOne_7_);
lean_dec_ref(v___x_6_);
v___f_8_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteModule_shapiroZ1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_8_, 0, v_toOne_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___redArg___boxed(lean_object* v_inst_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_GRH_New_DiscreteModule_shapiroZ1___redArg(v_inst_9_);
lean_dec_ref(v_inst_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1(lean_object* v_R_11_, lean_object* v_00_u0393_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_M_17_, lean_object* v_inst_18_, lean_object* v_U_19_){
_start:
{
lean_object* v___x_20_; lean_object* v_toOne_21_; lean_object* v___f_22_; 
v___x_20_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_14_);
v_toOne_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_toOne_21_);
lean_dec_ref(v___x_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteModule_shapiroZ1___redArg___lam__0), 3, 1);
lean_closure_set(v___f_22_, 0, v_toOne_21_);
return v___f_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroZ1___boxed(lean_object* v_R_23_, lean_object* v_00_u0393_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_M_29_, lean_object* v_inst_30_, lean_object* v_U_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_DiscreteModule_shapiroZ1(v_R_23_, v_00_u0393_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_M_29_, v_inst_30_, v_U_31_);
lean_dec_ref(v_M_29_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2___redArg(lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_M_36_){
_start:
{
lean_object* v_addCommGroup_37_; lean_object* v_moduleR_38_; lean_object* v___x_39_; lean_object* v_toOne_40_; lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_addCommGroup_37_ = lean_ctor_get(v_M_36_, 0);
lean_inc_ref(v_addCommGroup_37_);
v_moduleR_38_ = lean_ctor_get(v_M_36_, 1);
lean_inc(v_moduleR_38_);
lean_dec_ref(v_M_36_);
v___x_39_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_35_);
v_toOne_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_toOne_40_);
lean_dec_ref(v___x_39_);
v___f_41_ = ((lean_object*)(lp_GRH_New_DiscreteModule_shapiroH2___redArg___closed__0));
v___x_42_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_42_, 0, lean_box(0));
lean_closure_set(v___x_42_, 1, lean_box(0));
lean_closure_set(v___x_42_, 2, v_toOne_40_);
v___x_43_ = lp_GRH_New_pairMapH2___redArg(v_inst_34_, v_addCommGroup_37_, v_moduleR_38_, v___f_41_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2___redArg___boxed(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_M_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_GRH_New_DiscreteModule_shapiroH2___redArg(v_inst_44_, v_inst_45_, v_M_46_);
lean_dec_ref(v_inst_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2(lean_object* v_R_48_, lean_object* v_00_u0393_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_M_54_, lean_object* v_inst_55_, lean_object* v_U_56_){
_start:
{
lean_object* v_addCommGroup_57_; lean_object* v_moduleR_58_; lean_object* v___x_59_; lean_object* v_toOne_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_addCommGroup_57_ = lean_ctor_get(v_M_54_, 0);
lean_inc_ref(v_addCommGroup_57_);
v_moduleR_58_ = lean_ctor_get(v_M_54_, 1);
lean_inc(v_moduleR_58_);
lean_dec_ref(v_M_54_);
v___x_59_ = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(v_inst_51_);
v_toOne_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_toOne_60_);
lean_dec_ref(v___x_59_);
v___f_61_ = ((lean_object*)(lp_GRH_New_DiscreteModule_shapiroH2___redArg___closed__0));
v___x_62_ = lean_alloc_closure((void*)(lp_mathlib_Function_eval), 4, 3);
lean_closure_set(v___x_62_, 0, lean_box(0));
lean_closure_set(v___x_62_, 1, lean_box(0));
lean_closure_set(v___x_62_, 2, v_toOne_60_);
v___x_63_ = lp_GRH_New_pairMapH2___redArg(v_inst_50_, v_addCommGroup_57_, v_moduleR_58_, v___f_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_shapiroH2___boxed(lean_object* v_R_64_, lean_object* v_00_u0393_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_M_70_, lean_object* v_inst_71_, lean_object* v_U_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_GRH_New_DiscreteModule_shapiroH2(v_R_64_, v_00_u0393_65_, v_inst_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_M_70_, v_inst_71_, v_U_72_);
lean_dec_ref(v_inst_67_);
return v_res_73_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_ProfiniteCharacters(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_GaloisCohomology_ShapiroCorestriction(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_Groups_ProfiniteCharacters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
