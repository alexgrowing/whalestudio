// Lean compiler output
// Module: Lib.ClassField.GreenbergWiles.RelationsModL
// Imports: public import Init public meta import Init public import Lib.ClassField.GreenbergWiles.Relations
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
lean_object* lp_mathlib_AddSubgroupClass_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Representation_subrepresentation___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_torsion___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_torsion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_torsion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_RelationSetting_reductions___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions(lean_object* v_K_5_, lean_object* v_R_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_M_10_, lean_object* v_m_11_, lean_object* v_inst_12_, lean_object* v_D_13_, lean_object* v_00_u2113_14_, lean_object* v_T_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_reductions___boxed(lean_object* v_K_17_, lean_object* v_R_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_M_22_, lean_object* v_m_23_, lean_object* v_inst_24_, lean_object* v_D_25_, lean_object* v_00_u2113_26_, lean_object* v_T_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_RelationSetting_reductions(v_K_17_, v_R_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_M_22_, v_m_23_, v_inst_24_, v_D_25_, v_00_u2113_26_, v_T_27_);
lean_dec(v_T_27_);
lean_dec(v_00_u2113_26_);
lean_dec_ref(v_D_25_);
lean_dec(v_m_23_);
lean_dec_ref(v_M_22_);
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_torsion___redArg(lean_object* v_M_29_){
_start:
{
lean_object* v_addCommGroup_30_; lean_object* v_moduleR_31_; lean_object* v_00_u03c1_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_43_; 
v_addCommGroup_30_ = lean_ctor_get(v_M_29_, 0);
v_moduleR_31_ = lean_ctor_get(v_M_29_, 1);
v_00_u03c1_32_ = lean_ctor_get(v_M_29_, 3);
v_isSharedCheck_43_ = !lean_is_exclusive(v_M_29_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v_M_29_, 2);
lean_dec(v_unused_44_);
v___x_34_ = v_M_29_;
v_isShared_35_ = v_isSharedCheck_43_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_00_u03c1_32_);
lean_inc(v_moduleR_31_);
lean_inc(v_addCommGroup_30_);
lean_dec(v_M_29_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_43_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___f_39_; lean_object* v___x_41_; 
v___x_36_ = lp_mathlib_AddSubgroupClass_toAddGroup___redArg(v_addCommGroup_30_);
v___f_37_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_smul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_37_, 0, v_moduleR_31_);
v___x_38_ = lean_box(0);
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_Representation_subrepresentation___redArg___lam__0), 3, 1);
lean_closure_set(v___f_39_, 0, v_00_u03c1_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 3, v___f_39_);
lean_ctor_set(v___x_34_, 2, v___x_38_);
lean_ctor_set(v___x_34_, 1, v___f_37_);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_41_ = v___x_34_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 3, v___f_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_torsion(lean_object* v_R_45_, lean_object* v_G_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_M_50_, lean_object* v_00_u2113_51_){
_start:
{
lean_object* v_addCommGroup_52_; lean_object* v_moduleR_53_; lean_object* v_00_u03c1_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_65_; 
v_addCommGroup_52_ = lean_ctor_get(v_M_50_, 0);
v_moduleR_53_ = lean_ctor_get(v_M_50_, 1);
v_00_u03c1_54_ = lean_ctor_get(v_M_50_, 3);
v_isSharedCheck_65_ = !lean_is_exclusive(v_M_50_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v_M_50_, 2);
lean_dec(v_unused_66_);
v___x_56_ = v_M_50_;
v_isShared_57_ = v_isSharedCheck_65_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_00_u03c1_54_);
lean_inc(v_moduleR_53_);
lean_inc(v_addCommGroup_52_);
lean_dec(v_M_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_65_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___x_63_; 
v___x_58_ = lp_mathlib_AddSubgroupClass_toAddGroup___redArg(v_addCommGroup_52_);
v___f_59_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_smul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_59_, 0, v_moduleR_53_);
v___x_60_ = lean_box(0);
v___f_61_ = lean_alloc_closure((void*)(lp_mathlib_Representation_subrepresentation___redArg___lam__0), 3, 1);
lean_closure_set(v___f_61_, 0, v_00_u03c1_54_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 3, v___f_61_);
lean_ctor_set(v___x_56_, 2, v___x_60_);
lean_ctor_set(v___x_56_, 1, v___f_59_);
lean_ctor_set(v___x_56_, 0, v___x_58_);
v___x_63_ = v___x_56_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___f_59_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v___f_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteModule_torsion___boxed(lean_object* v_R_67_, lean_object* v_G_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_M_72_, lean_object* v_00_u2113_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_GRH_New_DiscreteModule_torsion(v_R_67_, v_G_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_M_72_, v_00_u2113_73_);
lean_dec(v_00_u2113_73_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_GRH_New_RelationSetting_allowedTorsion___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion(lean_object* v_K_79_, lean_object* v_R_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_M_84_, lean_object* v_m_85_, lean_object* v_inst_86_, lean_object* v_D_87_, lean_object* v_00_u2113_88_, lean_object* v_v_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RelationSetting_allowedTorsion___boxed(lean_object* v_K_91_, lean_object* v_R_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_M_96_, lean_object* v_m_97_, lean_object* v_inst_98_, lean_object* v_D_99_, lean_object* v_00_u2113_100_, lean_object* v_v_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_GRH_New_RelationSetting_allowedTorsion(v_K_91_, v_R_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_M_96_, v_m_97_, v_inst_98_, v_D_99_, v_00_u2113_100_, v_v_101_);
lean_dec(v_00_u2113_100_);
lean_dec_ref(v_D_99_);
lean_dec(v_m_97_);
lean_dec_ref(v_M_96_);
lean_dec_ref(v_inst_95_);
lean_dec_ref(v_inst_94_);
lean_dec_ref(v_inst_93_);
return v_res_102_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_Relations(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_ClassField_GreenbergWiles_RelationsModL(uint8_t builtin) {
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
res = initialize_GRH_Lib_ClassField_GreenbergWiles_Relations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
