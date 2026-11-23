// Lean compiler output
// Module: Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
// Imports: public import Init public meta import Init public import Mathlib public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
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
lean_object* lp_mathlib_MulDistribMulAction_toMonoidHom___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Reformulated_AutPerF_Tilt_map___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf___redArg___lam__0(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_f_1_, v_g_2_, v_x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf___redArg(lean_object* v_f_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_actionOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6_, 0, v_f_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf(lean_object* v_G_7_, lean_object* v_B_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_f_11_, lean_object* v_h1_12_, lean_object* v_hmul_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_actionOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_14_, 0, v_f_11_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_actionOf___boxed(lean_object* v_G_15_, lean_object* v_B_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_f_19_, lean_object* v_h1_20_, lean_object* v_hmul_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Reformulated_AutPerF_actionOf(v_G_15_, v_B_16_, v_inst_17_, v_inst_18_, v_f_19_, v_h1_20_, v_hmul_21_);
lean_dec_ref(v_inst_18_);
lean_dec_ref(v_inst_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___redArg___lam__0(lean_object* v_inst_23_, lean_object* v_g_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_31__overap_28_; lean_object* v___x_29_; 
v___f_27_ = lean_alloc_closure((void*)(lp_mathlib_MulDistribMulAction_toMonoidHom___redArg___lam__0), 3, 2);
lean_closure_set(v___f_27_, 0, v_inst_23_);
lean_closure_set(v___f_27_, 1, v_g_24_);
v___x_31__overap_28_ = lp_tree_Reformulated_AutPerF_Tilt_map___redArg(v___f_27_);
v___x_29_ = lean_apply_2(v___x_31__overap_28_, v___y_25_, v___y_26_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___redArg(lean_object* v_inst_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___f_32_; 
v___f_31_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___redArg___lam__0), 4, 1);
lean_closure_set(v___f_31_, 0, v_inst_30_);
v___f_32_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_actionOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_32_, 0, v___f_31_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction(lean_object* v_p_33_, lean_object* v_inst_34_, lean_object* v_R_35_, lean_object* v_inst_36_, lean_object* v_G_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___redArg(v_inst_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction___boxed(lean_object* v_p_42_, lean_object* v_inst_43_, lean_object* v_R_44_, lean_object* v_inst_45_, lean_object* v_G_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_tree_Reformulated_AutPerF_Tilt_mulSemiringAction(v_p_42_, v_inst_43_, v_R_44_, v_inst_45_, v_G_46_, v_inst_47_, v_inst_48_, v_inst_49_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_45_);
lean_dec(v_p_42_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul___redArg___lam__0(lean_object* v_inst_51_, lean_object* v_g_52_, lean_object* v_00_u03d6_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_30__overap_56_; lean_object* v___x_57_; 
v___f_55_ = lean_alloc_closure((void*)(lp_mathlib_MulDistribMulAction_toMonoidHom___redArg___lam__0), 3, 2);
lean_closure_set(v___f_55_, 0, v_inst_51_);
lean_closure_set(v___f_55_, 1, v_g_52_);
v___x_30__overap_56_ = lp_tree_Reformulated_AutPerF_Tilt_map___redArg(v___f_55_);
v___x_57_ = lean_apply_2(v___x_30__overap_56_, v_00_u03d6_53_, v___y_54_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul___redArg(lean_object* v_inst_58_){
_start:
{
lean_object* v___f_59_; 
v___f_59_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_PFlat_smul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_59_, 0, v_inst_58_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul(lean_object* v_p_60_, lean_object* v_inst_61_, lean_object* v_R_62_, lean_object* v_inst_63_, lean_object* v_G_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v___f_69_; 
v___f_69_ = lean_alloc_closure((void*)(lp_tree_Reformulated_AutPerF_PFlat_smul___redArg___lam__0), 4, 1);
lean_closure_set(v___f_69_, 0, v_inst_66_);
return v___f_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Reformulated_AutPerF_PFlat_smul___boxed(lean_object* v_p_70_, lean_object* v_inst_71_, lean_object* v_R_72_, lean_object* v_inst_73_, lean_object* v_G_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Reformulated_AutPerF_PFlat_smul(v_p_70_, v_inst_71_, v_R_72_, v_inst_73_, v_G_74_, v_inst_75_, v_inst_76_, v_inst_77_, v_inst_78_);
lean_dec_ref(v_inst_75_);
lean_dec_ref(v_inst_73_);
lean_dec(v_p_70_);
return v_res_79_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Action(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
