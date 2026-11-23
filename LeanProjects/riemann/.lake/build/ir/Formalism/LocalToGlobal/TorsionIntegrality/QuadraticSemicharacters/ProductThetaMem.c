// Lean compiler output
// Module: Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_H_qOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_H_qOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_H_qOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_H_qOf___redArg(lean_object* v_c_1_, lean_object* v_H_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_re_5_; lean_object* v___f_6_; 
lean_inc(v_x_3_);
v___x_4_ = lean_apply_2(v_H_2_, v_x_3_, v_x_3_);
v_re_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_re_5_);
lean_dec_ref(v___x_4_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_6_, 0, v_c_1_);
lean_closure_set(v___f_6_, 1, v_re_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_H_qOf(lean_object* v_V_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_c_10_, lean_object* v_H_11_, lean_object* v_x_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_tree_Formalism_L2_Th1_H_qOf___redArg(v_c_10_, v_H_11_, v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Th1_H_qOf___boxed(lean_object* v_V_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_c_17_, lean_object* v_H_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_Th1_H_qOf(v_V_14_, v_inst_15_, v_inst_16_, v_c_17_, v_H_18_, v_x_19_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
