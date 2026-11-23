// Lean compiler output
// Module: Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement public import Formalism.LocalToGlobal.GlobalTheory.DivPassage
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
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_V0C(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_V0C___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_goodPartComplexPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_goodPartComplexPoints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_V0C(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_Bs_5_, lean_object* v_A_6_, lean_object* v_X_7_, lean_object* v_cv_8_, uint8_t v_b_9_, lean_object* v_t_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_V0C___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_Bs_16_, lean_object* v_A_17_, lean_object* v_X_18_, lean_object* v_cv_19_, lean_object* v_b_20_, lean_object* v_t_21_){
_start:
{
uint8_t v_b_boxed_22_; lean_object* v_res_23_; 
v_b_boxed_22_ = lean_unbox(v_b_20_);
v_res_23_ = lp_tree_Formalism_IndefR_Cx_CxData_V0C(v_K_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_Bs_16_, v_A_17_, v_X_18_, v_cv_19_, v_b_boxed_22_, v_t_21_);
lean_dec(v_t_21_);
lean_dec_ref(v_cv_19_);
lean_dec_ref(v_X_18_);
lean_dec_ref(v_A_17_);
lean_dec_ref(v_Bs_16_);
lean_dec(v_inst_15_);
lean_dec_ref(v_inst_13_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_goodPartComplexPoints(lean_object* v_K_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_Bs_28_, lean_object* v_A_29_, lean_object* v_X_30_, lean_object* v_cv_31_, uint8_t v_b_32_, lean_object* v_j_33_, lean_object* v_t_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_IndefR_Cx_CxData_goodPartComplexPoints___boxed(lean_object* v_K_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_Bs_40_, lean_object* v_A_41_, lean_object* v_X_42_, lean_object* v_cv_43_, lean_object* v_b_44_, lean_object* v_j_45_, lean_object* v_t_46_){
_start:
{
uint8_t v_b_boxed_47_; lean_object* v_res_48_; 
v_b_boxed_47_ = lean_unbox(v_b_44_);
v_res_48_ = lp_tree_Formalism_IndefR_Cx_CxData_goodPartComplexPoints(v_K_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_Bs_40_, v_A_41_, v_X_42_, v_cv_43_, v_b_boxed_47_, v_j_45_, v_t_46_);
lean_dec(v_t_46_);
lean_dec(v_j_45_);
lean_dec_ref(v_cv_43_);
lean_dec_ref(v_X_42_);
lean_dec_ref(v_A_41_);
lean_dec_ref(v_Bs_40_);
lean_dec(v_inst_39_);
lean_dec_ref(v_inst_37_);
return v_res_48_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_PartsOrth(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_HeckeTupleStatement(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_DivPassage(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_CutTuples2(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_PartsOrth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteReal_HeckeTupleStatement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_DivPassage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
