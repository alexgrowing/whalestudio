// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
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
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_princ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_princ___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf___redArg(lean_object* v_F_1_, lean_object* v_M_2_, lean_object* v_un_3_){
_start:
{
lean_object* v_n_4_; lean_object* v_X_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_n_4_ = lean_ctor_get(v_F_1_, 0);
lean_inc(v_n_4_);
lean_dec_ref(v_F_1_);
v_X_5_ = lean_ctor_get(v_M_2_, 0);
v___x_6_ = l_List_finRange(v_n_4_);
lean_inc_ref(v_X_5_);
v___x_7_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v_X_5_);
lean_ctor_set(v___x_7_, 2, v_un_3_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf___redArg___boxed(lean_object* v_F_8_, lean_object* v_M_9_, lean_object* v_un_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_tree_GlobalTheory_FrameUnif_unfOf___redArg(v_F_8_, v_M_9_, v_un_10_);
lean_dec_ref(v_M_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf(lean_object* v_E_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_H_16_, lean_object* v_Dw_17_, lean_object* v_l_18_, lean_object* v_Xo_19_, lean_object* v_c_20_, lean_object* v_00_u03c3_21_, lean_object* v_r_22_, lean_object* v_g_23_, lean_object* v_e_24_, lean_object* v_F_25_, lean_object* v_M_26_, lean_object* v_un_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_GlobalTheory_FrameUnif_unfOf___redArg(v_F_25_, v_M_26_, v_un_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_unfOf___boxed(lean_object* v_E_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_H_33_, lean_object* v_Dw_34_, lean_object* v_l_35_, lean_object* v_Xo_36_, lean_object* v_c_37_, lean_object* v_00_u03c3_38_, lean_object* v_r_39_, lean_object* v_g_40_, lean_object* v_e_41_, lean_object* v_F_42_, lean_object* v_M_43_, lean_object* v_un_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_GlobalTheory_FrameUnif_unfOf(v_E_29_, v_inst_30_, v_inst_31_, v_inst_32_, v_H_33_, v_Dw_34_, v_l_35_, v_Xo_36_, v_c_37_, v_00_u03c3_38_, v_r_39_, v_g_40_, v_e_41_, v_F_42_, v_M_43_, v_un_44_);
lean_dec_ref(v_M_43_);
lean_dec_ref(v_e_41_);
lean_dec(v_g_40_);
lean_dec(v_r_39_);
lean_dec_ref(v_00_u03c3_38_);
lean_dec_ref(v_Xo_36_);
lean_dec_ref(v_l_35_);
lean_dec_ref(v_Dw_34_);
lean_dec_ref(v_H_33_);
lean_dec_ref(v_inst_30_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_princ(lean_object* v_E_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_H_50_, lean_object* v_r_51_, lean_object* v_l_52_, lean_object* v_Gm_53_, lean_object* v_Di_54_, lean_object* v_00_u03c60_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_FrameUnif_princ___boxed(lean_object* v_E_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_H_61_, lean_object* v_r_62_, lean_object* v_l_63_, lean_object* v_Gm_64_, lean_object* v_Di_65_, lean_object* v_00_u03c60_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_GlobalTheory_FrameUnif_princ(v_E_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_H_61_, v_r_62_, v_l_63_, v_Gm_64_, v_Di_65_, v_00_u03c60_66_);
lean_dec(v_00_u03c60_66_);
lean_dec_ref(v_Di_65_);
lean_dec(v_Gm_64_);
lean_dec_ref(v_l_63_);
lean_dec(v_r_62_);
lean_dec_ref(v_H_61_);
lean_dec_ref(v_inst_58_);
return v_res_67_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnFree(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnFree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
