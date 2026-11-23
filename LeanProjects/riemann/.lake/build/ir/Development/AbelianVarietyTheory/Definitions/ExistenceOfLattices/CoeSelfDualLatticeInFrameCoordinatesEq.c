// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1 public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_th___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_th(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_th___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_unf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_unf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_unf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_th___redArg(lean_object* v_C_1_, lean_object* v_00_u03c4_2_){
_start:
{
lean_object* v_00_u03b8_3_; lean_object* v___x_4_; 
v_00_u03b8_3_ = lean_ctor_get(v_C_1_, 5);
lean_inc_ref(v_00_u03b8_3_);
lean_dec_ref(v_C_1_);
v___x_4_ = lean_apply_1(v_00_u03b8_3_, v_00_u03c4_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_th(lean_object* v_D_5_, lean_object* v_H_6_, lean_object* v_Dw_7_, lean_object* v_l_8_, lean_object* v_Xo_9_, lean_object* v_c_10_, lean_object* v_00_u03c3_11_, lean_object* v_V_12_, lean_object* v_r_13_, lean_object* v_C_14_, lean_object* v_x_15_, lean_object* v_00_u03c4_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_GlobalTheory_Member_Ctx_th___redArg(v_C_14_, v_00_u03c4_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_th___boxed(lean_object* v_D_18_, lean_object* v_H_19_, lean_object* v_Dw_20_, lean_object* v_l_21_, lean_object* v_Xo_22_, lean_object* v_c_23_, lean_object* v_00_u03c3_24_, lean_object* v_V_25_, lean_object* v_r_26_, lean_object* v_C_27_, lean_object* v_x_28_, lean_object* v_00_u03c4_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_GlobalTheory_Member_Ctx_th(v_D_18_, v_H_19_, v_Dw_20_, v_l_21_, v_Xo_22_, v_c_23_, v_00_u03c3_24_, v_V_25_, v_r_26_, v_C_27_, v_x_28_, v_00_u03c4_29_);
lean_dec(v_x_28_);
lean_dec(v_r_26_);
lean_dec_ref(v_V_25_);
lean_dec_ref(v_00_u03c3_24_);
lean_dec_ref(v_Xo_22_);
lean_dec_ref(v_l_21_);
lean_dec_ref(v_Dw_20_);
lean_dec_ref(v_H_19_);
lean_dec_ref(v_D_18_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_unf___redArg(lean_object* v_C_31_, lean_object* v_un_32_){
_start:
{
lean_object* v_F_33_; lean_object* v_M_34_; lean_object* v_n_35_; lean_object* v_X_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_F_33_ = lean_ctor_get(v_C_31_, 2);
lean_inc_ref(v_F_33_);
v_M_34_ = lean_ctor_get(v_C_31_, 3);
lean_inc_ref(v_M_34_);
lean_dec_ref(v_C_31_);
v_n_35_ = lean_ctor_get(v_F_33_, 0);
lean_inc(v_n_35_);
lean_dec_ref(v_F_33_);
v_X_36_ = lean_ctor_get(v_M_34_, 0);
lean_inc_ref(v_X_36_);
lean_dec_ref(v_M_34_);
v___x_37_ = l_List_finRange(v_n_35_);
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v_X_36_);
lean_ctor_set(v___x_38_, 2, v_un_32_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_unf(lean_object* v_D_39_, lean_object* v_H_40_, lean_object* v_Dw_41_, lean_object* v_l_42_, lean_object* v_Xo_43_, lean_object* v_c_44_, lean_object* v_00_u03c3_45_, lean_object* v_V_46_, lean_object* v_r_47_, lean_object* v_C_48_, lean_object* v_un_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_tree_GlobalTheory_Member_Ctx_unf___redArg(v_C_48_, v_un_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_Member_Ctx_unf___boxed(lean_object* v_D_51_, lean_object* v_H_52_, lean_object* v_Dw_53_, lean_object* v_l_54_, lean_object* v_Xo_55_, lean_object* v_c_56_, lean_object* v_00_u03c3_57_, lean_object* v_V_58_, lean_object* v_r_59_, lean_object* v_C_60_, lean_object* v_un_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_GlobalTheory_Member_Ctx_unf(v_D_51_, v_H_52_, v_Dw_53_, v_l_54_, v_Xo_55_, v_c_56_, v_00_u03c3_57_, v_V_58_, v_r_59_, v_C_60_, v_un_61_);
lean_dec(v_r_59_);
lean_dec_ref(v_V_58_);
lean_dec_ref(v_00_u03c3_57_);
lean_dec_ref(v_Xo_55_);
lean_dec_ref(v_l_54_);
lean_dec_ref(v_Dw_53_);
lean_dec_ref(v_H_52_);
lean_dec_ref(v_D_51_);
return v_res_62_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FreeBridge(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_MarkSpec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_CoeSelfDualLatticeInFrameCoordinatesEq(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FreeBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_MarkSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
