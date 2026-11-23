// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
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
lean_object* lp_mathlib_AlgebraicGeometry_PresheafedSpace_comp___at___00AlgebraicGeometry_LocallyRingedSpace_comp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_CategoryTheory_CostructuredArrow_mk___at___00CategoryTheory_Over_mk___at___00ReciprocityTheory_ChartRestriction_G_Out_overRes_u03b9_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* lp_tree_CategoryTheory_CostructuredArrow_homMk___at___00CategoryTheory_Over_homMk___at___00ReciprocityTheory_ChartRestriction_G_Out_overRes_u03b9_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_toBase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_toBase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_toBase___redArg(lean_object* v_S_1_, lean_object* v_S_x27_2_, lean_object* v_f_3_, lean_object* v_A_4_, lean_object* v_A_x27_5_, lean_object* v_g_6_, lean_object* v_T_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_left_9_; lean_object* v_hom_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_left_13_; lean_object* v_left_14_; lean_object* v_left_15_; lean_object* v_left_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_left_9_ = lean_ctor_get(v_T_7_, 0);
lean_inc_n(v_left_9_, 2);
v_hom_10_ = lean_ctor_get(v_T_7_, 2);
lean_inc(v_hom_10_);
lean_dec_ref(v_T_7_);
v___x_11_ = lp_mathlib_AlgebraicGeometry_PresheafedSpace_comp___at___00AlgebraicGeometry_LocallyRingedSpace_comp_spec__0(v_left_9_, v_S_x27_2_, v_S_1_, v_hom_10_, v_f_3_);
v___x_12_ = lp_tree_CategoryTheory_CostructuredArrow_mk___at___00CategoryTheory_Over_mk___at___00ReciprocityTheory_ChartRestriction_G_Out_overRes_u03b9_spec__0_spec__1___redArg(v_left_9_, v___x_11_);
v_left_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_left_13_);
lean_dec_ref(v___x_12_);
v_left_14_ = lean_ctor_get(v_A_x27_5_, 0);
lean_inc(v_left_14_);
lean_dec_ref(v_A_x27_5_);
v_left_15_ = lean_ctor_get(v_A_4_, 0);
lean_inc(v_left_15_);
lean_dec_ref(v_A_4_);
v_left_16_ = lean_ctor_get(v_x_8_, 0);
lean_inc(v_left_16_);
lean_dec_ref(v_x_8_);
v___x_17_ = lp_mathlib_AlgebraicGeometry_PresheafedSpace_comp___at___00AlgebraicGeometry_LocallyRingedSpace_comp_spec__0(v_left_13_, v_left_14_, v_left_15_, v_left_16_, v_g_6_);
v___x_18_ = lp_tree_CategoryTheory_CostructuredArrow_homMk___at___00CategoryTheory_Over_homMk___at___00ReciprocityTheory_ChartRestriction_G_Out_overRes_u03b9_spec__1_spec__3___redArg(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_toBase(lean_object* v_S_19_, lean_object* v_S_x27_20_, lean_object* v_f_21_, lean_object* v_A_22_, lean_object* v_A_x27_23_, lean_object* v_g_24_, lean_object* v_hw_25_, lean_object* v_T_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_toBase___redArg(v_S_19_, v_S_x27_20_, v_f_21_, v_A_22_, v_A_x27_23_, v_g_24_, v_T_26_, v_x_27_);
return v___x_28_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_Imports(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
