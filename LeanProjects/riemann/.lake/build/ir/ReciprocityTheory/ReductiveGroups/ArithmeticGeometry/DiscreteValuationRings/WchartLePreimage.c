// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
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
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf___redArg(lean_object* v_D_1_, lean_object* v_Q_2_, lean_object* v_00_u03c7_3_, lean_object* v_00_u03c7_x27_4_){
_start:
{
lean_object* v_addX_5_; lean_object* v_toAddMonoid_6_; lean_object* v_toAddSemigroup_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_addX_5_ = lean_ctor_get(v_D_1_, 4);
lean_inc_ref(v_addX_5_);
lean_dec_ref(v_D_1_);
v_toAddMonoid_6_ = lean_ctor_get(v_addX_5_, 0);
lean_inc_ref(v_toAddMonoid_6_);
lean_dec_ref(v_addX_5_);
v_toAddSemigroup_7_ = lean_ctor_get(v_toAddMonoid_6_, 0);
lean_inc(v_toAddSemigroup_7_);
lean_dec_ref(v_toAddMonoid_6_);
lean_inc(v_00_u03c7_x27_4_);
lean_inc(v_00_u03c7_3_);
v___x_8_ = lean_apply_2(v_toAddSemigroup_7_, v_00_u03c7_3_, v_00_u03c7_x27_4_);
lean_inc_ref_n(v_Q_2_, 2);
v___x_9_ = lean_apply_1(v_Q_2_, v___x_8_);
v___x_10_ = lean_apply_1(v_Q_2_, v_00_u03c7_3_);
v___x_11_ = lean_int_sub(v___x_9_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_apply_1(v_Q_2_, v_00_u03c7_x27_4_);
v___x_13_ = lean_int_sub(v___x_11_, v___x_12_);
lean_dec(v___x_12_);
lean_dec(v___x_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf(lean_object* v_V_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_D_17_, lean_object* v_Q_18_, lean_object* v_00_u03c7_19_, lean_object* v_00_u03c7_x27_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf___redArg(v_D_17_, v_Q_18_, v_00_u03c7_19_, v_00_u03c7_x27_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf___boxed(lean_object* v_V_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_D_25_, lean_object* v_Q_26_, lean_object* v_00_u03c7_27_, lean_object* v_00_u03c7_x27_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_ReciprocityTheory_ChartRestriction_G_DVR_QForm_bOf(v_V_22_, v_inst_23_, v_inst_24_, v_D_25_, v_Q_26_, v_00_u03c7_27_, v_00_u03c7_x27_28_);
lean_dec_ref(v_inst_23_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
