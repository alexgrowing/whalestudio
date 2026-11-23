// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
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
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_resTop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_resTop(lean_object* v_Y_1_, lean_object* v_W_2_, lean_object* v_c_3_){
_start:
{
lean_object* v_presheaf_4_; lean_object* v_map_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_presheaf_4_ = lean_ctor_get(v_Y_1_, 1);
lean_inc_ref(v_presheaf_4_);
lean_dec_ref(v_Y_1_);
v_map_5_ = lean_ctor_get(v_presheaf_4_, 1);
lean_inc(v_map_5_);
lean_dec_ref(v_presheaf_4_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_4(v_map_5_, v___x_6_, v_W_2_, lean_box(0), v_c_3_);
return v___x_7_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
