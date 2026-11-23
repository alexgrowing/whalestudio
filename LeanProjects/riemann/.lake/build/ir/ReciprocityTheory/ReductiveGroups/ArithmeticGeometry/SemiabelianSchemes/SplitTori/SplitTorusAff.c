// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
// Imports: public import Init public meta import Init public import Mathlib.AlgebraicGeometry.Group.Abelian public import Mathlib.AlgebraicGeometry.Group.Affine public import Mathlib.AlgebraicGeometry.AffineSpace public import Mathlib.AlgebraicGeometry.Morphisms.Smooth public import Mathlib.AlgebraicGeometry.Morphisms.Separated public import Mathlib.AlgebraicGeometry.Morphisms.Flat public import Mathlib.AlgebraicGeometry.Geometrically.Connected public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
extern lean_object* lp_mathlib_Int_instCommRing;
lean_object* lp_mathlib_ULift_ring___redArg(lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU___closed__0;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU;
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Int_instCommRing;
v___x_2_ = lp_mathlib_ULift_ring___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU___closed__0);
return v___x_3_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_Group_Abelian(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_Group_Affine(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_AffineSpace(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_Morphisms_Smooth(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_Morphisms_Separated(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_Morphisms_Flat(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_AlgebraicGeometry_Geometrically_Connected(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_HopfAlgebra_MonoidAlgebra(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Monoidal_Cartesian_Grp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_Group_Abelian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_Group_Affine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_AffineSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_Morphisms_Smooth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_Morphisms_Separated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_Morphisms_Flat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_AlgebraicGeometry_Geometrically_Connected(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_HopfAlgebra_MonoidAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Monoidal_Cartesian_Grp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU = _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU();
lean_mark_persistent(lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_ZU);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
