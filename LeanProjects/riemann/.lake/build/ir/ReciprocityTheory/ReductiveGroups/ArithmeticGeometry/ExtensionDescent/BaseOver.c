// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_AlgebraicGeometry_PresheafedSpace_id___at___00AlgebraicGeometry_LocallyRingedSpace_id_spec__0(lean_object*);
lean_object* lp_mathlib_CategoryTheory_CostructuredArrow_mk___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__0;
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1;
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__2;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_baseOver(lean_object*);
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1, &lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1);
v___x_6_ = lean_int_neg(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp(lean_object* v_g_7_, lean_object* v_i_8_, lean_object* v_j_9_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_nat_dec_lt(v_i_8_, v_g_7_);
if (v___x_17_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = lean_nat_add(v_i_8_, v_g_7_);
v___x_19_ = lean_nat_dec_eq(v_j_9_, v___x_18_);
lean_dec(v___x_18_);
if (v___x_19_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1, &lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__1);
return v___x_20_;
}
}
v___jp_10_:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__0);
return v___x_11_;
}
v___jp_12_:
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_lt(v_j_9_, v_g_7_);
if (v___x_13_ == 0)
{
goto v___jp_10_;
}
else
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_nat_add(v_j_9_, v_g_7_);
v___x_15_ = lean_nat_dec_eq(v_i_8_, v___x_14_);
lean_dec(v___x_14_);
if (v___x_15_ == 0)
{
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__2, &lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__2_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___closed__2);
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp___boxed(lean_object* v_g_21_, lean_object* v_i_22_, lean_object* v_j_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_stdSymp(v_g_21_, v_i_22_, v_j_23_);
lean_dec(v_j_23_);
lean_dec(v_i_22_);
lean_dec(v_g_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_baseOver(lean_object* v_S_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lp_mathlib_AlgebraicGeometry_PresheafedSpace_id___at___00AlgebraicGeometry_LocallyRingedSpace_id_spec__0(v_S_25_);
v___x_27_ = lp_mathlib_CategoryTheory_CostructuredArrow_mk___redArg(v_S_25_, v___x_26_);
return v___x_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
