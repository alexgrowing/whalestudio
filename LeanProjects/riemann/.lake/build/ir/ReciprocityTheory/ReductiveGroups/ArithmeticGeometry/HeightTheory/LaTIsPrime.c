// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___redArg(lean_object* v_d_1_){
_start:
{
lean_object* v_D_2_; lean_object* v_T_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_D_2_ = lean_ctor_get(v_d_1_, 0);
v_T_3_ = lean_ctor_get(v_d_1_, 2);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_T_3_, v___x_4_);
v___x_6_ = lp_mathlib_Nat_fast__choose(v___x_5_, v_D_2_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___redArg___boxed(lean_object* v_d_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___redArg(v_d_7_);
lean_dec_ref(v_d_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb(lean_object* v_K_9_, lean_object* v_inst_10_, lean_object* v_00_u03b9_11_, lean_object* v_00_u03a9_12_, lean_object* v_inst_13_, lean_object* v_WT_14_, lean_object* v_A_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_d_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___redArg(v_d_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb___boxed(lean_object* v_K_20_, lean_object* v_inst_21_, lean_object* v_00_u03b9_22_, lean_object* v_00_u03a9_23_, lean_object* v_inst_24_, lean_object* v_WT_25_, lean_object* v_A_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_d_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_tree_ReciprocityTheory_ChartRestriction_G_T0_Data_Rb(v_K_20_, v_inst_21_, v_00_u03b9_22_, v_00_u03a9_23_, v_inst_24_, v_WT_25_, v_A_26_, v_inst_27_, v_inst_28_, v_d_29_);
lean_dec_ref(v_d_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_21_);
return v_res_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
