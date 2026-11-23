// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataDIV public import Formalism.SharpRestriction.Divisibility.LatticeTransfer public import Formalism.SharpRestriction.Divisibility.PrinLevClass public import Formalism.SharpRestriction.ParamsHeightRankConstant
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_DegreeFormula_dimFl___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_dimY(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_dimY___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_dimY(lean_object* v_D_1_, lean_object* v_Y_2_){
_start:
{
lean_object* v_what_u2082_3_; lean_object* v_instTau_4_; lean_object* v_N_5_; lean_object* v___x_6_; 
v_what_u2082_3_ = lean_ctor_get(v_D_1_, 4);
v_instTau_4_ = lean_ctor_get(v_what_u2082_3_, 5);
v_N_5_ = lean_ctor_get(v_Y_2_, 0);
v___x_6_ = lp_tree_Formalism_DegreeFormula_dimFl___redArg(v_instTau_4_, v_N_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_dimY___boxed(lean_object* v_D_7_, lean_object* v_Y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_MainNotions_WeightThresholdDefs_dimY(v_D_7_, v_Y_8_);
lean_dec_ref(v_Y_8_);
lean_dec_ref(v_D_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___redArg(lean_object* v_Y_10_){
_start:
{
lean_object* v_N_11_; lean_object* v_j_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v_N_11_ = lean_ctor_get(v_Y_10_, 0);
v_j_12_ = lean_ctor_get(v_Y_10_, 1);
v___x_13_ = lean_nat_sub(v_N_11_, v_j_12_);
v___x_14_ = lean_nat_dec_le(v_j_12_, v___x_13_);
if (v___x_14_ == 0)
{
return v___x_13_;
}
else
{
lean_dec(v___x_13_);
lean_inc(v_j_12_);
return v_j_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___redArg___boxed(lean_object* v_Y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___redArg(v_Y_15_);
lean_dec_ref(v_Y_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS(lean_object* v_D_17_, lean_object* v_Y_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___redArg(v_Y_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS___boxed(lean_object* v_D_20_, lean_object* v_Y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_MainNotions_WeightThresholdDefs_jS(v_D_20_, v_Y_21_);
lean_dec_ref(v_Y_21_);
lean_dec_ref(v_D_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap___redArg(lean_object* v_Y_23_, lean_object* v_lam_24_, lean_object* v_00_u03c4_25_){
_start:
{
lean_object* v_j_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; 
v_j_26_ = lean_ctor_get(v_Y_23_, 1);
lean_inc(v_j_26_);
lean_dec_ref(v_Y_23_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_sub(v_j_26_, v___x_27_);
lean_inc(v_lam_24_);
lean_inc(v_00_u03c4_25_);
v___x_29_ = lean_apply_2(v_lam_24_, v_00_u03c4_25_, v___x_28_);
v___x_30_ = lean_apply_2(v_lam_24_, v_00_u03c4_25_, v_j_26_);
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_31_, 0, v___x_30_);
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_32_, 0, v___x_29_);
lean_closure_set(v___f_32_, 1, v___f_31_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap(lean_object* v_D_33_, lean_object* v_Y_34_, lean_object* v_lam_35_, lean_object* v_00_u03c4_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap___redArg(v_Y_34_, v_lam_35_, v_00_u03c4_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap___boxed(lean_object* v_D_38_, lean_object* v_Y_39_, lean_object* v_lam_40_, lean_object* v_00_u03c4_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_MainNotions_WeightThresholdDefs_gap(v_D_38_, v_Y_39_, v_lam_40_, v_00_u03c4_41_);
lean_dec_ref(v_D_38_);
return v_res_42_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LatticeTransfer(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_PrinLevClass(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightThresholdDefs(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LatticeTransfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_PrinLevClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
