// Lean compiler output
// Module: Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataKerI public import Formalism.LocalRingCardinality.DataParamsT public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension public import Formalism.LocalToGlobal.Columns.LocWLemmas
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
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_latOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_latOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_latOf(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_V_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_00_u03b9_6_, lean_object* v_b_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_latOf___boxed(lean_object* v_K_9_, lean_object* v_inst_10_, lean_object* v_V_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_00_u03b9_14_, lean_object* v_b_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_latOf(v_K_9_, v_inst_10_, v_V_11_, v_inst_12_, v_inst_13_, v_00_u03b9_14_, v_b_15_);
lean_dec(v_b_15_);
lean_dec(v_inst_13_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_10_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg___lam__0(lean_object* v_M_17_, lean_object* v_i_18_, lean_object* v_b_19_, lean_object* v_inst_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc(v_k_21_);
v___x_22_ = lean_apply_2(v_M_17_, v_k_21_, v_i_18_);
v___x_23_ = lean_apply_1(v_b_19_, v_k_21_);
v___x_24_ = lean_apply_2(v_inst_20_, v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_b_28_, lean_object* v_M_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_toAddMonoid_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v_toAddMonoid_31_ = lean_ctor_get(v_inst_25_, 0);
v___f_32_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg___lam__0), 5, 4);
lean_closure_set(v___f_32_, 0, v_M_29_);
lean_closure_set(v___f_32_, 1, v_i_30_);
lean_closure_set(v___f_32_, 2, v_b_28_);
lean_closure_set(v___f_32_, 3, v_inst_26_);
v___x_33_ = lp_mathlib_Finset_sum___redArg(v_toAddMonoid_31_, v_inst_27_, v___f_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg___boxed(lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_b_37_, lean_object* v_M_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg(v_inst_34_, v_inst_35_, v_inst_36_, v_b_37_, v_M_38_, v_i_39_);
lean_dec_ref(v_inst_34_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf(lean_object* v_K_41_, lean_object* v_inst_42_, lean_object* v_V_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_00_u03b9_46_, lean_object* v_inst_47_, lean_object* v_b_48_, lean_object* v_M_49_, lean_object* v_i_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___redArg(v_inst_44_, v_inst_45_, v_inst_47_, v_b_48_, v_M_49_, v_i_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf___boxed(lean_object* v_K_52_, lean_object* v_inst_53_, lean_object* v_V_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_00_u03b9_57_, lean_object* v_inst_58_, lean_object* v_b_59_, lean_object* v_M_60_, lean_object* v_i_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_Formalism_BasicNotions_SkeletonIndexLemmas_famOf(v_K_52_, v_inst_53_, v_V_54_, v_inst_55_, v_inst_56_, v_00_u03b9_57_, v_inst_58_, v_b_59_, v_M_60_, v_i_61_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_53_);
return v_res_62_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKerI(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParamsT(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_LocWLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_CoeNeZeroOfNotMem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKerI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParamsT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_LocWLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
