// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataKernels
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.Params public import Formalism.ThetaLiftIndependence.Statement
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
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_mulFun___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_mulFun___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_mulFun(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_mulFun___redArg___lam__0(lean_object* v_g_1_, lean_object* v_00_u03c6_2_, lean_object* v_y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_re_5_; lean_object* v_im_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc(v_y_3_);
v___x_4_ = lean_apply_1(v_g_1_, v_y_3_);
v_re_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_re_5_);
v_im_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_im_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lean_apply_1(v_00_u03c6_2_, v_y_3_);
v___x_8_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_5_, v_im_6_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_mulFun___redArg(lean_object* v_g_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_mulFun___redArg___lam__0), 3, 1);
lean_closure_set(v___f_10_, 0, v_g_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_mulFun(lean_object* v_Y_11_, lean_object* v_g_12_){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_mulFun___redArg___lam__0), 3, 1);
lean_closure_set(v___f_13_, 0, v_g_12_);
return v___f_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist___redArg(lean_object* v_C_14_, lean_object* v_T_15_){
_start:
{
lean_object* v_clsFin_16_; lean_object* v_stabGrp_17_; lean_object* v_DGam_18_; lean_object* v_de_19_; lean_object* v_sSharp_20_; lean_object* v_sDiv_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_31_; 
v_clsFin_16_ = lean_ctor_get(v_C_14_, 0);
v_stabGrp_17_ = lean_ctor_get(v_C_14_, 1);
v_DGam_18_ = lean_ctor_get(v_C_14_, 2);
v_de_19_ = lean_ctor_get(v_C_14_, 3);
v_sSharp_20_ = lean_ctor_get(v_C_14_, 7);
v_sDiv_21_ = lean_ctor_get(v_C_14_, 8);
v_isSharedCheck_31_ = !lean_is_exclusive(v_C_14_);
if (v_isSharedCheck_31_ == 0)
{
lean_object* v_unused_32_; lean_object* v_unused_33_; lean_object* v_unused_34_; 
v_unused_32_ = lean_ctor_get(v_C_14_, 6);
lean_dec(v_unused_32_);
v_unused_33_ = lean_ctor_get(v_C_14_, 5);
lean_dec(v_unused_33_);
v_unused_34_ = lean_ctor_get(v_C_14_, 4);
lean_dec(v_unused_34_);
v___x_23_ = v_C_14_;
v_isShared_24_ = v_isSharedCheck_31_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_sDiv_21_);
lean_inc(v_sSharp_20_);
lean_inc(v_de_19_);
lean_inc(v_DGam_18_);
lean_inc(v_stabGrp_17_);
lean_inc(v_clsFin_16_);
lean_dec(v_C_14_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_31_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_rhoDet_25_; lean_object* v_rhoDet_x27_26_; lean_object* v_unf_27_; lean_object* v___x_29_; 
v_rhoDet_25_ = lean_ctor_get(v_T_15_, 0);
v_rhoDet_x27_26_ = lean_ctor_get(v_T_15_, 1);
v_unf_27_ = lean_ctor_get(v_T_15_, 2);
lean_inc_ref(v_unf_27_);
lean_inc_ref(v_rhoDet_x27_26_);
lean_inc_ref(v_rhoDet_25_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 6, v_unf_27_);
lean_ctor_set(v___x_23_, 5, v_rhoDet_x27_26_);
lean_ctor_set(v___x_23_, 4, v_rhoDet_25_);
v___x_29_ = v___x_23_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_clsFin_16_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_stabGrp_17_);
lean_ctor_set(v_reuseFailAlloc_30_, 2, v_DGam_18_);
lean_ctor_set(v_reuseFailAlloc_30_, 3, v_de_19_);
lean_ctor_set(v_reuseFailAlloc_30_, 4, v_rhoDet_25_);
lean_ctor_set(v_reuseFailAlloc_30_, 5, v_rhoDet_x27_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 6, v_unf_27_);
lean_ctor_set(v_reuseFailAlloc_30_, 7, v_sSharp_20_);
lean_ctor_set(v_reuseFailAlloc_30_, 8, v_sDiv_21_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist___redArg___boxed(lean_object* v_C_35_, lean_object* v_T_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_BasicNotions_ColumnChain_twist___redArg(v_C_35_, v_T_36_);
lean_dec_ref(v_T_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist(lean_object* v_R_38_, lean_object* v_00_u03b9_39_, lean_object* v_inst_40_, lean_object* v_hc_41_, lean_object* v_C_42_, lean_object* v_T_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_Formalism_BasicNotions_ColumnChain_twist___redArg(v_C_42_, v_T_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_twist___boxed(lean_object* v_R_45_, lean_object* v_00_u03b9_46_, lean_object* v_inst_47_, lean_object* v_hc_48_, lean_object* v_C_49_, lean_object* v_T_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_Formalism_BasicNotions_ColumnChain_twist(v_R_45_, v_00_u03b9_46_, v_inst_47_, v_hc_48_, v_C_49_, v_T_50_);
lean_dec_ref(v_T_50_);
lean_dec_ref(v_hc_48_);
lean_dec(v_inst_47_);
lean_dec_ref(v_R_45_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData___redArg(lean_object* v_C_52_){
_start:
{
lean_object* v_rhoDet_53_; lean_object* v_rhoDet_x27_54_; lean_object* v_unf_55_; lean_object* v___x_56_; 
v_rhoDet_53_ = lean_ctor_get(v_C_52_, 4);
v_rhoDet_x27_54_ = lean_ctor_get(v_C_52_, 5);
v_unf_55_ = lean_ctor_get(v_C_52_, 6);
lean_inc_ref(v_unf_55_);
lean_inc_ref(v_rhoDet_x27_54_);
lean_inc_ref(v_rhoDet_53_);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v_rhoDet_53_);
lean_ctor_set(v___x_56_, 1, v_rhoDet_x27_54_);
lean_ctor_set(v___x_56_, 2, v_unf_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData___redArg___boxed(lean_object* v_C_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_BasicNotions_ColumnChain_ownData___redArg(v_C_57_);
lean_dec_ref(v_C_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData(lean_object* v_R_59_, lean_object* v_00_u03b9_60_, lean_object* v_inst_61_, lean_object* v_hc_62_, lean_object* v_C_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_tree_Formalism_BasicNotions_ColumnChain_ownData___redArg(v_C_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_ColumnChain_ownData___boxed(lean_object* v_R_65_, lean_object* v_00_u03b9_66_, lean_object* v_inst_67_, lean_object* v_hc_68_, lean_object* v_C_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_BasicNotions_ColumnChain_ownData(v_R_65_, v_00_u03b9_66_, v_inst_67_, v_hc_68_, v_C_69_);
lean_dec_ref(v_C_69_);
lean_dec_ref(v_hc_68_);
lean_dec(v_inst_67_);
lean_dec_ref(v_R_65_);
return v_res_70_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Params(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKernels(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_Params(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
