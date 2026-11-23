// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
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
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_base___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_base(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_base___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup___redArg(lean_object* v_B_1_){
_start:
{
lean_object* v_supN_2_; 
v_supN_2_ = lean_ctor_get(v_B_1_, 6);
lean_inc(v_supN_2_);
return v_supN_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup___redArg___boxed(lean_object* v_B_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_tree_GlobalTheory_RunIn_SecNorm_sup___redArg(v_B_3_);
lean_dec_ref(v_B_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup(lean_object* v_D_5_, lean_object* v_B_6_){
_start:
{
lean_object* v_supN_7_; 
v_supN_7_ = lean_ctor_get(v_B_6_, 6);
lean_inc(v_supN_7_);
return v_supN_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_sup___boxed(lean_object* v_D_8_, lean_object* v_B_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_GlobalTheory_RunIn_SecNorm_sup(v_D_8_, v_B_9_);
lean_dec_ref(v_B_9_);
lean_dec_ref(v_D_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_base___redArg(lean_object* v_B_11_, lean_object* v_n_12_){
_start:
{
lean_object* v_fKO_13_; lean_object* v_eO_14_; lean_object* v_acgC_15_; lean_object* v_modC_16_; lean_object* v_modOC_17_; lean_object* v_Mlat_18_; lean_object* v_supN_19_; lean_object* v_Xc_20_; lean_object* v_acgF_21_; lean_object* v_modF_22_; lean_object* v_sg_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_fKO_13_ = lean_ctor_get(v_B_11_, 0);
v_eO_14_ = lean_ctor_get(v_B_11_, 1);
v_acgC_15_ = lean_ctor_get(v_B_11_, 2);
v_modC_16_ = lean_ctor_get(v_B_11_, 3);
v_modOC_17_ = lean_ctor_get(v_B_11_, 4);
v_Mlat_18_ = lean_ctor_get(v_B_11_, 5);
v_supN_19_ = lean_ctor_get(v_B_11_, 6);
v_Xc_20_ = lean_ctor_get(v_B_11_, 8);
v_acgF_21_ = lean_ctor_get(v_B_11_, 9);
v_modF_22_ = lean_ctor_get(v_B_11_, 10);
v_sg_23_ = lean_ctor_get(v_B_11_, 11);
v_isSharedCheck_30_ = !lean_is_exclusive(v_B_11_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v_B_11_, 7);
lean_dec(v_unused_31_);
v___x_25_ = v_B_11_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_sg_23_);
lean_inc(v_modF_22_);
lean_inc(v_acgF_21_);
lean_inc(v_Xc_20_);
lean_inc(v_supN_19_);
lean_inc(v_Mlat_18_);
lean_inc(v_modOC_17_);
lean_inc(v_modC_16_);
lean_inc(v_acgC_15_);
lean_inc(v_eO_14_);
lean_inc(v_fKO_13_);
lean_dec(v_B_11_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 7, v_n_12_);
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_fKO_13_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_eO_14_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v_acgC_15_);
lean_ctor_set(v_reuseFailAlloc_29_, 3, v_modC_16_);
lean_ctor_set(v_reuseFailAlloc_29_, 4, v_modOC_17_);
lean_ctor_set(v_reuseFailAlloc_29_, 5, v_Mlat_18_);
lean_ctor_set(v_reuseFailAlloc_29_, 6, v_supN_19_);
lean_ctor_set(v_reuseFailAlloc_29_, 7, v_n_12_);
lean_ctor_set(v_reuseFailAlloc_29_, 8, v_Xc_20_);
lean_ctor_set(v_reuseFailAlloc_29_, 9, v_acgF_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 10, v_modF_22_);
lean_ctor_set(v_reuseFailAlloc_29_, 11, v_sg_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_base(lean_object* v_D_32_, lean_object* v_B_33_, lean_object* v_n_34_){
_start:
{
lean_object* v_fKO_35_; lean_object* v_eO_36_; lean_object* v_acgC_37_; lean_object* v_modC_38_; lean_object* v_modOC_39_; lean_object* v_Mlat_40_; lean_object* v_supN_41_; lean_object* v_Xc_42_; lean_object* v_acgF_43_; lean_object* v_modF_44_; lean_object* v_sg_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_fKO_35_ = lean_ctor_get(v_B_33_, 0);
v_eO_36_ = lean_ctor_get(v_B_33_, 1);
v_acgC_37_ = lean_ctor_get(v_B_33_, 2);
v_modC_38_ = lean_ctor_get(v_B_33_, 3);
v_modOC_39_ = lean_ctor_get(v_B_33_, 4);
v_Mlat_40_ = lean_ctor_get(v_B_33_, 5);
v_supN_41_ = lean_ctor_get(v_B_33_, 6);
v_Xc_42_ = lean_ctor_get(v_B_33_, 8);
v_acgF_43_ = lean_ctor_get(v_B_33_, 9);
v_modF_44_ = lean_ctor_get(v_B_33_, 10);
v_sg_45_ = lean_ctor_get(v_B_33_, 11);
v_isSharedCheck_52_ = !lean_is_exclusive(v_B_33_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v_B_33_, 7);
lean_dec(v_unused_53_);
v___x_47_ = v_B_33_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_sg_45_);
lean_inc(v_modF_44_);
lean_inc(v_acgF_43_);
lean_inc(v_Xc_42_);
lean_inc(v_supN_41_);
lean_inc(v_Mlat_40_);
lean_inc(v_modOC_39_);
lean_inc(v_modC_38_);
lean_inc(v_acgC_37_);
lean_inc(v_eO_36_);
lean_inc(v_fKO_35_);
lean_dec(v_B_33_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 7, v_n_34_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_fKO_35_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_eO_36_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_acgC_37_);
lean_ctor_set(v_reuseFailAlloc_51_, 3, v_modC_38_);
lean_ctor_set(v_reuseFailAlloc_51_, 4, v_modOC_39_);
lean_ctor_set(v_reuseFailAlloc_51_, 5, v_Mlat_40_);
lean_ctor_set(v_reuseFailAlloc_51_, 6, v_supN_41_);
lean_ctor_set(v_reuseFailAlloc_51_, 7, v_n_34_);
lean_ctor_set(v_reuseFailAlloc_51_, 8, v_Xc_42_);
lean_ctor_set(v_reuseFailAlloc_51_, 9, v_acgF_43_);
lean_ctor_set(v_reuseFailAlloc_51_, 10, v_modF_44_);
lean_ctor_set(v_reuseFailAlloc_51_, 11, v_sg_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_RunIn_SecNorm_base___boxed(lean_object* v_D_54_, lean_object* v_B_55_, lean_object* v_n_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_tree_GlobalTheory_RunIn_SecNorm_base(v_D_54_, v_B_55_, v_n_56_);
lean_dec_ref(v_D_54_);
return v_res_57_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntAtExtExtAll(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_OEOsInjective(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_ThetaValues_SWEqSOf(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IntAtExtExtAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_OEOsInjective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
