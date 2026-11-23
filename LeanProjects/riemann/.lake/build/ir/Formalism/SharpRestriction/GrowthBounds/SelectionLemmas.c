// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting public import Formalism.SharpRestriction.GrowthBounds.DataG public import Formalism.SharpRestriction.ParConsts
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Finset_prod___at___00Formalism_G0_esymmR_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_powersetCard___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg___lam__0(lean_object* v_00_u03ba_1_, lean_object* v_v_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_00_u03ba_1_, v_v_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg___lam__1(lean_object* v___f_4_, lean_object* v_B_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lp_tree_Finset_prod___at___00Formalism_G0_esymmR_spec__0___redArg(v_B_5_, v___f_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg(lean_object* v_VV_7_, lean_object* v_00_u03ba_8_, lean_object* v_k_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_10_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_10_, 0, v_00_u03ba_8_);
v___f_11_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_11_, 0, v___f_10_);
v___x_12_ = lp_mathlib_Finset_powersetCard___redArg(v_k_9_, v_VV_7_);
v___x_13_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_12_, v___f_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn(lean_object* v_00_u03b9_14_, lean_object* v_VV_15_, lean_object* v_00_u03ba_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_tree_Formalism_MainNotions_SelectionLemmas_esymmOn___redArg(v_VV_15_, v_00_u03ba_16_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg___lam__0(lean_object* v_t_19_, lean_object* v_D_20_, lean_object* v_m_21_, lean_object* v_v_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = lean_apply_1(v_t_19_, v_v_22_);
v___x_24_ = lean_nat_add(v___x_23_, v_D_20_);
lean_dec(v___x_23_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v___x_24_, v___x_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_nat_mul(v_m_21_, v___x_26_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg___lam__0___boxed(lean_object* v_t_28_, lean_object* v_D_29_, lean_object* v_m_30_, lean_object* v_v_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg___lam__0(v_t_28_, v_D_29_, v_m_30_, v_v_31_);
lean_dec(v_m_30_);
lean_dec(v_D_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg(lean_object* v_VV_33_, lean_object* v_m_34_, lean_object* v_D_35_, lean_object* v_t_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___x_38_; 
v___f_37_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_37_, 0, v_t_36_);
lean_closure_set(v___f_37_, 1, v_D_35_);
lean_closure_set(v___f_37_, 2, v_m_34_);
v___x_38_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v_VV_33_, v___f_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_SelectionLemmas_tau(lean_object* v_00_u03b9_39_, lean_object* v_VV_40_, lean_object* v_m_41_, lean_object* v_D_42_, lean_object* v_t_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_tree_Formalism_MainNotions_SelectionLemmas_tau___redArg(v_VV_40_, v_m_41_, v_D_42_, v_t_43_);
return v___x_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SelectionLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
