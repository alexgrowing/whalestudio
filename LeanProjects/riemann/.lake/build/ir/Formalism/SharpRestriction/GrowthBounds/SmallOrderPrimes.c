// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ElevenLe public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
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
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_padicValNat(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_AuxBlock8_lowU(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_AuxBlock8_lowU(lean_object* v_D_1_, lean_object* v_u_2_, lean_object* v_w_3_){
_start:
{
lean_object* v_R_4_; lean_object* v_what_u2082_5_; lean_object* v_places_6_; lean_object* v_mem_7_; lean_object* v_m_8_; lean_object* v_resChar_9_; lean_object* v___x_10_; lean_object* v_C_11_; lean_object* v_DGam_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___f_17_; lean_object* v___f_18_; 
v_R_4_ = lean_ctor_get(v_D_1_, 0);
lean_inc_ref(v_R_4_);
v_what_u2082_5_ = lean_ctor_get(v_D_1_, 4);
v_places_6_ = lean_ctor_get(v_what_u2082_5_, 2);
lean_inc_ref(v_places_6_);
v_mem_7_ = lean_ctor_get(v_D_1_, 10);
lean_inc_ref(v_mem_7_);
lean_dec_ref(v_D_1_);
v_m_8_ = lean_ctor_get(v_R_4_, 2);
lean_inc(v_m_8_);
lean_dec_ref(v_R_4_);
v_resChar_9_ = lean_ctor_get(v_places_6_, 2);
lean_inc_ref(v_resChar_9_);
lean_dec_ref(v_places_6_);
v___x_10_ = lean_apply_1(v_mem_7_, v_u_2_);
v_C_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc_ref(v_C_11_);
lean_dec_ref(v___x_10_);
v_DGam_12_ = lean_ctor_get(v_C_11_, 2);
lean_inc(v_DGam_12_);
lean_dec_ref(v_C_11_);
v___x_13_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_m_8_);
v___x_14_ = lean_apply_1(v_resChar_9_, v_w_3_);
v___x_15_ = lp_mathlib_padicValNat(v___x_14_, v_DGam_12_);
lean_dec(v___x_14_);
v___x_16_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_17_, 0, v___x_13_);
lean_closure_set(v___f_17_, 1, v___x_16_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_18_, 0, v___f_17_);
return v___f_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ElevenLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ElevenLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
