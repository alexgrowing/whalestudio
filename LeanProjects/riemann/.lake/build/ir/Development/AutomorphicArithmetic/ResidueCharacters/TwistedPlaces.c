// Lean compiler output
// Module: Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataParams public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf
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
lean_object* lp_tree_Formalism_BasicNotions_Rows_Data_VV(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_gset(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_VVr(lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083(lean_object* v_D_3_, lean_object* v_L_4_){
_start:
{
lean_object* v_R_5_; lean_object* v_etaSz_6_; lean_object* v_t_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___f_11_; 
v_R_5_ = lean_ctor_get(v_D_3_, 0);
lean_inc_ref(v_R_5_);
lean_dec_ref(v_D_3_);
v_etaSz_6_ = lean_ctor_get(v_L_4_, 15);
lean_inc(v_etaSz_6_);
lean_dec_ref(v_L_4_);
v_t_7_ = lean_ctor_get(v_R_5_, 3);
lean_inc(v_t_7_);
lean_dec_ref(v_R_5_);
v___x_8_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_t_7_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v_etaSz_6_);
lean_closure_set(v___f_9_, 1, v___x_8_);
v___x_10_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083___closed__0, &lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083___closed__0_once, _init_lp_tree_Formalism_MainNotions_TwistedPlaces_eta_u2083___closed__0);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v___f_9_);
lean_closure_set(v___f_11_, 1, v___x_10_);
return v___f_11_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_unsigned_to_nat(2u);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_mod(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(2u);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_mod(v___x_16_, v___x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_gset(lean_object* v_D_18_){
_start:
{
lean_object* v_host_19_; lean_object* v_g_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_host_19_ = lean_ctor_get(v_D_18_, 1);
lean_inc_ref(v_host_19_);
lean_dec_ref(v_D_18_);
v_g_20_ = lean_ctor_get(v_host_19_, 6);
lean_inc_ref_n(v_g_20_, 2);
lean_dec_ref(v_host_19_);
v___x_21_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__0, &lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__0_once, _init_lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__0);
v___x_22_ = lean_apply_1(v_g_20_, v___x_21_);
v___x_23_ = lean_obj_once(&lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__1, &lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__1_once, _init_lp_tree_Formalism_MainNotions_TwistedPlaces_gset___closed__1);
v___x_24_ = lean_apply_1(v_g_20_, v___x_23_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_24_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lp_tree_Multiset_ndinsert___at___00Formalism_BasicNotions_SizeData_u2082_gTypes_spec__0(v___x_22_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TwistedPlaces_VVr(lean_object* v_D_28_, lean_object* v_l_29_){
_start:
{
lean_object* v_R_30_; lean_object* v_what_u2082_31_; lean_object* v___x_32_; lean_object* v___f_33_; 
v_R_30_ = lean_ctor_get(v_D_28_, 0);
lean_inc_ref(v_R_30_);
v_what_u2082_31_ = lean_ctor_get(v_D_28_, 4);
lean_inc_ref(v_what_u2082_31_);
lean_dec_ref(v_D_28_);
v___x_32_ = lp_tree_Formalism_BasicNotions_Rows_Data_VV(v_R_30_, v_what_u2082_31_, v_l_29_);
lean_dec_ref(v_R_30_);
v___f_33_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_33_, 0, v___x_32_);
return v___f_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AutomorphicArithmetic_ResidueCharacters_TwistedPlaces(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
