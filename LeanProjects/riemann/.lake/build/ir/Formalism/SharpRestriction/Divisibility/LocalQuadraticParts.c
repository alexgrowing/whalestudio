// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataParamsS public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.DataBu public import Formalism.LocalRingCardinality.PrincipalHermitianLattice public import Formalism.LocalRingCardinality.DataKap public import Formalism.LocalRingCardinality.KernelPlaceMeanBound public import Formalism.LocalRingCardinality.DataAmbForm public import Formalism.LocalRingCardinality.DataRRMetric public import Formalism.LocalRingCardinality.DataNChoice public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_ZMod_unitOfCoprime___redArg(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_nTT(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_nTT___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_MuH(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_hclP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_hclP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_askPrimes(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_askPrimes___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_nTT(lean_object* v_D_1_){
_start:
{
lean_object* v_host_2_; lean_object* v_TT_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_host_2_ = lean_ctor_get(v_D_1_, 1);
v_TT_3_ = lean_ctor_get(v_host_2_, 10);
v___x_4_ = l_List_lengthTR___redArg(v_TT_3_);
v___x_5_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_nTT___boxed(lean_object* v_D_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_tree_Formalism_MainNotions_LocalQuadraticParts_nTT(v_D_6_);
lean_dec_ref(v_D_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_MuH(lean_object* v_D_8_, lean_object* v_u_9_){
_start:
{
lean_object* v_div_10_; lean_object* v_Nu_11_; lean_object* v___x_12_; lean_object* v_addV_13_; lean_object* v_modV_14_; lean_object* v_modOV_15_; lean_object* v_fin_u03b9_16_; lean_object* v_dec_u03b9_17_; lean_object* v_b_18_; lean_object* v_X_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_27_; 
v_div_10_ = lean_ctor_get(v_D_8_, 12);
lean_inc_ref(v_div_10_);
lean_dec_ref(v_D_8_);
v_Nu_11_ = lean_ctor_get(v_div_10_, 1);
lean_inc_ref(v_Nu_11_);
lean_dec_ref(v_div_10_);
v___x_12_ = lean_apply_1(v_Nu_11_, v_u_9_);
v_addV_13_ = lean_ctor_get(v___x_12_, 0);
v_modV_14_ = lean_ctor_get(v___x_12_, 1);
v_modOV_15_ = lean_ctor_get(v___x_12_, 2);
v_fin_u03b9_16_ = lean_ctor_get(v___x_12_, 3);
v_dec_u03b9_17_ = lean_ctor_get(v___x_12_, 4);
v_b_18_ = lean_ctor_get(v___x_12_, 5);
v_X_19_ = lean_ctor_get(v___x_12_, 6);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v___x_12_, 7);
lean_dec(v_unused_28_);
v___x_21_ = v___x_12_;
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_X_19_);
lean_inc(v_b_18_);
lean_inc(v_dec_u03b9_17_);
lean_inc(v_fin_u03b9_16_);
lean_inc(v_modOV_15_);
lean_inc(v_modV_14_);
lean_inc(v_addV_13_);
lean_dec(v___x_12_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_box(0);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 7, v___x_23_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_addV_13_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_modV_14_);
lean_ctor_set(v_reuseFailAlloc_26_, 2, v_modOV_15_);
lean_ctor_set(v_reuseFailAlloc_26_, 3, v_fin_u03b9_16_);
lean_ctor_set(v_reuseFailAlloc_26_, 4, v_dec_u03b9_17_);
lean_ctor_set(v_reuseFailAlloc_26_, 5, v_b_18_);
lean_ctor_set(v_reuseFailAlloc_26_, 6, v_X_19_);
lean_ctor_set(v_reuseFailAlloc_26_, 7, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_hclP(lean_object* v_e_29_, lean_object* v_p_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_31_ = lean_unsigned_to_nat(2u);
v___x_32_ = lean_nat_add(v_e_29_, v___x_31_);
v___x_33_ = lean_nat_pow(v___x_31_, v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = lean_nat_gcd(v_p_30_, v___x_33_);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_dec_eq(v___x_34_, v___x_35_);
lean_dec(v___x_34_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v_toOne_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
lean_dec(v_p_30_);
v___x_37_ = lp_mathlib_ZMod_commRing(v___x_33_);
v___x_38_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_38_);
lean_dec_ref(v___x_38_);
v_toOne_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v___x_39_, 1);
lean_dec(v_unused_48_);
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toOne_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
lean_inc(v_toOne_40_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v_toOne_40_);
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_toOne_40_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_toOne_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
else
{
lean_object* v___x_49_; 
v___x_49_ = lp_mathlib_ZMod_unitOfCoprime___redArg(v___x_33_, v_p_30_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_hclP___boxed(lean_object* v_e_50_, lean_object* v_p_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_tree_Formalism_MainNotions_LocalQuadraticParts_hclP(v_e_50_, v_p_51_);
lean_dec(v_e_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_askPrimes(lean_object* v_a_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = l_Int_toNat(v_a_53_);
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
v___x_57_ = l_List_range(v___x_56_);
v___x_58_ = lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_LocalQuadraticParts_askPrimes___boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_MainNotions_LocalQuadraticParts_askPrimes(v_a_59_);
lean_dec(v_a_59_);
return v_res_60_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParamsS(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataBu(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKap(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_KernelPlaceMeanBound(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataAmbForm(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataRRMetric(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataNChoice(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_ZetaZeroFreeRegion(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_PlaceRankTwoOne(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataParamsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataBu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_KernelPlaceMeanBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataAmbForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataRRMetric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataNChoice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_ZetaZeroFreeRegion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_PlaceRankTwoOne(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
