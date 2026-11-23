// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.WeightAlgebra
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataParams public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.Divisibility.WeightFamilies public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_Tp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_scaled_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_scaled_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Msup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Msup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_WWc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_WWc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Thc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Thc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Nat_cast___at___00Formalism_MainNotions_WeightAlgebra_PJ_Thc_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_MainNotions_WeightAlgebra_PJ_Thc_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Theta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Theta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_qq(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_g0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_g0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KHyp_deg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KHyp_deg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KAdm_deg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KAdm_deg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_n0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_n0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__2;
static lean_once_cell_t lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg___lam__0(lean_object* v_aP_1_, lean_object* v_aP_2_, lean_object* v_00_u03c4_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_i_4_);
lean_inc(v_00_u03c4_3_);
v___x_5_ = lean_apply_2(v_aP_1_, v_00_u03c4_3_, v_i_4_);
v___x_6_ = lean_apply_2(v_aP_2_, v_00_u03c4_3_, v_i_4_);
v___x_7_ = lean_nat_add(v___x_5_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg___lam__1(lean_object* v_aM_8_, lean_object* v_aM_9_, lean_object* v_00_u03c4_10_, lean_object* v_i_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
lean_inc(v_i_11_);
lean_inc(v_00_u03c4_10_);
v___x_12_ = lean_apply_2(v_aM_8_, v_00_u03c4_10_, v_i_11_);
v___x_13_ = lean_apply_2(v_aM_9_, v_00_u03c4_10_, v_i_11_);
v___x_14_ = lean_nat_add(v___x_12_, v___x_13_);
lean_dec(v___x_13_);
lean_dec(v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg(lean_object* v_w_15_, lean_object* v_w_x27_16_){
_start:
{
lean_object* v_aP_17_; lean_object* v_aM_18_; lean_object* v_n_19_; lean_object* v_aP_20_; lean_object* v_aM_21_; lean_object* v_n_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_32_; 
v_aP_17_ = lean_ctor_get(v_w_15_, 0);
lean_inc_ref(v_aP_17_);
v_aM_18_ = lean_ctor_get(v_w_15_, 1);
lean_inc_ref(v_aM_18_);
v_n_19_ = lean_ctor_get(v_w_15_, 2);
lean_inc(v_n_19_);
lean_dec_ref(v_w_15_);
v_aP_20_ = lean_ctor_get(v_w_x27_16_, 0);
v_aM_21_ = lean_ctor_get(v_w_x27_16_, 1);
v_n_22_ = lean_ctor_get(v_w_x27_16_, 2);
v_isSharedCheck_32_ = !lean_is_exclusive(v_w_x27_16_);
if (v_isSharedCheck_32_ == 0)
{
v___x_24_ = v_w_x27_16_;
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_n_22_);
lean_inc(v_aM_21_);
lean_inc(v_aP_20_);
lean_dec(v_w_x27_16_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_26_, 0, v_aP_17_);
lean_closure_set(v___f_26_, 1, v_aP_20_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg___lam__1), 4, 2);
lean_closure_set(v___f_27_, 0, v_aM_18_);
lean_closure_set(v___f_27_, 1, v_aM_21_);
v___x_28_ = lean_nat_add(v_n_19_, v_n_22_);
lean_dec(v_n_22_);
lean_dec(v_n_19_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 2, v___x_28_);
lean_ctor_set(v___x_24_, 1, v___f_27_);
lean_ctor_set(v___x_24_, 0, v___f_26_);
v___x_30_ = v___x_24_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___f_26_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___f_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd(lean_object* v_D_33_, lean_object* v_j_34_, lean_object* v_w_35_, lean_object* v_w_x27_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg(v_w_35_, v_w_x27_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___boxed(lean_object* v_D_38_, lean_object* v_j_39_, lean_object* v_w_40_, lean_object* v_w_x27_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wadd(v_D_38_, v_j_39_, v_w_40_, v_w_x27_41_);
lean_dec(v_j_39_);
lean_dec_ref(v_D_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__0(lean_object* v_aP_43_, lean_object* v_c_44_, lean_object* v_00_u03c4_45_, lean_object* v_i_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_apply_2(v_aP_43_, v_00_u03c4_45_, v_i_46_);
v___x_48_ = lean_nat_mul(v_c_44_, v___x_47_);
lean_dec(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__0___boxed(lean_object* v_aP_49_, lean_object* v_c_50_, lean_object* v_00_u03c4_51_, lean_object* v_i_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__0(v_aP_49_, v_c_50_, v_00_u03c4_51_, v_i_52_);
lean_dec(v_c_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__1(lean_object* v_aM_54_, lean_object* v_c_55_, lean_object* v_00_u03c4_56_, lean_object* v_i_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_apply_2(v_aM_54_, v_00_u03c4_56_, v_i_57_);
v___x_59_ = lean_nat_mul(v_c_55_, v___x_58_);
lean_dec(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__1___boxed(lean_object* v_aM_60_, lean_object* v_c_61_, lean_object* v_00_u03c4_62_, lean_object* v_i_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__1(v_aM_60_, v_c_61_, v_00_u03c4_62_, v_i_63_);
lean_dec(v_c_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg(lean_object* v_c_65_, lean_object* v_w_66_){
_start:
{
lean_object* v_aP_67_; lean_object* v_aM_68_; lean_object* v_n_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
v_aP_67_ = lean_ctor_get(v_w_66_, 0);
v_aM_68_ = lean_ctor_get(v_w_66_, 1);
v_n_69_ = lean_ctor_get(v_w_66_, 2);
v_isSharedCheck_79_ = !lean_is_exclusive(v_w_66_);
if (v_isSharedCheck_79_ == 0)
{
v___x_71_ = v_w_66_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_n_69_);
lean_inc(v_aM_68_);
lean_inc(v_aP_67_);
lean_dec(v_w_66_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
lean_inc_n(v_c_65_, 2);
v___f_73_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_73_, 0, v_aP_67_);
lean_closure_set(v___f_73_, 1, v_c_65_);
v___f_74_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_74_, 0, v_aM_68_);
lean_closure_set(v___f_74_, 1, v_c_65_);
v___x_75_ = lean_nat_mul(v_c_65_, v_n_69_);
lean_dec(v_n_69_);
lean_dec(v_c_65_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 2, v___x_75_);
lean_ctor_set(v___x_71_, 1, v___f_74_);
lean_ctor_set(v___x_71_, 0, v___f_73_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___f_73_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___f_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul(lean_object* v_D_80_, lean_object* v_j_81_, lean_object* v_c_82_, lean_object* v_w_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg(v_c_82_, v_w_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___boxed(lean_object* v_D_85_, lean_object* v_j_86_, lean_object* v_c_87_, lean_object* v_w_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul(v_D_85_, v_j_86_, v_c_87_, v_w_88_);
lean_dec(v_j_86_);
lean_dec_ref(v_D_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___lam__0(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(0u);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___lam__0___boxed(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___lam__0(v_x_93_, v_x_94_);
lean_dec(v_x_94_);
lean_dec(v_x_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(lean_object* v_n_97_){
_start:
{
lean_object* v___f_98_; lean_object* v___x_99_; 
v___f_98_ = ((lean_object*)(lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg___closed__0));
v___x_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_99_, 0, v___f_98_);
lean_ctor_set(v___x_99_, 1, v___f_98_);
lean_ctor_set(v___x_99_, 2, v_n_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar(lean_object* v_D_100_, lean_object* v_j_101_, lean_object* v_n_102_, lean_object* v_h_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(v_n_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___boxed(lean_object* v_D_105_, lean_object* v_j_106_, lean_object* v_n_107_, lean_object* v_h_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar(v_D_105_, v_j_106_, v_n_107_, v_h_108_);
lean_dec(v_j_106_);
lean_dec_ref(v_D_105_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(lean_object* v_p_110_, lean_object* v_l_111_, lean_object* v_i_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v_i_112_, v___x_113_);
v___x_115_ = lean_nat_dec_lt(v___x_114_, v_p_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v___x_114_);
v___x_116_ = lean_apply_1(v_l_111_, v_i_112_);
v___x_117_ = lean_nat_to_int(v___x_116_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_inc_ref(v_l_111_);
v___x_118_ = lean_apply_1(v_l_111_, v_i_112_);
v___x_119_ = lean_nat_to_int(v___x_118_);
v___x_120_ = lean_apply_1(v_l_111_, v___x_114_);
v___x_121_ = lean_nat_to_int(v___x_120_);
v___x_122_ = lean_int_sub(v___x_119_, v___x_121_);
lean_dec(v___x_121_);
lean_dec(v___x_119_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ___boxed(lean_object* v_p_123_, lean_object* v_l_124_, lean_object* v_i_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_p_123_, v_l_124_, v_i_125_);
lean_dec(v_p_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__0(lean_object* v_w_127_, lean_object* v_00_u03c4_128_, lean_object* v_i_129_){
_start:
{
lean_object* v_aP_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_aP_130_ = lean_ctor_get(v_w_127_, 0);
lean_inc_ref(v_aP_130_);
lean_dec_ref(v_w_127_);
v___x_131_ = lean_apply_2(v_aP_130_, v_00_u03c4_128_, v_i_129_);
v___x_132_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__1(lean_object* v_w_133_, lean_object* v_00_u03c4_134_, lean_object* v_i_135_){
_start:
{
lean_object* v_aM_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_aM_136_ = lean_ctor_get(v_w_133_, 1);
lean_inc_ref(v_aM_136_);
lean_dec_ref(v_w_133_);
v___x_137_ = lean_apply_2(v_aM_136_, v_00_u03c4_134_, v_i_135_);
v___x_138_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__2(lean_object* v_R_139_, lean_object* v_j_140_, lean_object* v_w_141_, lean_object* v_00_u03c4_142_){
_start:
{
lean_object* v___x_143_; lean_object* v_fst_144_; lean_object* v_snd_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___f_152_; 
v___x_143_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_139_, v_j_140_);
v_fst_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_fst_144_);
v_snd_145_ = lean_ctor_get(v___x_143_, 1);
lean_inc(v_snd_145_);
lean_dec_ref(v___x_143_);
lean_inc(v_00_u03c4_142_);
lean_inc_ref(v_w_141_);
v___f_146_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__0), 3, 2);
lean_closure_set(v___f_146_, 0, v_w_141_);
lean_closure_set(v___f_146_, 1, v_00_u03c4_142_);
v___f_147_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__1), 3, 2);
lean_closure_set(v___f_147_, 0, v_w_141_);
lean_closure_set(v___f_147_, 1, v_00_u03c4_142_);
v___x_148_ = l_List_finRange(v_fst_144_);
v___x_149_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_148_, v___f_146_);
v___x_150_ = l_List_finRange(v_snd_145_);
v___x_151_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_150_, v___f_147_);
v___f_152_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_152_, 0, v___x_149_);
lean_closure_set(v___f_152_, 1, v___x_151_);
return v___f_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__2___boxed(lean_object* v_R_153_, lean_object* v_j_154_, lean_object* v_w_155_, lean_object* v_00_u03c4_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__2(v_R_153_, v_j_154_, v_w_155_, v_00_u03c4_156_);
lean_dec(v_j_154_);
lean_dec_ref(v_R_153_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_absA(lean_object* v_D_158_, lean_object* v_j_159_, lean_object* v_w_160_){
_start:
{
lean_object* v_what_u2082_161_; lean_object* v_R_162_; lean_object* v_instTau_163_; lean_object* v___f_164_; lean_object* v___x_165_; 
v_what_u2082_161_ = lean_ctor_get(v_D_158_, 4);
lean_inc_ref(v_what_u2082_161_);
v_R_162_ = lean_ctor_get(v_D_158_, 0);
lean_inc_ref(v_R_162_);
lean_dec_ref(v_D_158_);
v_instTau_163_ = lean_ctor_get(v_what_u2082_161_, 5);
lean_inc(v_instTau_163_);
lean_dec_ref(v_what_u2082_161_);
v___f_164_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_absA___lam__2___boxed), 4, 3);
lean_closure_set(v___f_164_, 0, v_R_162_);
lean_closure_set(v___f_164_, 1, v_j_159_);
lean_closure_set(v___f_164_, 2, v_w_160_);
v___x_165_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v_instTau_163_, v___f_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__0(lean_object* v_w_166_, lean_object* v_00_u03c4_167_, lean_object* v_i_168_){
_start:
{
lean_object* v_aP_169_; lean_object* v___x_170_; 
v_aP_169_ = lean_ctor_get(v_w_166_, 0);
lean_inc_ref(v_aP_169_);
lean_dec_ref(v_w_166_);
v___x_170_ = lean_apply_2(v_aP_169_, v_00_u03c4_167_, v_i_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__1(lean_object* v_w_171_, lean_object* v_00_u03c4_172_, lean_object* v_i_173_){
_start:
{
lean_object* v_aM_174_; lean_object* v___x_175_; 
v_aM_174_ = lean_ctor_get(v_w_171_, 1);
lean_inc_ref(v_aM_174_);
lean_dec_ref(v_w_171_);
v___x_175_ = lean_apply_2(v_aM_174_, v_00_u03c4_172_, v_i_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__2(lean_object* v_R_176_, lean_object* v_j_177_, lean_object* v_w_178_, lean_object* v_00_u03c4_179_){
_start:
{
lean_object* v___x_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_180_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_176_, v_j_177_);
v_fst_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_fst_181_);
v_snd_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_snd_182_);
lean_dec_ref(v___x_180_);
lean_inc(v_00_u03c4_179_);
lean_inc_ref(v_w_178_);
v___f_183_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__0), 3, 2);
lean_closure_set(v___f_183_, 0, v_w_178_);
lean_closure_set(v___f_183_, 1, v_00_u03c4_179_);
v___f_184_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__1), 3, 2);
lean_closure_set(v___f_184_, 0, v_w_178_);
lean_closure_set(v___f_184_, 1, v_00_u03c4_179_);
v___x_185_ = l_List_finRange(v_fst_181_);
v___x_186_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_185_, v___f_183_);
v___x_187_ = l_List_finRange(v_snd_182_);
v___x_188_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_187_, v___f_184_);
v___x_189_ = lean_nat_add(v___x_186_, v___x_188_);
lean_dec(v___x_188_);
lean_dec(v___x_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__2___boxed(lean_object* v_R_190_, lean_object* v_j_191_, lean_object* v_w_192_, lean_object* v_00_u03c4_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__2(v_R_190_, v_j_191_, v_w_192_, v_00_u03c4_193_);
lean_dec(v_j_191_);
lean_dec_ref(v_R_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_degP(lean_object* v_D_195_, lean_object* v_j_196_, lean_object* v_w_197_){
_start:
{
lean_object* v_what_u2082_198_; lean_object* v_R_199_; lean_object* v_instTau_200_; lean_object* v___f_201_; lean_object* v___x_202_; 
v_what_u2082_198_ = lean_ctor_get(v_D_195_, 4);
lean_inc_ref(v_what_u2082_198_);
v_R_199_ = lean_ctor_get(v_D_195_, 0);
lean_inc_ref(v_R_199_);
lean_dec_ref(v_D_195_);
v_instTau_200_ = lean_ctor_get(v_what_u2082_198_, 5);
lean_inc(v_instTau_200_);
lean_dec_ref(v_what_u2082_198_);
v___f_201_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightAlgebra_degP___lam__2___boxed), 4, 3);
lean_closure_set(v___f_201_, 0, v_R_199_);
lean_closure_set(v___f_201_, 1, v_j_196_);
lean_closure_set(v___f_201_, 2, v_w_197_);
v___x_202_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v_instTau_200_, v___f_201_);
return v___x_202_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__0(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_to_int(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt(lean_object* v_D_207_, lean_object* v_j_208_, lean_object* v_w_209_, lean_object* v_00_u03c4_210_){
_start:
{
lean_object* v_R_211_; lean_object* v___x_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___x_227_; lean_object* v___y_229_; uint8_t v___x_237_; 
v_R_211_ = lean_ctor_get(v_D_207_, 0);
v___x_212_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_211_, v_j_208_);
v_fst_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_fst_213_);
v_snd_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v___x_212_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_nat_dec_lt(v___x_227_, v_fst_213_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1, &lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1);
v___y_229_ = v___x_238_;
goto v___jp_228_;
}
else
{
lean_object* v_aP_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_aP_239_ = lean_ctor_get(v_w_209_, 0);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_sub(v_fst_213_, v___x_240_);
lean_inc_ref(v_aP_239_);
lean_inc(v_00_u03c4_210_);
v___x_242_ = lean_apply_2(v_aP_239_, v_00_u03c4_210_, v___x_241_);
v___x_243_ = lean_nat_to_int(v___x_242_);
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
v___jp_215_:
{
lean_object* v_n_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_n_218_ = lean_ctor_get(v_w_209_, 2);
lean_inc(v_n_218_);
lean_dec_ref(v_w_209_);
v___x_219_ = lean_int_add(v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec(v___y_216_);
v___x_220_ = lean_nat_to_int(v_n_218_);
v___x_221_ = lean_int_add(v___x_219_, v___x_220_);
lean_dec(v___x_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_nat_add(v_fst_213_, v_snd_214_);
lean_dec(v_snd_214_);
lean_dec(v_fst_213_);
v___x_223_ = lean_nat_to_int(v___x_222_);
v___x_224_ = lean_int_sub(v___x_221_, v___x_223_);
lean_dec(v___x_223_);
lean_dec(v___x_221_);
v___x_225_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__0, &lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__0_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__0);
v___x_226_ = lean_int_add(v___x_224_, v___x_225_);
lean_dec(v___x_224_);
return v___x_226_;
}
v___jp_228_:
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_lt(v___x_227_, v_snd_214_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; 
lean_dec(v_00_u03c4_210_);
v___x_231_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1, &lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___closed__1);
v___y_216_ = v___y_229_;
v___y_217_ = v___x_231_;
goto v___jp_215_;
}
else
{
lean_object* v_aM_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_aM_232_ = lean_ctor_get(v_w_209_, 1);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_sub(v_snd_214_, v___x_233_);
lean_inc_ref(v_aM_232_);
v___x_235_ = lean_apply_2(v_aM_232_, v_00_u03c4_210_, v___x_234_);
v___x_236_ = lean_nat_to_int(v___x_235_);
v___y_216_ = v___y_229_;
v___y_217_ = v___x_236_;
goto v___jp_215_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt___boxed(lean_object* v_D_244_, lean_object* v_j_245_, lean_object* v_w_246_, lean_object* v_00_u03c4_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_tree_Formalism_MainNotions_WeightAlgebra_ncAt(v_D_244_, v_j_245_, v_w_246_, v_00_u03c4_247_);
lean_dec(v_j_245_);
lean_dec_ref(v_D_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(lean_object* v_D_249_, lean_object* v_j_250_, lean_object* v_T_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lp_tree_Formalism_MainNotions_WeightFamilies_dimY(v_D_249_, v_j_250_);
v___x_253_ = lean_nat_add(v_T_251_, v___x_252_);
lean_dec(v___x_252_);
v___x_254_ = lean_unsigned_to_nat(2u);
v___x_255_ = lean_nat_add(v___x_253_, v___x_254_);
lean_dec(v___x_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_Tp___boxed(lean_object* v_D_256_, lean_object* v_j_257_, lean_object* v_T_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(v_D_256_, v_j_257_, v_T_258_);
lean_dec(v_T_258_);
lean_dec(v_j_257_);
lean_dec_ref(v_D_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___redArg___lam__0(lean_object* v_f_u2097_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_apply_1(v_f_u2097_260_, v___y_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___redArg(lean_object* v_f_u2097_263_){
_start:
{
lean_object* v___f_264_; 
v___f_264_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_264_, 0, v_f_u2097_263_);
return v___f_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0(lean_object* v_B_265_, lean_object* v_j_266_, lean_object* v_w_267_, lean_object* v_X_268_, lean_object* v_inst_269_, lean_object* v_f_u2097_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_271_, 0, v_f_u2097_270_);
return v___f_271_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0___boxed(lean_object* v_B_272_, lean_object* v_j_273_, lean_object* v_w_274_, lean_object* v_X_275_, lean_object* v_inst_276_, lean_object* v_f_u2097_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = lp_tree_LinearMap_restrictScalars___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__0(v_B_272_, v_j_273_, v_w_274_, v_X_275_, v_inst_276_, v_f_u2097_277_);
lean_dec_ref(v_X_275_);
lean_dec_ref(v_w_274_);
lean_dec(v_j_273_);
lean_dec_ref(v_B_272_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__1(lean_object* v_B_279_, lean_object* v_j_280_, lean_object* v_w_281_, lean_object* v_X_282_, lean_object* v_00_u03c3_u2081_u2082_283_, lean_object* v_inst_284_, lean_object* v_f_285_, lean_object* v_p_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__1___boxed(lean_object* v_B_288_, lean_object* v_j_289_, lean_object* v_w_290_, lean_object* v_X_291_, lean_object* v_00_u03c3_u2081_u2082_292_, lean_object* v_inst_293_, lean_object* v_f_294_, lean_object* v_p_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_emb_spec__1(v_B_288_, v_j_289_, v_w_290_, v_X_291_, v_00_u03c3_u2081_u2082_292_, v_inst_293_, v_f_294_, v_p_295_);
lean_dec(v_f_294_);
lean_dec(v_00_u03c3_u2081_u2082_292_);
lean_dec_ref(v_X_291_);
lean_dec_ref(v_w_290_);
lean_dec(v_j_289_);
lean_dec_ref(v_B_288_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___redArg(lean_object* v_B_297_, lean_object* v_j_298_, lean_object* v_X_299_, lean_object* v_w_300_, lean_object* v_N_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(0);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___redArg___boxed(lean_object* v_B_303_, lean_object* v_j_304_, lean_object* v_X_305_, lean_object* v_w_306_, lean_object* v_N_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___redArg(v_B_303_, v_j_304_, v_X_305_, v_w_306_, v_N_307_);
lean_dec_ref(v_w_306_);
lean_dec_ref(v_X_305_);
lean_dec(v_j_304_);
lean_dec_ref(v_B_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb(lean_object* v_D_309_, lean_object* v_B_310_, lean_object* v_P_311_, lean_object* v_j_312_, lean_object* v_X_313_, lean_object* v_w_314_, lean_object* v_N_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_box(0);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb___boxed(lean_object* v_D_317_, lean_object* v_B_318_, lean_object* v_P_319_, lean_object* v_j_320_, lean_object* v_X_321_, lean_object* v_w_322_, lean_object* v_N_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_emb(v_D_317_, v_B_318_, v_P_319_, v_j_320_, v_X_321_, v_w_322_, v_N_323_);
lean_dec_ref(v_w_322_);
lean_dec_ref(v_X_321_);
lean_dec(v_j_320_);
lean_dec_ref(v_P_319_);
lean_dec_ref(v_B_318_);
lean_dec_ref(v_D_317_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_scaled_spec__0(lean_object* v_B_325_, lean_object* v_j_326_, lean_object* v_w_327_, lean_object* v_00_u03c3_u2081_u2082_328_, lean_object* v_inst_329_, lean_object* v_f_330_, lean_object* v_p_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_scaled_spec__0___boxed(lean_object* v_B_333_, lean_object* v_j_334_, lean_object* v_w_335_, lean_object* v_00_u03c3_u2081_u2082_336_, lean_object* v_inst_337_, lean_object* v_f_338_, lean_object* v_p_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = lp_tree_Submodule_map___at___00Formalism_MainNotions_WeightAlgebra_PJ_scaled_spec__0(v_B_333_, v_j_334_, v_w_335_, v_00_u03c3_u2081_u2082_336_, v_inst_337_, v_f_338_, v_p_339_);
lean_dec(v_f_338_);
lean_dec(v_00_u03c3_u2081_u2082_336_);
lean_dec_ref(v_w_335_);
lean_dec(v_j_334_);
lean_dec_ref(v_B_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg___lam__0(lean_object* v_modOC_341_, lean_object* v_j_342_, lean_object* v_w_343_, lean_object* v_s_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_apply_4(v_modOC_341_, v_j_342_, v_w_343_, v_s_344_, v___y_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg(lean_object* v_B_347_, lean_object* v_j_348_, lean_object* v_s_349_, lean_object* v_w_350_, lean_object* v_N_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg___boxed(lean_object* v_B_353_, lean_object* v_j_354_, lean_object* v_s_355_, lean_object* v_w_356_, lean_object* v_N_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___redArg(v_B_353_, v_j_354_, v_s_355_, v_w_356_, v_N_357_);
lean_dec_ref(v_w_356_);
lean_dec(v_s_355_);
lean_dec(v_j_354_);
lean_dec_ref(v_B_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled(lean_object* v_D_359_, lean_object* v_B_360_, lean_object* v_P_361_, lean_object* v_j_362_, lean_object* v___X_363_, lean_object* v_s_364_, lean_object* v_w_365_, lean_object* v_N_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled___boxed(lean_object* v_D_368_, lean_object* v_B_369_, lean_object* v_P_370_, lean_object* v_j_371_, lean_object* v___X_372_, lean_object* v_s_373_, lean_object* v_w_374_, lean_object* v_N_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_scaled(v_D_368_, v_B_369_, v_P_370_, v_j_371_, v___X_372_, v_s_373_, v_w_374_, v_N_375_);
lean_dec_ref(v_w_374_);
lean_dec(v_s_373_);
lean_dec_ref(v___X_372_);
lean_dec(v_j_371_);
lean_dec_ref(v_P_370_);
lean_dec_ref(v_B_369_);
lean_dec_ref(v_D_368_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Msup(lean_object* v_D_377_, lean_object* v_B_378_, lean_object* v_P_379_, lean_object* v_j_380_, lean_object* v_X_381_, lean_object* v_w_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Msup___boxed(lean_object* v_D_384_, lean_object* v_B_385_, lean_object* v_P_386_, lean_object* v_j_387_, lean_object* v_X_388_, lean_object* v_w_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Msup(v_D_384_, v_B_385_, v_P_386_, v_j_387_, v_X_388_, v_w_389_);
lean_dec_ref(v_w_389_);
lean_dec_ref(v_X_388_);
lean_dec(v_j_387_);
lean_dec_ref(v_P_386_);
lean_dec_ref(v_B_385_);
lean_dec_ref(v_D_384_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_WWc(lean_object* v_D_391_, lean_object* v_B_392_, lean_object* v_P_393_, lean_object* v_j_394_, lean_object* v_X_395_, lean_object* v_s_396_, lean_object* v_w_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_box(0);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_WWc___boxed(lean_object* v_D_399_, lean_object* v_B_400_, lean_object* v_P_401_, lean_object* v_j_402_, lean_object* v_X_403_, lean_object* v_s_404_, lean_object* v_w_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_WWc(v_D_399_, v_B_400_, v_P_401_, v_j_402_, v_X_403_, v_s_404_, v_w_405_);
lean_dec_ref(v_w_405_);
lean_dec(v_s_404_);
lean_dec_ref(v_X_403_);
lean_dec(v_j_402_);
lean_dec_ref(v_P_401_);
lean_dec_ref(v_B_400_);
lean_dec_ref(v_D_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Thc(lean_object* v_D_407_, lean_object* v_B_408_, lean_object* v_P_409_, lean_object* v_j_410_, lean_object* v_X_411_, lean_object* v_s_412_, lean_object* v_w_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Thc___boxed(lean_object* v_D_415_, lean_object* v_B_416_, lean_object* v_P_417_, lean_object* v_j_418_, lean_object* v_X_419_, lean_object* v_s_420_, lean_object* v_w_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Thc(v_D_415_, v_B_416_, v_P_417_, v_j_418_, v_X_419_, v_s_420_, v_w_421_);
lean_dec_ref(v_w_421_);
lean_dec(v_s_420_);
lean_dec_ref(v_X_419_);
lean_dec(v_j_418_);
lean_dec_ref(v_P_417_);
lean_dec_ref(v_B_416_);
lean_dec_ref(v_D_415_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Nat_cast___at___00Formalism_MainNotions_WeightAlgebra_PJ_Thc_spec__0_spec__0(lean_object* v_B_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_fKO_425_; lean_object* v_toCommRing_426_; lean_object* v_toSemiring_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_toNatCast_430_; lean_object* v___x_431_; 
v_fKO_425_ = lean_ctor_get(v_B_423_, 0);
lean_inc_ref(v_fKO_425_);
lean_dec_ref(v_B_423_);
v_toCommRing_426_ = lean_ctor_get(v_fKO_425_, 0);
lean_inc_ref(v_toCommRing_426_);
lean_dec_ref(v_fKO_425_);
v_toSemiring_427_ = lean_ctor_get(v_toCommRing_426_, 0);
lean_inc_ref(v_toSemiring_427_);
lean_dec_ref(v_toCommRing_426_);
v___x_428_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_427_);
v___x_429_ = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(v___x_428_);
v_toNatCast_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_toNatCast_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = lean_apply_1(v_toNatCast_430_, v_a_424_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* lp_tree_Nat_cast___at___00Formalism_MainNotions_WeightAlgebra_PJ_Thc_spec__0(lean_object* v_B_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lp_tree_Nat_cast___at___00Nat_cast___at___00Formalism_MainNotions_WeightAlgebra_PJ_Thc_spec__0_spec__0(v_B_432_, v_a_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___redArg(lean_object* v_D_435_, lean_object* v_j_436_, lean_object* v_wL_437_, lean_object* v_wF_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lp_tree_Formalism_MainNotions_WeightFamilies_dimY(v_D_435_, v_j_436_);
v___x_440_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wsmul___redArg(v___x_439_, v_wL_437_);
v___x_441_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wadd___redArg(v_wF_438_, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___redArg___boxed(lean_object* v_D_442_, lean_object* v_j_443_, lean_object* v_wL_444_, lean_object* v_wF_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___redArg(v_D_442_, v_j_443_, v_wL_444_, v_wF_445_);
lean_dec(v_j_443_);
lean_dec_ref(v_D_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0(lean_object* v_D_447_, lean_object* v_B_448_, lean_object* v_P_449_, lean_object* v_j_450_, lean_object* v___X_451_, lean_object* v_wL_452_, lean_object* v_wF_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___redArg(v_D_447_, v_j_450_, v_wL_452_, v_wF_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0___boxed(lean_object* v_D_455_, lean_object* v_B_456_, lean_object* v_P_457_, lean_object* v_j_458_, lean_object* v___X_459_, lean_object* v_wL_460_, lean_object* v_wF_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_wF0(v_D_455_, v_B_456_, v_P_457_, v_j_458_, v___X_459_, v_wL_460_, v_wF_461_);
lean_dec_ref(v___X_459_);
lean_dec(v_j_458_);
lean_dec_ref(v_P_457_);
lean_dec_ref(v_B_456_);
lean_dec_ref(v_D_455_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Theta(lean_object* v_D_463_, lean_object* v_B_464_, lean_object* v_P_465_, lean_object* v_j_466_, lean_object* v_X_467_, lean_object* v_S_468_, lean_object* v_ka_469_, lean_object* v_wL_470_, lean_object* v_wF_471_, lean_object* v_T_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Theta___boxed(lean_object* v_D_474_, lean_object* v_B_475_, lean_object* v_P_476_, lean_object* v_j_477_, lean_object* v_X_478_, lean_object* v_S_479_, lean_object* v_ka_480_, lean_object* v_wL_481_, lean_object* v_wF_482_, lean_object* v_T_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = lp_tree_Formalism_MainNotions_WeightAlgebra_PJ_Theta(v_D_474_, v_B_475_, v_P_476_, v_j_477_, v_X_478_, v_S_479_, v_ka_480_, v_wL_481_, v_wF_482_, v_T_483_);
lean_dec(v_T_483_);
lean_dec_ref(v_wF_482_);
lean_dec_ref(v_wL_481_);
lean_dec_ref(v_ka_480_);
lean_dec_ref(v_S_479_);
lean_dec_ref(v_X_478_);
lean_dec(v_j_477_);
lean_dec_ref(v_P_476_);
lean_dec_ref(v_B_475_);
lean_dec_ref(v_D_474_);
return v_res_484_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__0(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_mod(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__1(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(2u);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_mod(v___x_489_, v___x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_qq(lean_object* v_D_491_){
_start:
{
lean_object* v_host_492_; lean_object* v_g_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_host_492_ = lean_ctor_get(v_D_491_, 1);
lean_inc_ref(v_host_492_);
lean_dec_ref(v_D_491_);
v_g_493_ = lean_ctor_get(v_host_492_, 6);
lean_inc_ref_n(v_g_493_, 2);
lean_dec_ref(v_host_492_);
v___x_494_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__0, &lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__0_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__0);
v___x_495_ = lean_apply_1(v_g_493_, v___x_494_);
v___x_496_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__1, &lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__1_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_qq___closed__1);
v___x_497_ = lean_apply_1(v_g_493_, v___x_496_);
v___x_498_ = lean_nat_dec_le(v___x_495_, v___x_497_);
if (v___x_498_ == 0)
{
lean_dec(v___x_495_);
return v___x_497_;
}
else
{
lean_dec(v___x_497_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_g0(lean_object* v_D_499_){
_start:
{
lean_object* v_R_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_R_500_ = lean_ctor_get(v_D_499_, 0);
v___x_501_ = lean_unsigned_to_nat(1250u);
v___x_502_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_500_);
v___x_503_ = lean_nat_mul(v___x_501_, v___x_502_);
lean_dec(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_g0___boxed(lean_object* v_D_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = lp_tree_Formalism_MainNotions_WeightAlgebra_g0(v_D_504_);
lean_dec_ref(v_D_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DF(lean_object* v_D_506_, lean_object* v_j_507_, lean_object* v_wL_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lp_tree_Formalism_MainNotions_WeightAlgebra_degP(v_D_506_, v_j_507_, v_wL_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KHyp_deg(lean_object* v_H_510_){
_start:
{
lean_object* v_A1_511_; lean_object* v_Ac_512_; lean_object* v_CRc_513_; lean_object* v___x_514_; 
v_A1_511_ = lean_ctor_get(v_H_510_, 3);
v_Ac_512_ = lean_ctor_get(v_H_510_, 5);
v_CRc_513_ = lean_ctor_get(v_H_510_, 6);
lean_inc(v_CRc_513_);
lean_inc(v_Ac_512_);
lean_inc(v_A1_511_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v_A1_511_);
lean_ctor_set(v___x_514_, 1, v_Ac_512_);
lean_ctor_set(v___x_514_, 2, v_CRc_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KHyp_deg___boxed(lean_object* v_H_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = lp_tree_Formalism_MainNotions_WeightAlgebra_KHyp_deg(v_H_515_);
lean_dec_ref(v_H_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KAdm_deg(lean_object* v_K_517_){
_start:
{
lean_object* v_AG_518_; lean_object* v_Af_519_; lean_object* v_AW_520_; lean_object* v_AL_521_; lean_object* v_CRm_522_; lean_object* v___x_523_; 
v_AG_518_ = lean_ctor_get(v_K_517_, 1);
v_Af_519_ = lean_ctor_get(v_K_517_, 3);
v_AW_520_ = lean_ctor_get(v_K_517_, 5);
v_AL_521_ = lean_ctor_get(v_K_517_, 7);
v_CRm_522_ = lean_ctor_get(v_K_517_, 8);
lean_inc(v_CRm_522_);
lean_inc(v_AL_521_);
lean_inc(v_AW_520_);
lean_inc(v_Af_519_);
lean_inc(v_AG_518_);
v___x_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_523_, 0, v_AG_518_);
lean_ctor_set(v___x_523_, 1, v_Af_519_);
lean_ctor_set(v___x_523_, 2, v_AW_520_);
lean_ctor_set(v___x_523_, 3, v_AL_521_);
lean_ctor_set(v___x_523_, 4, v_CRm_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_KAdm_deg___boxed(lean_object* v_K_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = lp_tree_Formalism_MainNotions_WeightAlgebra_KAdm_deg(v_K_524_);
lean_dec_ref(v_K_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_n0(lean_object* v_D_526_, lean_object* v_j_527_){
_start:
{
lean_object* v_R_528_; lean_object* v___x_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_R_528_ = lean_ctor_get(v_D_526_, 0);
v___x_529_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_528_, v_j_527_);
v_fst_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_fst_530_);
v_snd_531_ = lean_ctor_get(v___x_529_, 1);
lean_inc(v_snd_531_);
lean_dec_ref(v___x_529_);
v___x_532_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_528_);
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = lp_tree_Formalism_MainNotions_WeightAlgebra_g0(v_D_526_);
v___x_535_ = lean_nat_mul(v___x_533_, v___x_534_);
lean_dec(v___x_534_);
v___x_536_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_528_);
v___x_537_ = lean_nat_mul(v___x_536_, v_fst_530_);
lean_dec(v_fst_530_);
lean_dec(v___x_536_);
v___x_538_ = lean_nat_mul(v___x_537_, v_snd_531_);
lean_dec(v_snd_531_);
lean_dec(v___x_537_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v___x_538_, v___x_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_nat_mul(v___x_535_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v___x_535_);
v___x_542_ = lean_nat_add(v___x_532_, v___x_541_);
lean_dec(v___x_541_);
lean_dec(v___x_532_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_n0___boxed(lean_object* v_D_543_, lean_object* v_j_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = lp_tree_Formalism_MainNotions_WeightAlgebra_n0(v_D_543_, v_j_544_);
lean_dec(v_j_544_);
lean_dec_ref(v_D_543_);
return v_res_545_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__0(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(72u);
v___x_547_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__1(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(5u);
v___x_549_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__2(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__1, &lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__1_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__1);
v___x_551_ = lean_unsigned_to_nat(4u);
v___x_552_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___f_555_; 
v___x_553_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__2, &lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__2_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__2);
v___x_554_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__0, &lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__0_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__0);
v___f_555_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_555_, 0, v___x_554_);
lean_closure_set(v___f_555_, 1, v___x_553_);
return v___f_555_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant(lean_object* v_D_556_, lean_object* v_j_557_){
_start:
{
lean_object* v_R_558_; lean_object* v_m_559_; lean_object* v___x_560_; lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___f_577_; 
v_R_558_ = lean_ctor_get(v_D_556_, 0);
lean_inc_ref(v_R_558_);
v_m_559_ = lean_ctor_get(v_R_558_, 2);
lean_inc(v_m_559_);
v___x_560_ = lean_unsigned_to_nat(4u);
v___f_561_ = lean_obj_once(&lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__3, &lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__3_once, _init_lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___closed__3);
v___x_562_ = lp_tree_Formalism_MainNotions_WeightFamilies_dimY(v_D_556_, v_j_557_);
lean_dec_ref(v_D_556_);
v___x_563_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_562_);
v___x_564_ = lean_unsigned_to_nat(2u);
v___x_565_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_564_, v___x_563_);
v___f_566_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_566_, 0, v___f_561_);
lean_closure_set(v___f_566_, 1, v___x_565_);
v___x_567_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_558_);
v___x_568_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_567_);
v___x_569_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_564_, v___x_568_);
v___f_570_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_570_, 0, v___f_566_);
lean_closure_set(v___f_570_, 1, v___x_569_);
v___x_571_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_558_);
lean_dec_ref(v_R_558_);
v___x_572_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_571_);
v___x_573_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_564_, v___x_572_);
v___f_574_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_574_, 0, v___f_570_);
lean_closure_set(v___f_574_, 1, v___x_573_);
v___x_575_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_m_559_);
v___x_576_ = lp_mathlib_npowRec___at___00Cardinal_cantorFunctionAux_spec__0(v___x_560_, v___x_575_);
v___f_577_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_577_, 0, v___f_574_);
lean_closure_set(v___f_577_, 1, v___x_576_);
return v___f_577_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant___boxed(lean_object* v_D_578_, lean_object* v_j_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = lp_tree_Formalism_MainNotions_WeightAlgebra_DivisibilityWeightConstant(v_D_578_, v_j_579_);
lean_dec(v_j_579_);
return v_res_580_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightFamilies(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightAlgebra(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_WeightFamilies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_ModuliIntegralCharts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
