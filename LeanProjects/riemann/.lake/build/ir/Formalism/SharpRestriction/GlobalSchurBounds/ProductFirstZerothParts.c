// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataLatDefs public import Formalism.LocalRingCardinality.DataErr public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.ParamsHeightRankConstant public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_pmap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0(lean_object*);
lean_object* lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Ow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Ow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wsum___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wsum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_tpow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_tpow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___lam__1(lean_object*);
static const lean_closure_object lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__0 = (const lean_object*)&lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__0_value;
static const lean_closure_object lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__1 = (const lean_object*)&lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__1_value;
static const lean_ctor_object lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__0_value),((lean_object*)&lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__1_value)}};
static const lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__2 = (const lean_object*)&lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__2_value;
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__3(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__0_value;
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__1 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1___redArg(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Gs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Gs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_GsD___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_GsD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_MramI(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_MramI___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_imgL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_imgL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Pt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_lamTr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_sgTr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Ow(lean_object* v_D_1_, lean_object* v_w_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Ow___boxed(lean_object* v_D_4_, lean_object* v_w_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Ow(v_D_4_, v_w_5_);
lean_dec(v_w_5_);
lean_dec_ref(v_D_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wsum___lam__0(lean_object* v_l_7_, lean_object* v_i_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_1(v_l_7_, v_i_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wsum(lean_object* v_n_10_, lean_object* v_l_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_12_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wsum___lam__0), 2, 1);
lean_closure_set(v___f_12_, 0, v_l_11_);
v___x_13_ = l_List_finRange(v_n_10_);
v___x_14_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_13_, v___f_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_tpow(lean_object* v_D_15_, lean_object* v_u_16_, lean_object* v_n_17_){
_start:
{
lean_object* v_mem_18_; lean_object* v___x_19_; lean_object* v_A_20_; lean_object* v_T_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_mem_18_ = lean_ctor_get(v_D_15_, 10);
lean_inc_ref(v_mem_18_);
lean_dec_ref(v_D_15_);
v___x_19_ = lean_apply_1(v_mem_18_, v_u_16_);
v_A_20_ = lean_ctor_get(v___x_19_, 1);
lean_inc_ref(v_A_20_);
lean_dec_ref(v___x_19_);
v_T_21_ = lean_ctor_get(v_A_20_, 0);
lean_inc(v_T_21_);
lean_dec_ref(v_A_20_);
v___x_22_ = lp_mathlib_Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0(v_T_21_);
v___x_23_ = lp_tree_npowRec___at___00Formalism_MainNotions_TaylorLogMetric_mono_spec__0(v_n_17_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_tpow___boxed(lean_object* v_D_24_, lean_object* v_u_25_, lean_object* v_n_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_tpow(v_D_24_, v_u_25_, v_n_26_);
lean_dec(v_n_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__0___lam__0(lean_object* v_i_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_apply_2(v___y_29_, v_i_28_, v___y_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__0(lean_object* v_i_32_){
_start:
{
lean_object* v___f_33_; 
v___f_33_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_33_, 0, v_i_32_);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__1___lam__0(lean_object* v_f_34_, lean_object* v_c_35_, lean_object* v_i_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_apply_3(v_f_34_, v_i_36_, v_c_35_, v___y_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__1(lean_object* v_f_39_){
_start:
{
lean_object* v___f_40_; 
v___f_40_ = lean_alloc_closure((void*)(lp_tree_LinearMap_pi___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__1___lam__0), 4, 1);
lean_closure_set(v___f_40_, 0, v_f_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia___lam__0(lean_object* v_D_41_, lean_object* v_u_42_, lean_object* v_i_43_, lean_object* v_v_44_, lean_object* v_a_45_, lean_object* v_c_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_fm_49_; lean_object* v___x_50_; lean_object* v_dil_51_; lean_object* v_dilT_52_; lean_object* v___x_53_; lean_object* v_toLinearMap_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___x_158__overap_57_; lean_object* v___x_58_; 
v_fm_49_ = lean_ctor_get(v_D_41_, 50);
lean_inc_ref(v_fm_49_);
lean_dec_ref(v_D_41_);
v___x_50_ = lean_apply_1(v_fm_49_, v_u_42_);
v_dil_51_ = lean_ctor_get(v___x_50_, 10);
lean_inc(v_dil_51_);
v_dilT_52_ = lean_ctor_get(v___x_50_, 11);
lean_inc_ref(v_dilT_52_);
lean_dec_ref(v___x_50_);
lean_inc(v_c_46_);
lean_inc_ref(v_a_45_);
lean_inc(v_v_44_);
lean_inc(v_i_43_);
v___x_53_ = lean_apply_4(v_dilT_52_, v_i_43_, v_v_44_, v_a_45_, v_c_46_);
v_toLinearMap_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_toLinearMap_54_);
lean_dec_ref(v___x_53_);
v___x_55_ = lean_apply_4(v_dil_51_, v_i_43_, v_v_44_, v_a_45_, v_c_46_);
v___f_56_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_56_, 0, v___x_55_);
v___x_158__overap_57_ = lp_mathlib_LinearMap_comp___redArg___lam__0(v___f_56_, v_toLinearMap_54_, v___y_47_);
v___x_58_ = lean_apply_1(v___x_158__overap_57_, v___y_48_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia(lean_object* v_D_59_, lean_object* v_u_60_, lean_object* v_i_61_, lean_object* v_v_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___f_65_; 
v___f_64_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia___lam__0), 8, 5);
lean_closure_set(v___f_64_, 0, v_D_59_);
lean_closure_set(v___f_64_, 1, v_u_60_);
lean_closure_set(v___f_64_, 2, v_i_61_);
lean_closure_set(v___f_64_, 3, v_v_62_);
lean_closure_set(v___f_64_, 4, v_a_63_);
v___f_65_ = lean_alloc_closure((void*)(lp_tree_LinearMap_pi___at___00Formalism_MainNotions_product__first__zeroth__parts_dia_spec__1___lam__0), 4, 1);
lean_closure_set(v___f_65_, 0, v___f_64_);
return v___f_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___lam__0(lean_object* v_u_66_){
_start:
{
lean_object* v_val_67_; lean_object* v_inv_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v_val_67_ = lean_ctor_get(v_u_66_, 0);
v_inv_68_ = lean_ctor_get(v_u_66_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_u_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_70_ = v_u_66_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_inv_68_);
lean_inc(v_val_67_);
lean_dec(v_u_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_val_67_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_inv_68_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___lam__1(lean_object* v_p_76_){
_start:
{
lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_fst_77_ = lean_ctor_get(v_p_76_, 0);
v_snd_78_ = lean_ctor_get(v_p_76_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_p_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v_p_76_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snd_78_);
lean_inc(v_fst_77_);
lean_dec(v_p_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_fst_77_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_snd_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0(lean_object* v___x_91_, lean_object* v_v_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = ((lean_object*)(lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___closed__2));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0___boxed(lean_object* v___x_94_, lean_object* v_v_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0(v___x_94_, v_v_95_);
lean_dec(v_v_95_);
lean_dec_ref(v___x_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__0(lean_object* v_val_97_, lean_object* v_property_98_){
_start:
{
lean_inc_ref(v_val_97_);
return v_val_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__0___boxed(lean_object* v_val_99_, lean_object* v_property_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__0(v_val_99_, v_property_100_);
lean_dec_ref(v_val_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__1(lean_object* v_D_102_, lean_object* v_u_103_, lean_object* v_i_104_, lean_object* v_v_105_, lean_object* v_a_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_1131__overap_110_; lean_object* v___x_111_; 
v___x_1131__overap_110_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia(v_D_102_, v_u_103_, v_i_104_, v_v_105_, v_a_106_);
v___x_111_ = lean_apply_3(v___x_1131__overap_110_, v___y_107_, v___y_108_, v___y_109_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2(lean_object* v_toMul_112_, lean_object* v_FvDec_113_, lean_object* v_v_114_, lean_object* v_toOne_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_fst_117_ = lean_ctor_get(v_a_116_, 0);
lean_inc_n(v_fst_117_, 2);
v_snd_118_ = lean_ctor_get(v_a_116_, 1);
lean_inc_n(v_snd_118_, 2);
lean_dec_ref(v_a_116_);
lean_inc(v_toMul_112_);
v___x_119_ = lean_apply_2(v_toMul_112_, v_fst_117_, v_snd_118_);
lean_inc_ref(v_FvDec_113_);
lean_inc(v_toOne_115_);
lean_inc(v_v_114_);
v___x_120_ = lean_apply_3(v_FvDec_113_, v_v_114_, v___x_119_, v_toOne_115_);
v___x_121_ = lean_unbox(v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
lean_dec(v_snd_118_);
lean_dec(v_fst_117_);
lean_dec(v_toOne_115_);
lean_dec(v_v_114_);
lean_dec_ref(v_FvDec_113_);
lean_dec(v_toMul_112_);
v___x_122_ = lean_unbox(v___x_120_);
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_apply_2(v_toMul_112_, v_snd_118_, v_fst_117_);
v___x_124_ = lean_apply_3(v_FvDec_113_, v_v_114_, v___x_123_, v_toOne_115_);
v___x_125_ = lean_unbox(v___x_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2___boxed(lean_object* v_toMul_126_, lean_object* v_FvDec_127_, lean_object* v_v_128_, lean_object* v_toOne_129_, lean_object* v_a_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2(v_toMul_126_, v_FvDec_127_, v_v_128_, v_toOne_129_, v_a_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__3(lean_object* v___x_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_toFun_135_; lean_object* v___x_136_; 
v_toFun_135_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_toFun_135_);
lean_dec_ref(v___x_133_);
v___x_136_ = lean_apply_1(v_toFun_135_, v___y_134_);
return v___x_136_;
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___closed__0(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_138_ = lp_mathlib_Complex_ofReal(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1(lean_object* v_x_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___closed__0, &lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___closed__0_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___closed__0);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1___boxed(lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__1(v_x_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v_x_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___lam__0(lean_object* v_x1_147_, lean_object* v_x2_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_152_; lean_object* v_re_153_; lean_object* v_im_154_; lean_object* v___x_155_; lean_object* v_re_156_; lean_object* v_im_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_166_; 
lean_inc(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_152_ = lean_apply_3(v_x1_147_, v___y_149_, v___y_150_, v___y_151_);
v_re_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_re_153_);
v_im_154_ = lean_ctor_get(v___x_152_, 1);
lean_inc(v_im_154_);
lean_dec_ref(v___x_152_);
v___x_155_ = lean_apply_3(v_x2_148_, v___y_149_, v___y_150_, v___y_151_);
v_re_156_ = lean_ctor_get(v___x_155_, 0);
v_im_157_ = lean_ctor_get(v___x_155_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_166_ == 0)
{
v___x_159_ = v___x_155_;
v_isShared_160_ = v_isSharedCheck_166_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_im_157_);
lean_inc(v_re_156_);
lean_dec(v___x_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_166_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_164_; 
v___f_161_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_161_, 0, v_re_153_);
lean_closure_set(v___f_161_, 1, v_re_156_);
v___f_162_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_162_, 0, v_im_154_);
lean_closure_set(v___f_162_, 1, v_im_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___f_162_);
lean_ctor_set(v___x_159_, 0, v___f_161_);
v___x_164_ = v___x_159_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___f_161_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___f_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1(lean_object* v_s_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_172_; 
v___f_170_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__0));
v___f_171_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1___closed__1));
v___x_172_ = l_List_foldrTR___redArg(v___f_170_, v___f_171_, v_s_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1___redArg(lean_object* v_s_173_, lean_object* v_f_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lp_mathlib_Multiset_map___redArg(v_f_174_, v_s_173_);
v___x_176_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1_spec__1(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm(lean_object* v_D_178_, lean_object* v_u_179_, lean_object* v_i_180_, lean_object* v_v_181_){
_start:
{
lean_object* v_mem_182_; lean_object* v___x_183_; lean_object* v_A_184_; lean_object* v_FvField_185_; lean_object* v_FvFin_186_; lean_object* v_FvDec_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_toSemiring_191_; lean_object* v_toMonoid_192_; lean_object* v___x_193_; lean_object* v_toOne_194_; lean_object* v_toMul_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_mem_182_ = lean_ctor_get(v_D_178_, 10);
lean_inc_ref(v_mem_182_);
lean_inc(v_u_179_);
v___x_183_ = lean_apply_1(v_mem_182_, v_u_179_);
v_A_184_ = lean_ctor_get(v___x_183_, 1);
lean_inc_ref(v_A_184_);
lean_dec_ref(v___x_183_);
v_FvField_185_ = lean_ctor_get(v_A_184_, 2);
v_FvFin_186_ = lean_ctor_get(v_A_184_, 3);
v_FvDec_187_ = lean_ctor_get(v_A_184_, 4);
lean_inc_ref(v_FvField_185_);
lean_inc_n(v_v_181_, 4);
v___x_188_ = lean_apply_1(v_FvField_185_, v_v_181_);
v___x_189_ = lp_mathlib_Field_toSemifield___redArg(v___x_188_);
lean_dec_ref(v___x_188_);
v___x_190_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_189_);
v_toSemiring_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc_ref(v_toSemiring_191_);
lean_dec_ref(v___x_190_);
v_toMonoid_192_ = lean_ctor_get(v_toSemiring_191_, 1);
lean_inc_ref(v_toMonoid_192_);
lean_dec_ref(v_toSemiring_191_);
v___x_193_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_192_);
lean_dec_ref(v_toMonoid_192_);
v_toOne_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_toOne_194_);
v_toMul_195_ = lean_ctor_get(v___x_193_, 1);
lean_inc(v_toMul_195_);
lean_dec_ref(v___x_193_);
v___f_196_ = ((lean_object*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___closed__0));
v___f_197_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__1), 8, 4);
lean_closure_set(v___f_197_, 0, v_D_178_);
lean_closure_set(v___f_197_, 1, v_u_179_);
lean_closure_set(v___f_197_, 2, v_i_180_);
lean_closure_set(v___f_197_, 3, v_v_181_);
lean_inc(v_FvFin_186_);
v___x_198_ = lean_apply_1(v_FvFin_186_, v_v_181_);
lean_inc_ref(v_FvDec_187_);
v___f_199_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2___boxed), 5, 4);
lean_closure_set(v___f_199_, 0, v_toMul_195_);
lean_closure_set(v___f_199_, 1, v_FvDec_187_);
lean_closure_set(v___f_199_, 2, v_v_181_);
lean_closure_set(v___f_199_, 3, v_toOne_194_);
v___x_200_ = lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0(v_A_184_, v_v_181_);
lean_dec(v_v_181_);
lean_dec_ref(v_A_184_);
v___x_201_ = lp_mathlib_Equiv_symm___redArg(v___x_200_);
v___f_202_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__3), 2, 1);
lean_closure_set(v___f_202_, 0, v___x_201_);
lean_inc(v___x_198_);
v___x_203_ = lp_mathlib_Multiset_product___redArg(v___x_198_, v___x_198_);
v___x_204_ = lp_mathlib_Multiset_filter___redArg(v___f_199_, v___x_203_);
v___x_205_ = lp_mathlib_Multiset_pmap___redArg(v___f_196_, v___x_204_);
v___x_206_ = lp_mathlib_Finset_map___redArg(v___f_202_, v___x_205_);
v___x_207_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1___redArg(v___x_206_, v___f_197_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1(lean_object* v_00_u03b9_208_, lean_object* v_s_209_, lean_object* v_f_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1___redArg(v_s_209_, v_f_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Gs___lam__1(lean_object* v_psiT_212_, lean_object* v_v_213_, lean_object* v_D_214_, lean_object* v_u_215_, lean_object* v_i_216_, lean_object* v_a_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_val_221_; lean_object* v___x_222_; lean_object* v_re_223_; lean_object* v_im_224_; lean_object* v___x_798__overap_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_val_221_ = lean_ctor_get(v_a_217_, 0);
lean_inc(v_val_221_);
lean_inc(v_v_213_);
v___x_222_ = lean_apply_2(v_psiT_212_, v_v_213_, v_val_221_);
v_re_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_re_223_);
v_im_224_ = lean_ctor_get(v___x_222_, 1);
lean_inc(v_im_224_);
lean_dec_ref(v___x_222_);
v___x_798__overap_225_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia(v_D_214_, v_u_215_, v_i_216_, v_v_213_, v_a_217_);
v___x_226_ = lean_apply_3(v___x_798__overap_225_, v___y_218_, v___y_219_, v___y_220_);
v___x_227_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_223_, v_im_224_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Gs(lean_object* v_D_228_, lean_object* v_u_229_, lean_object* v_i_230_, lean_object* v_v_231_){
_start:
{
lean_object* v_mem_232_; lean_object* v___x_233_; lean_object* v_A_234_; lean_object* v_FvField_235_; lean_object* v_FvFin_236_; lean_object* v_FvDec_237_; lean_object* v_psiT_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_toSemiring_242_; lean_object* v_toMonoid_243_; lean_object* v___x_244_; lean_object* v_toOne_245_; lean_object* v_toMul_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_mem_232_ = lean_ctor_get(v_D_228_, 10);
lean_inc_ref(v_mem_232_);
lean_inc(v_u_229_);
v___x_233_ = lean_apply_1(v_mem_232_, v_u_229_);
v_A_234_ = lean_ctor_get(v___x_233_, 1);
lean_inc_ref(v_A_234_);
lean_dec_ref(v___x_233_);
v_FvField_235_ = lean_ctor_get(v_A_234_, 2);
v_FvFin_236_ = lean_ctor_get(v_A_234_, 3);
v_FvDec_237_ = lean_ctor_get(v_A_234_, 4);
v_psiT_238_ = lean_ctor_get(v_A_234_, 5);
lean_inc_ref(v_FvField_235_);
lean_inc_n(v_v_231_, 4);
v___x_239_ = lean_apply_1(v_FvField_235_, v_v_231_);
v___x_240_ = lp_mathlib_Field_toSemifield___redArg(v___x_239_);
lean_dec_ref(v___x_239_);
v___x_241_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_240_);
v_toSemiring_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_toSemiring_242_);
lean_dec_ref(v___x_241_);
v_toMonoid_243_ = lean_ctor_get(v_toSemiring_242_, 1);
lean_inc_ref(v_toMonoid_243_);
lean_dec_ref(v_toSemiring_242_);
v___x_244_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_243_);
lean_dec_ref(v_toMonoid_243_);
v_toOne_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_toOne_245_);
v_toMul_246_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_toMul_246_);
lean_dec_ref(v___x_244_);
v___f_247_ = ((lean_object*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___closed__0));
lean_inc_ref(v_psiT_238_);
v___f_248_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Gs___lam__1), 9, 5);
lean_closure_set(v___f_248_, 0, v_psiT_238_);
lean_closure_set(v___f_248_, 1, v_v_231_);
lean_closure_set(v___f_248_, 2, v_D_228_);
lean_closure_set(v___f_248_, 3, v_u_229_);
lean_closure_set(v___f_248_, 4, v_i_230_);
lean_inc(v_FvFin_236_);
v___x_249_ = lean_apply_1(v_FvFin_236_, v_v_231_);
lean_inc_ref(v_FvDec_237_);
v___f_250_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2___boxed), 5, 4);
lean_closure_set(v___f_250_, 0, v_toMul_246_);
lean_closure_set(v___f_250_, 1, v_FvDec_237_);
lean_closure_set(v___f_250_, 2, v_v_231_);
lean_closure_set(v___f_250_, 3, v_toOne_245_);
v___x_251_ = lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0(v_A_234_, v_v_231_);
lean_dec(v_v_231_);
lean_dec_ref(v_A_234_);
v___x_252_ = lp_mathlib_Equiv_symm___redArg(v___x_251_);
v___f_253_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__3), 2, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
lean_inc(v___x_249_);
v___x_254_ = lp_mathlib_Multiset_product___redArg(v___x_249_, v___x_249_);
v___x_255_ = lp_mathlib_Multiset_filter___redArg(v___f_250_, v___x_254_);
v___x_256_ = lp_mathlib_Multiset_pmap___redArg(v___f_247_, v___x_255_);
v___x_257_ = lp_mathlib_Finset_map___redArg(v___f_253_, v___x_256_);
v___x_258_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1___redArg(v___x_257_, v___f_248_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_GsD___lam__3(lean_object* v_toNeg_259_, lean_object* v_psiT_260_, lean_object* v_v_261_, lean_object* v_D_262_, lean_object* v_u_263_, lean_object* v_i_264_, lean_object* v_a_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_val_269_; lean_object* v_inv_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_284_; 
v_val_269_ = lean_ctor_get(v_a_265_, 0);
v_inv_270_ = lean_ctor_get(v_a_265_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_284_ == 0)
{
v___x_272_ = v_a_265_;
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_inv_270_);
lean_inc(v_val_269_);
lean_dec(v_a_265_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_re_276_; lean_object* v_im_277_; lean_object* v___x_279_; 
lean_inc(v_val_269_);
v___x_274_ = lean_apply_1(v_toNeg_259_, v_val_269_);
lean_inc(v_v_261_);
v___x_275_ = lean_apply_2(v_psiT_260_, v_v_261_, v___x_274_);
v_re_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_re_276_);
v_im_277_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_im_277_);
lean_dec_ref(v___x_275_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v_val_269_);
lean_ctor_set(v___x_272_, 0, v_inv_270_);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_inv_270_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_val_269_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_1161__overap_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_1161__overap_280_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_dia(v_D_262_, v_u_263_, v_i_264_, v_v_261_, v___x_279_);
v___x_281_ = lean_apply_3(v___x_1161__overap_280_, v___y_266_, v___y_267_, v___y_268_);
v___x_282_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_276_, v_im_277_, v___x_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_GsD(lean_object* v_D_285_, lean_object* v_u_286_, lean_object* v_i_287_, lean_object* v_v_288_){
_start:
{
lean_object* v_mem_289_; lean_object* v___x_290_; lean_object* v_A_291_; lean_object* v_FvField_292_; lean_object* v_FvFin_293_; lean_object* v_FvDec_294_; lean_object* v_psiT_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_toSemiring_299_; lean_object* v_toMonoid_300_; lean_object* v___x_301_; lean_object* v_toOne_302_; lean_object* v_toMul_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_toRing_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_toNeg_310_; lean_object* v___f_311_; lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___x_320_; 
v_mem_289_ = lean_ctor_get(v_D_285_, 10);
lean_inc_ref(v_mem_289_);
lean_inc(v_u_286_);
v___x_290_ = lean_apply_1(v_mem_289_, v_u_286_);
v_A_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc_ref(v_A_291_);
lean_dec_ref(v___x_290_);
v_FvField_292_ = lean_ctor_get(v_A_291_, 2);
v_FvFin_293_ = lean_ctor_get(v_A_291_, 3);
v_FvDec_294_ = lean_ctor_get(v_A_291_, 4);
v_psiT_295_ = lean_ctor_get(v_A_291_, 5);
lean_inc_ref(v_psiT_295_);
lean_inc_ref(v_FvField_292_);
lean_inc_n(v_v_288_, 3);
v___x_296_ = lean_apply_1(v_FvField_292_, v_v_288_);
v___x_297_ = lp_mathlib_Field_toSemifield___redArg(v___x_296_);
v___x_298_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_297_);
v_toSemiring_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc_ref(v_toSemiring_299_);
lean_dec_ref(v___x_298_);
v_toMonoid_300_ = lean_ctor_get(v_toSemiring_299_, 1);
lean_inc_ref(v_toMonoid_300_);
lean_dec_ref(v_toSemiring_299_);
v___x_301_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_300_);
lean_dec_ref(v_toMonoid_300_);
v_toOne_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_toOne_302_);
v_toMul_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc(v_toMul_303_);
lean_dec_ref(v___x_301_);
lean_inc(v_FvFin_293_);
v___x_304_ = lean_apply_1(v_FvFin_293_, v_v_288_);
lean_inc(v___x_304_);
v___x_305_ = lp_mathlib_Multiset_product___redArg(v___x_304_, v___x_304_);
v___x_306_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_296_);
v_toRing_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_toRing_307_);
lean_dec_ref(v___x_306_);
v___x_308_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_toRing_307_);
lean_dec_ref(v_toRing_307_);
v___x_309_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_308_);
lean_dec_ref(v___x_308_);
v_toNeg_310_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_toNeg_310_);
lean_dec_ref(v___x_309_);
v___f_311_ = ((lean_object*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___closed__0));
lean_inc_ref(v_FvDec_294_);
v___f_312_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__2___boxed), 5, 4);
lean_closure_set(v___f_312_, 0, v_toMul_303_);
lean_closure_set(v___f_312_, 1, v_FvDec_294_);
lean_closure_set(v___f_312_, 2, v_v_288_);
lean_closure_set(v___f_312_, 3, v_toOne_302_);
v___x_313_ = lp_tree_unitsEquivProdSubtype___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__0(v_A_291_, v_v_288_);
lean_dec_ref(v_A_291_);
v___x_314_ = lp_mathlib_Equiv_symm___redArg(v___x_313_);
v___f_315_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Nm___lam__3), 2, 1);
lean_closure_set(v___f_315_, 0, v___x_314_);
v___x_316_ = lp_mathlib_Multiset_filter___redArg(v___f_312_, v___x_305_);
v___x_317_ = lp_mathlib_Multiset_pmap___redArg(v___f_311_, v___x_316_);
v___x_318_ = lp_mathlib_Finset_map___redArg(v___f_315_, v___x_317_);
v___f_319_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_GsD___lam__3), 10, 6);
lean_closure_set(v___f_319_, 0, v_toNeg_310_);
lean_closure_set(v___f_319_, 1, v_psiT_295_);
lean_closure_set(v___f_319_, 2, v_v_288_);
lean_closure_set(v___f_319_, 3, v_D_285_);
lean_closure_set(v___f_319_, 4, v_u_286_);
lean_closure_set(v___f_319_, 5, v_i_287_);
v___x_320_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_product__first__zeroth__parts_Nm_spec__1___redArg(v___x_318_, v___f_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_MramI(lean_object* v_D_321_, lean_object* v_u_322_, lean_object* v_i_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_box(0);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_MramI___boxed(lean_object* v_D_325_, lean_object* v_u_326_, lean_object* v_i_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_MramI(v_D_325_, v_u_326_, v_i_327_);
lean_dec(v_i_327_);
lean_dec(v_u_326_);
lean_dec_ref(v_D_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_imgL(lean_object* v_D_329_, lean_object* v_u_330_, lean_object* v_i_331_, lean_object* v_j_332_, lean_object* v_w_333_, lean_object* v_f_334_, lean_object* v_A_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_box(0);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_imgL___boxed(lean_object* v_D_337_, lean_object* v_u_338_, lean_object* v_i_339_, lean_object* v_j_340_, lean_object* v_w_341_, lean_object* v_f_342_, lean_object* v_A_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_imgL(v_D_337_, v_u_338_, v_i_339_, v_j_340_, v_w_341_, v_f_342_, v_A_343_);
lean_dec_ref(v_f_342_);
lean_dec(v_w_341_);
lean_dec(v_j_340_);
lean_dec(v_i_339_);
lean_dec(v_u_338_);
lean_dec_ref(v_D_337_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_Pt(lean_object* v_D_345_, lean_object* v_u_346_){
_start:
{
lean_object* v_mem_347_; lean_object* v___x_348_; lean_object* v_P_349_; lean_object* v_evz_350_; lean_object* v_lowerMap_351_; lean_object* v___f_352_; 
v_mem_347_ = lean_ctor_get(v_D_345_, 10);
lean_inc_ref(v_mem_347_);
lean_dec_ref(v_D_345_);
v___x_348_ = lean_apply_1(v_mem_347_, v_u_346_);
v_P_349_ = lean_ctor_get(v___x_348_, 2);
lean_inc_ref(v_P_349_);
lean_dec_ref(v___x_348_);
v_evz_350_ = lean_ctor_get(v_P_349_, 4);
lean_inc(v_evz_350_);
v_lowerMap_351_ = lean_ctor_get(v_P_349_, 7);
lean_inc(v_lowerMap_351_);
lean_dec_ref(v_P_349_);
v___f_352_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_352_, 0, v_evz_350_);
lean_closure_set(v___f_352_, 1, v_lowerMap_351_);
return v___f_352_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0(lean_object* v_l_353_, lean_object* v_c_354_, lean_object* v_i_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_apply_1(v_l_353_, v_i_355_);
v___x_357_ = lean_int_sub(v___x_356_, v_c_354_);
lean_dec(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0___boxed(lean_object* v_l_358_, lean_object* v_c_359_, lean_object* v_i_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0(v_l_358_, v_c_359_, v_i_360_);
lean_dec(v_c_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg(lean_object* v_l_362_, lean_object* v_c_363_){
_start:
{
lean_object* v___f_364_; 
v___f_364_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_364_, 0, v_l_362_);
lean_closure_set(v___f_364_, 1, v_c_363_);
return v___f_364_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh(lean_object* v_n_365_, lean_object* v_l_366_, lean_object* v_c_367_){
_start:
{
lean_object* v___f_368_; 
v___f_368_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_368_, 0, v_l_366_);
lean_closure_set(v___f_368_, 1, v_c_367_);
return v___f_368_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___boxed(lean_object* v_n_369_, lean_object* v_l_370_, lean_object* v_c_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh(v_n_369_, v_l_370_, v_c_371_);
lean_dec(v_n_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw(lean_object* v_R_373_){
_start:
{
lean_object* v_m_374_; lean_object* v_t_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_m_374_ = lean_ctor_get(v_R_373_, 2);
v_t_375_ = lean_ctor_get(v_R_373_, 3);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_t_375_, v___x_376_);
v___x_378_ = lean_nat_mul(v_m_374_, v___x_377_);
lean_dec(v___x_377_);
v___x_379_ = lean_nat_shiftr(v___x_378_, v___x_376_);
lean_dec(v___x_378_);
v___x_380_ = lean_nat_to_int(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw___boxed(lean_object* v_R_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw(v_R_381_);
lean_dec_ref(v_R_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_lamTr(lean_object* v_D_383_, lean_object* v_u_384_, lean_object* v_00_u03c4_385_){
_start:
{
lean_object* v_R_386_; lean_object* v_fm_387_; lean_object* v_m_388_; lean_object* v___x_389_; lean_object* v_lam_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___f_393_; 
v_R_386_ = lean_ctor_get(v_D_383_, 0);
lean_inc_ref(v_R_386_);
v_fm_387_ = lean_ctor_get(v_D_383_, 50);
lean_inc_ref(v_fm_387_);
lean_dec_ref(v_D_383_);
v_m_388_ = lean_ctor_get(v_R_386_, 2);
v___x_389_ = lean_apply_1(v_fm_387_, v_u_384_);
v_lam_390_ = lean_ctor_get(v___x_389_, 14);
lean_inc_ref(v_lam_390_);
lean_dec_ref(v___x_389_);
lean_inc(v_m_388_);
v___x_391_ = lean_apply_2(v_lam_390_, v_m_388_, v_00_u03c4_385_);
v___x_392_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw(v_R_386_);
lean_dec_ref(v_R_386_);
v___f_393_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_393_, 0, v___x_391_);
lean_closure_set(v___f_393_, 1, v___x_392_);
return v___f_393_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_product__first__zeroth__parts_sgTr(lean_object* v_D_394_, lean_object* v_u_395_, lean_object* v_00_u03c4_396_){
_start:
{
lean_object* v_R_397_; lean_object* v_fm_398_; lean_object* v___x_399_; lean_object* v_sg_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___f_403_; 
v_R_397_ = lean_ctor_get(v_D_394_, 0);
lean_inc_ref(v_R_397_);
v_fm_398_ = lean_ctor_get(v_D_394_, 50);
lean_inc_ref(v_fm_398_);
lean_dec_ref(v_D_394_);
v___x_399_ = lean_apply_1(v_fm_398_, v_u_395_);
v_sg_400_ = lean_ctor_get(v___x_399_, 15);
lean_inc_ref(v_sg_400_);
lean_dec_ref(v___x_399_);
v___x_401_ = lean_apply_1(v_sg_400_, v_00_u03c4_396_);
v___x_402_ = lp_tree_Formalism_MainNotions_product__first__zeroth__parts_cTw(v_R_397_);
lean_dec_ref(v_R_397_);
v___f_403_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_product__first__zeroth__parts_wSh___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_403_, 0, v___x_401_);
lean_closure_set(v___f_403_, 1, v___x_402_);
return v___f_403_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataLatDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataErr(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_TaylorLogMetric(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_PrimeDegreeVariant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_ProductFirstZerothParts(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataLatDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_TaylorLogMetric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_PrimeDegreeVariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
