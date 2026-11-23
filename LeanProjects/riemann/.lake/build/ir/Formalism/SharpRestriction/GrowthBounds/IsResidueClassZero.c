// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataGatTies public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting public import Formalism.SharpRestriction.GrowthBounds.DataG public import Formalism.SharpRestriction.GrowthBounds.DataGChain
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_tau1___redArg(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_tau2___redArg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_bind___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_rec___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_map___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___at___00Behrend_box_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_SizeData_u2082_lifts(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_hG___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_hG___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_hG___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_hG___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_hG(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_cG___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_cG___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cG(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cG___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Nm(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Nm___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fill___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fill___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_al___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_al(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_al___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_box___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_box___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___closed__0 = (const lean_object*)&lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_box(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_boxLoc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_boxLoc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_boxLoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_aL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_bL(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plGG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plGG(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plGG___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lowFE___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lowFE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lowFE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_MainNotions_G_hG___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_G_hG___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(8u);
v___x_4_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_hG(lean_object* v_s_5_){
_start:
{
lean_object* v_eps_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___f_10_; 
v_eps_6_ = lean_ctor_get(v_s_5_, 1);
lean_inc(v_eps_6_);
lean_dec_ref(v_s_5_);
v___x_7_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_hG___closed__0, &lp_tree_Formalism_MainNotions_G_hG___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_hG___closed__0);
v___x_8_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_hG___closed__1, &lp_tree_Formalism_MainNotions_G_hG___closed__1_once, _init_lp_tree_Formalism_MainNotions_G_hG___closed__1);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___x_8_);
lean_closure_set(v___f_9_, 1, v_eps_6_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_7_);
lean_closure_set(v___f_10_, 1, v___f_9_);
return v___f_10_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_G_cG___redArg___closed__0(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(4u);
v___x_12_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cG___redArg(lean_object* v_L_13_){
_start:
{
lean_object* v_Sc_14_; lean_object* v___x_15_; lean_object* v___f_16_; 
v_Sc_14_ = lean_ctor_get(v_L_13_, 14);
lean_inc(v_Sc_14_);
lean_dec_ref(v_L_13_);
v___x_15_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_cG___redArg___closed__0, &lp_tree_Formalism_MainNotions_G_cG___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_cG___redArg___closed__0);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_16_, 0, v___x_15_);
lean_closure_set(v___f_16_, 1, v_Sc_14_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cG(lean_object* v_D_17_, lean_object* v_L_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_tree_Formalism_MainNotions_G_cG___redArg(v_L_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_cG___boxed(lean_object* v_D_20_, lean_object* v_L_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_MainNotions_G_cG(v_D_20_, v_L_21_);
lean_dec_ref(v_D_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Nm(lean_object* v_D_23_){
_start:
{
lean_object* v_R_24_; lean_object* v_m_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_R_24_ = lean_ctor_get(v_D_23_, 0);
v_m_25_ = lean_ctor_get(v_R_24_, 2);
v___x_26_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_24_, v_m_25_);
v___x_27_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Nm___boxed(lean_object* v_D_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_MainNotions_G_Nm(v_D_28_);
lean_dec_ref(v_D_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fill___redArg(lean_object* v_D_30_, lean_object* v_X_31_, lean_object* v_b_32_, lean_object* v_j_33_, lean_object* v_z_34_){
_start:
{
lean_object* v___y_36_; lean_object* v_fst_42_; uint8_t v___x_43_; 
v_fst_42_ = lean_ctor_get(v_z_34_, 0);
v___x_43_ = lean_unbox(v_fst_42_);
if (v___x_43_ == 0)
{
lean_object* v_R_44_; lean_object* v_host_45_; lean_object* v_snd_46_; lean_object* v_toFrame_47_; lean_object* v_TT_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_R_44_ = lean_ctor_get(v_D_30_, 0);
lean_inc_ref(v_R_44_);
v_host_45_ = lean_ctor_get(v_D_30_, 1);
lean_inc_ref(v_host_45_);
lean_dec_ref(v_D_30_);
v_snd_46_ = lean_ctor_get(v_z_34_, 1);
v_toFrame_47_ = lean_ctor_get(v_R_44_, 0);
lean_inc_ref(v_toFrame_47_);
lean_dec_ref(v_R_44_);
v_TT_48_ = lean_ctor_get(v_host_45_, 10);
lean_inc(v_TT_48_);
lean_dec_ref(v_host_45_);
v___x_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_49_, 0, v_toFrame_47_);
lean_inc(v_snd_46_);
v___x_50_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_49_, v_snd_46_, v_TT_48_);
if (v___x_50_ == 0)
{
lean_dec_ref(v_b_32_);
goto v___jp_40_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_inc(v_snd_46_);
v___x_51_ = lean_apply_1(v_b_32_, v_snd_46_);
v___x_52_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_51_);
v___y_36_ = v___x_52_;
goto v___jp_35_;
}
}
else
{
lean_dec_ref(v_b_32_);
lean_dec_ref(v_D_30_);
goto v___jp_40_;
}
v___jp_35_:
{
lean_object* v_off_37_; lean_object* v___x_38_; lean_object* v___f_39_; 
v_off_37_ = lean_ctor_get(v_X_31_, 1);
lean_inc(v_off_37_);
lean_dec_ref(v_X_31_);
v___x_38_ = lean_apply_2(v_off_37_, v_j_33_, v_z_34_);
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_39_, 0, v___y_36_);
lean_closure_set(v___f_39_, 1, v___x_38_);
return v___f_39_;
}
v___jp_40_:
{
lean_object* v___x_41_; 
v___x_41_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_36_ = v___x_41_;
goto v___jp_35_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fill(lean_object* v_D_53_, lean_object* v_L_54_, lean_object* v_X_55_, lean_object* v_b_56_, lean_object* v_j_57_, lean_object* v_z_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_MainNotions_G_fill___redArg(v_D_53_, v_X_55_, v_b_56_, v_j_57_, v_z_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_fill___boxed(lean_object* v_D_60_, lean_object* v_L_61_, lean_object* v_X_62_, lean_object* v_b_63_, lean_object* v_j_64_, lean_object* v_z_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_MainNotions_G_fill(v_D_60_, v_L_61_, v_X_62_, v_b_63_, v_j_64_, v_z_65_);
lean_dec_ref(v_L_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_al___redArg(lean_object* v_L_67_, lean_object* v_a_68_, lean_object* v_s_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___f_76_; 
v___x_70_ = lean_apply_1(v_a_68_, v_s_69_);
v___x_71_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_70_);
v___x_72_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_hG___closed__0, &lp_tree_Formalism_MainNotions_G_hG___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_hG___closed__0);
v___x_73_ = lp_tree_Formalism_MainNotions_G_cG___redArg(v_L_67_);
v___f_74_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_74_, 0, v___x_72_);
lean_closure_set(v___f_74_, 1, v___x_73_);
v___f_75_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_75_, 0, v___f_74_);
v___f_76_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_76_, 0, v___x_71_);
lean_closure_set(v___f_76_, 1, v___f_75_);
return v___f_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_al(lean_object* v_D_77_, lean_object* v_L_78_, lean_object* v_a_79_, lean_object* v_s_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_tree_Formalism_MainNotions_G_al___redArg(v_L_78_, v_a_79_, v_s_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_al___boxed(lean_object* v_D_82_, lean_object* v_L_83_, lean_object* v_a_84_, lean_object* v_s_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_MainNotions_G_al(v_D_82_, v_L_83_, v_a_84_, v_s_85_);
lean_dec_ref(v_D_82_);
return v_res_86_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_nat_to_int(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_box(0);
v___x_90_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0, &lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0);
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_box___lam__0(lean_object* v_host_92_, lean_object* v___x_93_, lean_object* v_W_94_, lean_object* v_t_95_){
_start:
{
lean_object* v_TT_96_; uint8_t v___x_97_; 
v_TT_96_ = lean_ctor_get(v_host_92_, 10);
lean_inc(v_TT_96_);
lean_dec_ref(v_host_92_);
v___x_97_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_93_, v_t_95_, v_TT_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1, &lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1_once, _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1);
return v___x_98_;
}
else
{
lean_inc(v_W_94_);
return v_W_94_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_box___lam__0___boxed(lean_object* v_host_99_, lean_object* v___x_100_, lean_object* v_W_101_, lean_object* v_t_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_MainNotions_G_box___lam__0(v_host_99_, v___x_100_, v_W_101_, v_t_102_);
lean_dec(v_W_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__3(lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__3___boxed(lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__3(v___y_106_, v___y_107_);
lean_dec(v___y_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_109_, lean_object* v_b_110_, lean_object* v_f_111_, lean_object* v_a_x27_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lean_nat_dec_eq(v_a_x27_112_, v_a_109_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_apply_2(v_f_111_, v_a_x27_112_, lean_box(0));
return v___x_114_;
}
else
{
lean_dec(v_a_x27_112_);
lean_dec(v_f_111_);
lean_inc(v_b_110_);
return v_b_110_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_115_, lean_object* v_b_116_, lean_object* v_f_117_, lean_object* v_a_x27_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg(v_a_115_, v_b_116_, v_f_117_, v_a_x27_118_);
lean_dec(v_b_116_);
lean_dec(v_a_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_a_120_, lean_object* v_b_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg(v_a_120_, v_b_121_, v___y_122_, v___y_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_a_126_, lean_object* v_b_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__0(v_a_126_, v_b_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v_b_127_);
lean_dec(v_a_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__1(lean_object* v_a_132_, lean_object* v_p_133_, lean_object* v_b_134_){
_start:
{
lean_object* v___f_135_; lean_object* v___x_136_; 
v___f_135_ = lean_alloc_closure((void*)(lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_135_, 0, v_a_132_);
lean_closure_set(v___f_135_, 1, v_b_134_);
v___x_136_ = lp_mathlib_Multiset_map___redArg(v___f_135_, v_p_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__2(lean_object* v_t_137_, lean_object* v_a_138_, lean_object* v_m_139_, lean_object* v_p_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_inc(v_a_138_);
v___f_141_ = lean_alloc_closure((void*)(lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__1), 3, 2);
lean_closure_set(v___f_141_, 0, v_a_138_);
lean_closure_set(v___f_141_, 1, v_p_140_);
v___x_142_ = lean_apply_1(v_t_137_, v_a_138_);
v___x_143_ = lp_mathlib_Multiset_bind___redArg(v___x_142_, v___f_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__2___boxed(lean_object* v_t_144_, lean_object* v_a_145_, lean_object* v_m_146_, lean_object* v_p_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__2(v_t_144_, v_a_145_, v_m_146_, v_p_147_);
lean_dec(v_m_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg(lean_object* v___x_153_, lean_object* v_m_154_, lean_object* v_t_155_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___f_156_ = lean_alloc_closure((void*)(lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_156_, 0, v_t_155_);
v___x_157_ = ((lean_object*)(lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_158_ = lp_mathlib_Multiset_rec___redArg(v___x_157_, v___f_156_, v_m_154_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_159_, lean_object* v_m_160_, lean_object* v_t_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg(v___x_159_, v_m_160_, v_t_161_);
lean_dec_ref(v___x_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg___lam__0(lean_object* v_t_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_apply_1(v_t_163_, v_a_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg(lean_object* v___x_166_, lean_object* v_s_167_, lean_object* v_t_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; 
v___f_169_ = lean_alloc_closure((void*)(lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_169_, 0, v_t_168_);
v___x_170_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg(v___x_166_, v_s_167_, v___f_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg___boxed(lean_object* v___x_171_, lean_object* v_s_172_, lean_object* v_t_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg(v___x_171_, v_s_172_, v_t_173_);
lean_dec_ref(v___x_171_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___lam__0(lean_object* v_f_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_apply_2(v_f_175_, v_a_176_, lean_box(0));
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg(lean_object* v___x_179_, lean_object* v_t_180_){
_start:
{
lean_object* v_ord_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_ord_181_ = lean_ctor_get(v___x_179_, 1);
v___f_182_ = ((lean_object*)(lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg___closed__0));
lean_inc(v_ord_181_);
v___x_183_ = l_List_finRange(v_ord_181_);
v___x_184_ = lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg(v___x_179_, v___x_183_, v_t_180_);
lean_dec_ref(v___x_179_);
v___x_185_ = lp_mathlib_Finset_map___redArg(v___f_182_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_box(lean_object* v_D_186_, lean_object* v_W_187_){
_start:
{
lean_object* v_R_188_; lean_object* v_host_189_; lean_object* v_toFrame_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___x_193_; 
v_R_188_ = lean_ctor_get(v_D_186_, 0);
lean_inc_ref(v_R_188_);
v_host_189_ = lean_ctor_get(v_D_186_, 1);
lean_inc_ref(v_host_189_);
lean_dec_ref(v_D_186_);
v_toFrame_190_ = lean_ctor_get(v_R_188_, 0);
lean_inc_ref_n(v_toFrame_190_, 2);
lean_dec_ref(v_R_188_);
v___x_191_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_191_, 0, v_toFrame_190_);
v___f_192_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_box___lam__0___boxed), 4, 3);
lean_closure_set(v___f_192_, 0, v_host_189_);
lean_closure_set(v___f_192_, 1, v___x_191_);
lean_closure_set(v___f_192_, 2, v_W_187_);
v___x_193_ = lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg(v_toFrame_190_, v___f_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0(lean_object* v___x_194_, lean_object* v_00_u03b4_195_, lean_object* v_t_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lp_tree_Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0___redArg(v___x_194_, v_t_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0(lean_object* v___x_198_, lean_object* v_00_u03b2_199_, lean_object* v_s_200_, lean_object* v_t_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___redArg(v___x_198_, v_s_200_, v_t_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0___boxed(lean_object* v___x_203_, lean_object* v_00_u03b2_204_, lean_object* v_s_205_, lean_object* v_t_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = lp_tree_Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0(v___x_203_, v_00_u03b2_204_, v_s_205_, v_t_206_);
lean_dec_ref(v___x_203_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2(lean_object* v___x_208_, lean_object* v_00_u03b4_209_, lean_object* v_m_210_, lean_object* v_a_211_, lean_object* v_b_212_, lean_object* v_f_213_, lean_object* v_a_x27_214_, lean_object* v_ha_x27_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___redArg(v_a_211_, v_b_212_, v_f_213_, v_a_x27_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v___x_217_, lean_object* v_00_u03b4_218_, lean_object* v_m_219_, lean_object* v_a_220_, lean_object* v_b_221_, lean_object* v_f_222_, lean_object* v_a_x27_223_, lean_object* v_ha_x27_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = lp_tree_Multiset_Pi_cons___at___00Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1_spec__2(v___x_217_, v_00_u03b4_218_, v_m_219_, v_a_220_, v_b_221_, v_f_222_, v_a_x27_223_, v_ha_x27_224_);
lean_dec(v_b_221_);
lean_dec(v_a_220_);
lean_dec(v_m_219_);
lean_dec_ref(v___x_217_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1(lean_object* v___x_226_, lean_object* v_00_u03b2_227_, lean_object* v_m_228_, lean_object* v_t_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___redArg(v___x_226_, v_m_228_, v_t_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1___boxed(lean_object* v___x_231_, lean_object* v_00_u03b2_232_, lean_object* v_m_233_, lean_object* v_t_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = lp_tree_Multiset_pi___at___00Finset_pi___at___00Fintype_piFinset___at___00Formalism_MainNotions_G_box_spec__0_spec__0_spec__1(v___x_231_, v_00_u03b2_232_, v_m_233_, v_t_234_);
lean_dec_ref(v___x_231_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_boxLoc___lam__0(lean_object* v___x_236_, lean_object* v_TT_237_, lean_object* v_W_238_, lean_object* v_i_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_236_, v_i_239_, v_TT_237_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1, &lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1_once, _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__1);
return v___x_241_;
}
else
{
lean_inc(v_W_238_);
return v_W_238_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_boxLoc___lam__0___boxed(lean_object* v___x_242_, lean_object* v_TT_243_, lean_object* v_W_244_, lean_object* v_i_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = lp_tree_Formalism_MainNotions_G_boxLoc___lam__0(v___x_242_, v_TT_243_, v_W_244_, v_i_245_);
lean_dec(v_W_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_boxLoc(lean_object* v_n_x27_247_, lean_object* v_TT_248_, lean_object* v_W_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___f_251_; lean_object* v___x_252_; 
lean_inc(v_n_x27_247_);
v___x_250_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_250_, 0, v_n_x27_247_);
v___f_251_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_boxLoc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_251_, 0, v___x_250_);
lean_closure_set(v___f_251_, 1, v_TT_248_);
lean_closure_set(v___f_251_, 2, v_W_249_);
v___x_252_ = lp_mathlib_Fintype_piFinset___at___00Behrend_box_spec__0___redArg(v_n_x27_247_, v___f_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_aL(lean_object* v_D_253_, lean_object* v_L_254_, lean_object* v_t_255_){
_start:
{
lean_object* v_R_256_; lean_object* v_host_257_; lean_object* v_toFrame_258_; lean_object* v_TT_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_R_256_ = lean_ctor_get(v_D_253_, 0);
lean_inc_ref(v_R_256_);
v_host_257_ = lean_ctor_get(v_D_253_, 1);
lean_inc_ref(v_host_257_);
lean_dec_ref(v_D_253_);
v_toFrame_258_ = lean_ctor_get(v_R_256_, 0);
lean_inc_ref(v_toFrame_258_);
lean_dec_ref(v_R_256_);
v_TT_259_ = lean_ctor_get(v_host_257_, 10);
lean_inc(v_TT_259_);
lean_dec_ref(v_host_257_);
v___x_260_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_260_, 0, v_toFrame_258_);
lean_inc(v_t_255_);
v___x_261_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_260_, v_t_255_, v_TT_259_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec(v_t_255_);
lean_dec_ref(v_L_254_);
v___x_262_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0, &lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0);
return v___x_262_;
}
else
{
lean_object* v_aT_263_; lean_object* v___x_264_; 
v_aT_263_ = lean_ctor_get(v_L_254_, 1);
lean_inc_ref(v_aT_263_);
lean_dec_ref(v_L_254_);
v___x_264_ = lean_apply_1(v_aT_263_, v_t_255_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_bL(lean_object* v_D_265_, lean_object* v_L_266_, lean_object* v_t_267_){
_start:
{
lean_object* v_R_268_; lean_object* v_host_269_; lean_object* v_toFrame_270_; lean_object* v_TT_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_R_268_ = lean_ctor_get(v_D_265_, 0);
lean_inc_ref(v_R_268_);
v_host_269_ = lean_ctor_get(v_D_265_, 1);
lean_inc_ref(v_host_269_);
lean_dec_ref(v_D_265_);
v_toFrame_270_ = lean_ctor_get(v_R_268_, 0);
lean_inc_ref(v_toFrame_270_);
lean_dec_ref(v_R_268_);
v_TT_271_ = lean_ctor_get(v_host_269_, 10);
lean_inc(v_TT_271_);
lean_dec_ref(v_host_269_);
v___x_272_ = lean_alloc_closure((void*)(lp_tree_Formalism_HC_Frame_instDecidableEqA___boxed), 3, 1);
lean_closure_set(v___x_272_, 0, v_toFrame_270_);
lean_inc(v_t_267_);
v___x_273_ = lp_mathlib_Multiset_decidableMem___aux__1___redArg(v___x_272_, v_t_267_, v_TT_271_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_t_267_);
lean_dec_ref(v_L_266_);
v___x_274_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0, &lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0_once, _init_lp_tree_Formalism_MainNotions_G_box___lam__0___closed__0);
return v___x_274_;
}
else
{
lean_object* v_bT_275_; lean_object* v___x_276_; 
v_bT_275_ = lean_ctor_get(v_L_266_, 2);
lean_inc_ref(v_bT_275_);
lean_dec_ref(v_L_266_);
v___x_276_ = lean_apply_1(v_bT_275_, v_t_267_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plGG___redArg(lean_object* v_z_277_){
_start:
{
lean_object* v_fst_278_; uint8_t v___x_279_; 
v_fst_278_ = lean_ctor_get(v_z_277_, 0);
v___x_279_ = lean_unbox(v_fst_278_);
if (v___x_279_ == 0)
{
lean_object* v_snd_280_; lean_object* v___x_281_; 
v_snd_280_ = lean_ctor_get(v_z_277_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v_z_277_);
v___x_281_ = lp_tree_Formalism_HC_Frame_tau1___redArg(v_snd_280_);
return v___x_281_;
}
else
{
lean_object* v_snd_282_; lean_object* v___x_283_; 
v_snd_282_ = lean_ctor_get(v_z_277_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v_z_277_);
v___x_283_ = lp_tree_Formalism_HC_Frame_tau2___redArg(v_snd_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plGG(lean_object* v_D_284_, lean_object* v_z_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lp_tree_Formalism_MainNotions_G_plGG___redArg(v_z_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_plGG___boxed(lean_object* v_D_287_, lean_object* v_z_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_tree_Formalism_MainNotions_G_plGG(v_D_287_, v_z_288_);
lean_dec_ref(v_D_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lowFE___lam__0(lean_object* v_L_290_, lean_object* v_w_291_, lean_object* v_u_292_, lean_object* v_j_293_){
_start:
{
lean_object* v_F_294_; lean_object* v_E_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___f_299_; 
v_F_294_ = lean_ctor_get(v_L_290_, 5);
lean_inc(v_F_294_);
v_E_295_ = lean_ctor_get(v_L_290_, 6);
lean_inc(v_E_295_);
lean_dec_ref(v_L_290_);
lean_inc(v_w_291_);
lean_inc(v_j_293_);
v___x_296_ = lean_apply_2(v_F_294_, v_j_293_, v_w_291_);
v___x_297_ = lean_apply_3(v_E_295_, v_u_292_, v_j_293_, v_w_291_);
v___f_298_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_298_, 0, v___x_297_);
v___f_299_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_299_, 0, v___x_296_);
lean_closure_set(v___f_299_, 1, v___f_298_);
return v___f_299_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lowFE(lean_object* v_D_300_, lean_object* v_L_301_, lean_object* v_u_302_, lean_object* v_w_303_){
_start:
{
lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___f_304_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_lowFE___lam__0), 4, 3);
lean_closure_set(v___f_304_, 0, v_L_301_);
lean_closure_set(v___f_304_, 1, v_w_303_);
lean_closure_set(v___f_304_, 2, v_u_302_);
v___x_305_ = lp_tree_Formalism_BasicNotions_SizeData_u2082_lifts(v_D_300_);
v___x_306_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_305_, v___f_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lowFE___boxed(lean_object* v_D_307_, lean_object* v_L_308_, lean_object* v_u_309_, lean_object* v_w_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = lp_tree_Formalism_MainNotions_G_lowFE(v_D_307_, v_L_308_, v_u_309_, v_w_310_);
lean_dec_ref(v_D_307_);
return v_res_311_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataGatTies(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataGChain(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataGatTies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_DataGChain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
