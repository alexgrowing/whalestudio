// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.DataDIV public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.DataKap public import Formalism.SharpRestriction.ParamsHeightRankConstant
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_DV_kapW(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lp_mathlib_abs___at___00BoundingSieve_errSum_spec__0(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
static lean_once_cell_t lp_tree_Formalism_MainNotions_placeRankTwoOne_pS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_pS___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_pS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_qS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_NN(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_NN___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_placeRankTwoOne_idOf_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_placeRankTwoOne_idOf_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_dimY(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_dimY___boxed(lean_object*);
static lean_object* _init_lp_tree_Formalism_MainNotions_placeRankTwoOne_pS___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___f_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_2_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_2_, 0, v___x_1_);
return v___f_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_pS(lean_object* v_D_3_, lean_object* v_j_4_){
_start:
{
lean_object* v_R_5_; lean_object* v_k_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___f_11_; 
v_R_5_ = lean_ctor_get(v_D_3_, 0);
lean_inc_ref(v_R_5_);
lean_dec_ref(v_D_3_);
v_k_6_ = lean_ctor_get(v_R_5_, 1);
lean_inc(v_k_6_);
lean_dec_ref(v_R_5_);
v___x_7_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_k_6_);
v___x_8_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_j_4_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___x_7_);
lean_closure_set(v___f_9_, 1, v___x_8_);
v___f_10_ = lean_obj_once(&lp_tree_Formalism_MainNotions_placeRankTwoOne_pS___closed__0, &lp_tree_Formalism_MainNotions_placeRankTwoOne_pS___closed__0_once, _init_lp_tree_Formalism_MainNotions_placeRankTwoOne_pS___closed__0);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v___f_9_);
lean_closure_set(v___f_11_, 1, v___f_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_qS(lean_object* v_D_12_, lean_object* v_j_13_){
_start:
{
lean_object* v_R_14_; lean_object* v_m_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___f_18_; lean_object* v___f_19_; 
v_R_14_ = lean_ctor_get(v_D_12_, 0);
lean_inc_ref(v_R_14_);
lean_dec_ref(v_D_12_);
v_m_15_ = lean_ctor_get(v_R_14_, 2);
lean_inc(v_m_15_);
lean_dec_ref(v_R_14_);
v___x_16_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_m_15_);
v___x_17_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v_j_13_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_18_, 0, v___x_17_);
v___f_19_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_19_, 0, v___x_16_);
lean_closure_set(v___f_19_, 1, v___f_18_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_NN(lean_object* v_D_20_){
_start:
{
lean_object* v_R_21_; lean_object* v_m_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_R_21_ = lean_ctor_get(v_D_20_, 0);
v_m_22_ = lean_ctor_get(v_R_21_, 2);
v___x_23_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_21_, v_m_22_);
v___x_24_ = lp_mathlib_Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00Nat_cast___at___00__private_Mathlib_NumberTheory_ModularForms_EisensteinSeries_E2_Transform_0__EisensteinSeries_00_u03b4_spec__0_spec__0_spec__2_spec__3(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_NN___boxed(lean_object* v_D_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_tree_Formalism_MainNotions_placeRankTwoOne_NN(v_D_25_);
lean_dec_ref(v_D_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__0(lean_object* v_D_27_, lean_object* v_j_28_, lean_object* v_00_u03c4_29_, lean_object* v_w_30_, lean_object* v_i_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___x_38_; 
lean_inc(v_00_u03c4_29_);
v___x_32_ = lp_tree_Formalism_BasicNotions_DV_kapW(v_D_27_, v_j_28_, v_00_u03c4_29_, v_i_31_);
v___x_33_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_32_);
v___x_34_ = lean_apply_1(v_w_30_, v_00_u03c4_29_);
v___x_35_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_34_);
v___f_36_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_36_, 0, v___x_35_);
v___f_37_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_37_, 0, v___x_33_);
lean_closure_set(v___f_37_, 1, v___f_36_);
v___x_38_ = lp_mathlib_abs___at___00BoundingSieve_errSum_spec__0(v___f_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__1(lean_object* v_D_39_, lean_object* v_j_40_, lean_object* v_w_41_, lean_object* v_R_42_, lean_object* v_00_u03c4_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_44_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__0), 5, 4);
lean_closure_set(v___f_44_, 0, v_D_39_);
lean_closure_set(v___f_44_, 1, v_j_40_);
lean_closure_set(v___f_44_, 2, v_00_u03c4_43_);
lean_closure_set(v___f_44_, 3, v_w_41_);
v___x_45_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_42_);
v___x_46_ = l_List_finRange(v___x_45_);
v___x_47_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_46_, v___f_44_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__1___boxed(lean_object* v_D_48_, lean_object* v_j_49_, lean_object* v_w_50_, lean_object* v_R_51_, lean_object* v_00_u03c4_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__1(v_D_48_, v_j_49_, v_w_50_, v_R_51_, v_00_u03c4_52_);
lean_dec_ref(v_R_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_normU(lean_object* v_D_54_, lean_object* v_j_55_, lean_object* v_w_56_){
_start:
{
lean_object* v_what_u2082_57_; lean_object* v_R_58_; lean_object* v_instTau_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
v_what_u2082_57_ = lean_ctor_get(v_D_54_, 4);
v_R_58_ = lean_ctor_get(v_D_54_, 0);
lean_inc_ref(v_R_58_);
v_instTau_59_ = lean_ctor_get(v_what_u2082_57_, 5);
lean_inc(v_instTau_59_);
v___f_60_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_placeRankTwoOne_normU___lam__1___boxed), 5, 4);
lean_closure_set(v___f_60_, 0, v_D_54_);
lean_closure_set(v___f_60_, 1, v_j_55_);
lean_closure_set(v___f_60_, 2, v_w_56_);
lean_closure_set(v___f_60_, 3, v_R_58_);
v___x_61_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v_instTau_59_, v___f_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_placeRankTwoOne_idOf_spec__0(lean_object* v___x_62_, lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_placeRankTwoOne_idOf_spec__0___boxed(lean_object* v___x_65_, lean_object* v_s_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_tree_Submodule_span___at___00Formalism_MainNotions_placeRankTwoOne_idOf_spec__0(v___x_65_, v_s_66_);
lean_dec_ref(v___x_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___redArg(lean_object* v_D_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___redArg___boxed(lean_object* v_D_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___redArg(v_D_70_);
lean_dec_ref(v_D_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf(lean_object* v_D_72_, lean_object* v_00_u03c4_73_, lean_object* v_I_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf___boxed(lean_object* v_D_76_, lean_object* v_00_u03c4_77_, lean_object* v_I_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_tree_Formalism_MainNotions_placeRankTwoOne_idOf(v_D_76_, v_00_u03c4_77_, v_I_78_);
lean_dec(v_00_u03c4_77_);
lean_dec_ref(v_D_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idMul(lean_object* v_K_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_V_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_I_87_, lean_object* v_M_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_idMul___boxed(lean_object* v_K_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_V_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_I_97_, lean_object* v_M_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_tree_Formalism_MainNotions_placeRankTwoOne_idMul(v_K_90_, v_inst_91_, v_inst_92_, v_V_93_, v_inst_94_, v_inst_95_, v_inst_96_, v_I_97_, v_M_98_);
lean_dec(v_inst_96_);
lean_dec(v_inst_95_);
lean_dec_ref(v_inst_94_);
lean_dec_ref(v_inst_91_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_dimY(lean_object* v_D_100_){
_start:
{
lean_object* v_R_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_R_101_ = lean_ctor_get(v_D_100_, 0);
v___x_102_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_101_);
v___x_103_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_101_);
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lp_mathlib_Nat_fast__choose(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_nat_mul(v___x_102_, v___x_105_);
lean_dec(v___x_105_);
lean_dec(v___x_102_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_placeRankTwoOne_dimY___boxed(lean_object* v_D_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_MainNotions_placeRankTwoOne_dimY(v_D_107_);
lean_dec_ref(v_D_107_);
return v_res_108_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataKap(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_PlaceRankTwoOne(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataKap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParamsHeightRankConstant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
