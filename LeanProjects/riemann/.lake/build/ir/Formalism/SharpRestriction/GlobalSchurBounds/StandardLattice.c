// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataLevelD public import Formalism.LocalRingCardinality.DataTies public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigY0(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_pY(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_pY___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_qY(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_qY___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_uN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_vN(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_bN(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_pY(lean_object* v_D_1_){
_start:
{
lean_object* v_R_2_; lean_object* v___x_3_; lean_object* v_fst_4_; 
v_R_2_ = lean_ctor_get(v_D_1_, 0);
v___x_3_ = lp_tree_Formalism_BasicNotions_Ranks_sigY0(v_R_2_);
v_fst_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_fst_4_);
lean_dec_ref(v___x_3_);
return v_fst_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_pY___boxed(lean_object* v_D_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_MainNotions_StandardLattice_pY(v_D_5_);
lean_dec_ref(v_D_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_qY(lean_object* v_D_7_){
_start:
{
lean_object* v_R_8_; lean_object* v___x_9_; lean_object* v_snd_10_; 
v_R_8_ = lean_ctor_get(v_D_7_, 0);
v___x_9_ = lp_tree_Formalism_BasicNotions_Ranks_sigY0(v_R_8_);
v_snd_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_9_);
return v_snd_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_qY___boxed(lean_object* v_D_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_MainNotions_StandardLattice_qY(v_D_11_);
lean_dec_ref(v_D_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_uN(lean_object* v_D_13_, lean_object* v_u_14_, lean_object* v_00_u03c1_15_, lean_object* v_i_16_){
_start:
{
lean_object* v_R_17_; lean_object* v_hcW_18_; lean_object* v_k_19_; uint8_t v___x_20_; 
v_R_17_ = lean_ctor_get(v_D_13_, 0);
lean_inc_ref(v_R_17_);
v_hcW_18_ = lean_ctor_get(v_D_13_, 9);
lean_inc_ref(v_hcW_18_);
lean_dec_ref(v_D_13_);
v_k_19_ = lean_ctor_get(v_R_17_, 1);
lean_inc(v_k_19_);
lean_dec_ref(v_R_17_);
v___x_20_ = lean_nat_dec_lt(v_i_16_, v_k_19_);
lean_dec(v_k_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec_ref(v_hcW_18_);
lean_dec(v_i_16_);
lean_dec(v_00_u03c1_15_);
lean_dec(v_u_14_);
v___x_21_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v_u_23_; lean_object* v___x_24_; lean_object* v___f_25_; 
v___x_22_ = lean_apply_2(v_hcW_18_, v_u_14_, v_00_u03c1_15_);
v_u_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_u_23_);
lean_dec_ref(v___x_22_);
v___x_24_ = lean_apply_1(v_u_23_, v_i_16_);
v___f_25_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_25_, 0, v___x_24_);
return v___f_25_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_vN(lean_object* v_D_26_, lean_object* v_00_u03c1_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_R_29_; lean_object* v_hc_30_; lean_object* v_k_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_R_29_ = lean_ctor_get(v_D_26_, 0);
lean_inc_ref(v_R_29_);
v_hc_30_ = lean_ctor_get(v_D_26_, 6);
lean_inc_ref(v_hc_30_);
lean_dec_ref(v_D_26_);
v_k_31_ = lean_ctor_get(v_R_29_, 1);
lean_inc(v_k_31_);
lean_dec_ref(v_R_29_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_sub(v_k_31_, v___x_32_);
lean_dec(v_k_31_);
v___x_34_ = lean_nat_dec_lt(v_i_28_, v___x_33_);
lean_dec(v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec_ref(v_hc_30_);
lean_dec(v_i_28_);
lean_dec(v_00_u03c1_27_);
v___x_35_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v_v_37_; lean_object* v___x_38_; lean_object* v___f_39_; 
v___x_36_ = lean_apply_1(v_hc_30_, v_00_u03c1_27_);
v_v_37_ = lean_ctor_get(v___x_36_, 1);
lean_inc_ref(v_v_37_);
lean_dec_ref(v___x_36_);
v___x_38_ = lean_apply_1(v_v_37_, v_i_28_);
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_39_, 0, v___x_38_);
return v___f_39_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_StandardLattice_bN(lean_object* v_D_40_, lean_object* v_00_u03c1_41_, lean_object* v_j_42_){
_start:
{
lean_object* v_R_43_; lean_object* v_hc_44_; lean_object* v_m_45_; uint8_t v___x_46_; 
v_R_43_ = lean_ctor_get(v_D_40_, 0);
lean_inc_ref(v_R_43_);
v_hc_44_ = lean_ctor_get(v_D_40_, 6);
lean_inc_ref(v_hc_44_);
lean_dec_ref(v_D_40_);
v_m_45_ = lean_ctor_get(v_R_43_, 2);
lean_inc(v_m_45_);
lean_dec_ref(v_R_43_);
v___x_46_ = lean_nat_dec_lt(v_j_42_, v_m_45_);
lean_dec(v_m_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_dec_ref(v_hc_44_);
lean_dec(v_j_42_);
lean_dec(v_00_u03c1_41_);
v___x_47_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_47_;
}
else
{
lean_object* v___x_48_; lean_object* v_b_49_; lean_object* v___x_50_; lean_object* v___f_51_; 
v___x_48_ = lean_apply_1(v_hc_44_, v_00_u03c1_41_);
v_b_49_ = lean_ctor_get(v___x_48_, 2);
lean_inc_ref(v_b_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_apply_1(v_b_49_, v_j_42_);
v___f_51_ = lean_alloc_closure((void*)(lp_mathlib_Rat_cast___at___00Rat_cast___at___00rationalCauSeqPkg_spec__1_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_51_, 0, v___x_50_);
return v___f_51_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataLevelD(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataTies(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_RelevantZeroGramTerms(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GapAtLeast(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_StandardLattice(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_DataLevelD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataTies(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_RelevantZeroGramTerms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GapAtLeast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
