// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.Divisibility.ZetaProductPairs public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan public import Formalism.SharpRestriction.Divisibility.JumpSets public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues public import Formalism.SharpRestriction.ParConsts public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature public import Formalism.SharpRestriction.ElevenLe public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow public import Formalism.LocalRingCardinality.DataBu public import Formalism.LocalRingCardinality.DataDIV public import Formalism.LocalRingCardinality.DataDIVDefs public import Formalism.LocalRingCardinality.DataErr public import Formalism.LocalRingCardinality.DataForced public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.LocalRingCardinality.PrincipalHermitianLattice public import Formalism.LocalRingCardinality.DataTheta public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension public import Formalism.LocalRingCardinality.Lemmas public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
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
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_tau1___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_padicValNat(lean_object*, lean_object*);
uint8_t l_Nat_decidableExistsFin___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_N(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_tauOfTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_sumA___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_sumA(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_WeightDegreeSizes_Lmu_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_WeightDegreeSizes_Lmu_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_LmuS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_LmuS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtZ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtZ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtDualZ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtDualZ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_tauOfTop(lean_object* v_D_1_, lean_object* v_t_2_){
_start:
{
lean_object* v_eTau_3_; lean_object* v___x_4_; lean_object* v_toFun_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_eTau_3_ = lean_ctor_get(v_D_1_, 5);
lean_inc_ref(v_eTau_3_);
lean_dec_ref(v_D_1_);
v___x_4_ = lp_mathlib_Equiv_symm___redArg(v_eTau_3_);
v_toFun_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toFun_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_tree_Formalism_HC_Frame_tau1___redArg(v_t_2_);
v___x_7_ = lean_apply_1(v_toFun_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_sumA___lam__0(lean_object* v_L_8_, lean_object* v_t_9_){
_start:
{
lean_object* v_aT_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_aT_10_ = lean_ctor_get(v_L_8_, 1);
lean_inc_ref(v_aT_10_);
lean_dec_ref(v_L_8_);
v___x_11_ = lean_apply_1(v_aT_10_, v_t_9_);
v___x_12_ = lp_mathlib_Int_cast___at___00Int_cast___at___00Int_cast___at___00Int_cast___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__0_spec__1_spec__4_spec__5(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_sumA(lean_object* v_D_13_, lean_object* v_L_14_){
_start:
{
lean_object* v_host_15_; lean_object* v_TT_16_; lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_host_15_ = lean_ctor_get(v_D_13_, 1);
lean_inc_ref(v_host_15_);
lean_dec_ref(v_D_13_);
v_TT_16_ = lean_ctor_get(v_host_15_, 10);
lean_inc(v_TT_16_);
lean_dec_ref(v_host_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightDegreeSizes_sumA___lam__0), 2, 1);
lean_closure_set(v___f_17_, 0, v_L_14_);
v___x_18_ = lp_mathlib_Multiset_attach___redArg(v_TT_16_);
v___x_19_ = lp_mathlib_Finset_sum___at___00BoundingSieve_multSum_spec__0___redArg(v___x_18_, v___f_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_WeightDegreeSizes_Lmu_spec__0(lean_object* v___x_20_, lean_object* v___x_21_, lean_object* v_s_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_box(0);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_span___at___00Formalism_MainNotions_WeightDegreeSizes_Lmu_spec__0___boxed(lean_object* v___x_24_, lean_object* v___x_25_, lean_object* v_s_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_tree_Submodule_span___at___00Formalism_MainNotions_WeightDegreeSizes_Lmu_spec__0(v___x_24_, v___x_25_, v_s_26_);
lean_dec_ref(v___x_25_);
lean_dec_ref(v___x_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___redArg(lean_object* v_D_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___redArg___boxed(lean_object* v_D_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___redArg(v_D_30_);
lean_dec_ref(v_D_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu(lean_object* v_D_32_, lean_object* v_00_u03bc_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu___boxed(lean_object* v_D_35_, lean_object* v_00_u03bc_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_Lmu(v_D_35_, v_00_u03bc_36_);
lean_dec(v_00_u03bc_36_);
lean_dec_ref(v_D_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_LmuS(lean_object* v_D_38_, lean_object* v_EE_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_S_43_, lean_object* v_00_u03bc_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_LmuS___boxed(lean_object* v_D_46_, lean_object* v_EE_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_S_51_, lean_object* v_00_u03bc_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_LmuS(v_D_46_, v_EE_47_, v_inst_48_, v_inst_49_, v_inst_50_, v_S_51_, v_00_u03bc_52_);
lean_dec(v_00_u03bc_52_);
lean_dec_ref(v_S_51_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_D_46_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtO(lean_object* v_D_54_, lean_object* v_00_u03bc_55_, lean_object* v_j_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtO___boxed(lean_object* v_D_58_, lean_object* v_00_u03bc_59_, lean_object* v_j_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtO(v_D_58_, v_00_u03bc_59_, v_j_60_);
lean_dec(v_j_60_);
lean_dec(v_00_u03bc_59_);
lean_dec_ref(v_D_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtZ(lean_object* v_D_62_, lean_object* v_00_u03bc_63_, lean_object* v_j_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtZ___boxed(lean_object* v_D_66_, lean_object* v_00_u03bc_67_, lean_object* v_j_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtZ(v_D_66_, v_00_u03bc_67_, v_j_68_);
lean_dec(v_j_68_);
lean_dec(v_00_u03bc_67_);
lean_dec_ref(v_D_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtDualZ(lean_object* v_D_70_, lean_object* v_00_u03bc_71_, lean_object* v_j_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtDualZ___boxed(lean_object* v_D_74_, lean_object* v_00_u03bc_75_, lean_object* v_j_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_MtDualZ(v_D_74_, v_00_u03bc_75_, v_j_76_);
lean_dec(v_j_76_);
lean_dec(v_00_u03bc_75_);
lean_dec_ref(v_D_74_);
return v_res_77_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp___lam__0(lean_object* v_host_78_, lean_object* v___x_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_g_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_g_81_ = lean_ctor_get(v_host_78_, 6);
lean_inc_ref(v_g_81_);
lean_dec_ref(v_host_78_);
v___x_82_ = lean_apply_1(v_g_81_, v_a_80_);
v___x_83_ = lean_nat_dec_eq(v___x_79_, v___x_82_);
lean_dec(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp___lam__0___boxed(lean_object* v_host_84_, lean_object* v___x_85_, lean_object* v_a_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp___lam__0(v_host_84_, v___x_85_, v_a_86_);
lean_dec(v___x_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp(lean_object* v_D_89_, lean_object* v_w_90_){
_start:
{
lean_object* v_what_u2082_91_; lean_object* v_places_92_; lean_object* v_R_93_; lean_object* v_host_94_; lean_object* v_u_u2080_95_; lean_object* v_mem_96_; lean_object* v_resChar_97_; lean_object* v___x_98_; lean_object* v_C_99_; lean_object* v_DGam_100_; lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_what_u2082_91_ = lean_ctor_get(v_D_89_, 4);
v_places_92_ = lean_ctor_get(v_what_u2082_91_, 2);
lean_inc_ref(v_places_92_);
v_R_93_ = lean_ctor_get(v_D_89_, 0);
lean_inc_ref(v_R_93_);
v_host_94_ = lean_ctor_get(v_D_89_, 1);
lean_inc_ref(v_host_94_);
v_u_u2080_95_ = lean_ctor_get(v_D_89_, 8);
lean_inc(v_u_u2080_95_);
v_mem_96_ = lean_ctor_get(v_D_89_, 10);
lean_inc_ref(v_mem_96_);
lean_dec_ref(v_D_89_);
v_resChar_97_ = lean_ctor_get(v_places_92_, 2);
lean_inc_ref(v_resChar_97_);
lean_dec_ref(v_places_92_);
v___x_98_ = lean_apply_1(v_mem_96_, v_u_u2080_95_);
v_C_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc_ref(v_C_99_);
lean_dec_ref(v___x_98_);
v_DGam_100_ = lean_ctor_get(v_C_99_, 2);
lean_inc(v_DGam_100_);
lean_dec_ref(v_C_99_);
v___x_101_ = lean_apply_1(v_resChar_97_, v_w_90_);
lean_inc(v___x_101_);
v___f_102_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_WeightDegreeSizes_dualExp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_102_, 0, v_host_94_);
lean_closure_set(v___f_102_, 1, v___x_101_);
v___x_103_ = lp_mathlib_padicValNat(v___x_101_, v_DGam_100_);
lean_dec(v___x_101_);
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = l_Nat_decidableExistsFin___redArg(v___x_104_, v___f_102_);
if (v___x_105_ == 0)
{
lean_dec_ref(v_R_93_);
return v___x_103_;
}
else
{
lean_object* v_m_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_m_106_ = lean_ctor_get(v_R_93_, 2);
lean_inc(v_m_106_);
v___x_107_ = lp_tree_Formalism_BasicNotions_Ranks_f(v_R_93_);
v___x_108_ = lean_nat_mul(v___x_104_, v___x_107_);
lean_dec(v___x_107_);
v___x_109_ = lp_tree_Formalism_BasicNotions_Ranks_N(v_R_93_, v_m_106_);
lean_dec(v_m_106_);
lean_dec_ref(v_R_93_);
v___x_110_ = lean_nat_pow(v___x_109_, v___x_104_);
lean_dec(v___x_109_);
v___x_111_ = lean_nat_mul(v___x_108_, v___x_110_);
lean_dec(v___x_110_);
lean_dec(v___x_108_);
v___x_112_ = lean_nat_add(v___x_103_, v___x_111_);
lean_dec(v___x_111_);
lean_dec(v___x_103_);
return v___x_112_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_ZetaProductPairs(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_InnerProductFormulaField(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_AbsolutelyIrreducibleSpan(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_JumpSets(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LiftErrorLocal(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_FamilyThetaDenominatorValues(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_WeilJacquetShalikaLaw(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_ProductFirstZerothParts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_CayleySignature(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ElevenLe(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataBu(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIV(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataErr(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForced(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataTheta(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Lemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_CoeNeZeroOfNotMem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_WeightDegreeSizes(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_Divisibility_ZetaProductPairs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_InnerProductFormulaField(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_AbsolutelyIrreducibleSpan(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_JumpSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LiftErrorLocal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_FamilyThetaDenominatorValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_WeilJacquetShalikaLaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_ProductFirstZerothParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_CayleySignature(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ElevenLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataBu(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataDIVDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataForced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataTheta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_RankBoundMonotoneInDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_CoeNeZeroOfNotMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
