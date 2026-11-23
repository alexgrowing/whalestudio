// Lean compiler output
// Module: Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn public import Formalism.LocalRingCardinality.DataMink public import Formalism.CyclotomicNorms.StatementI public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow public import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_tameList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_tameList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_tameList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_setTu___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_setTu(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_setTu___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_tree_GlobalTheory_EX_DC_thrTu___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_tree_GlobalTheory_EX_DC_thrTu___lam__0___closed__0 = (const lean_object*)&lp_tree_GlobalTheory_EX_DC_thrTu___lam__0___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_thrTu___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_thrTu___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_thrTu(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_tameList___redArg(lean_object* v_g_1_, lean_object* v_00_u03c7_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toSemiring_5_; 
v___x_4_ = lp_mathlib_ZMod_commRing(v_g_1_);
v_toSemiring_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v___x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_toMonoid_6_; lean_object* v___x_7_; lean_object* v_toOne_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_15_; 
lean_dec_ref(v_00_u03c7_2_);
v_toMonoid_6_ = lean_ctor_get(v_toSemiring_5_, 1);
lean_inc_ref(v_toMonoid_6_);
lean_dec_ref(v_toSemiring_5_);
v___x_7_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_6_);
lean_dec_ref(v_toMonoid_6_);
v_toOne_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_15_ == 0)
{
lean_object* v_unused_16_; 
v_unused_16_ = lean_ctor_get(v___x_7_, 1);
lean_dec(v_unused_16_);
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_toOne_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
lean_inc(v_toOne_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v_toOne_8_);
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_toOne_8_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_toOne_8_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
else
{
lean_object* v_val_17_; lean_object* v_snd_18_; uint8_t v___x_19_; 
lean_dec_ref(v_toSemiring_5_);
v_val_17_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_x_3_, 1);
v_snd_18_ = lean_ctor_get(v_val_17_, 1);
v___x_19_ = lean_unbox(v_snd_18_);
if (v___x_19_ == 0)
{
lean_object* v_fst_20_; lean_object* v___x_21_; lean_object* v_val_22_; lean_object* v_inv_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_fst_20_ = lean_ctor_get(v_val_17_, 0);
lean_inc(v_fst_20_);
lean_dec(v_val_17_);
v___x_21_ = lean_apply_1(v_00_u03c7_2_, v_fst_20_);
v_val_22_ = lean_ctor_get(v___x_21_, 0);
v_inv_23_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_21_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_inv_23_);
lean_inc(v_val_22_);
lean_dec(v___x_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_val_22_);
lean_ctor_set(v___x_25_, 0, v_inv_23_);
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_inv_23_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_val_22_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_fst_31_; lean_object* v___x_32_; 
v_fst_31_ = lean_ctor_get(v_val_17_, 0);
lean_inc(v_fst_31_);
lean_dec(v_val_17_);
v___x_32_ = lean_apply_1(v_00_u03c7_2_, v_fst_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_tameList(lean_object* v_g_33_, lean_object* v_m_34_, lean_object* v_00_u03c7_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_tree_GlobalTheory_EX_DC_tameList___redArg(v_g_33_, v_00_u03c7_35_, v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_tameList___boxed(lean_object* v_g_38_, lean_object* v_m_39_, lean_object* v_00_u03c7_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_GlobalTheory_EX_DC_tameList(v_g_38_, v_m_39_, v_00_u03c7_40_, v_x_41_);
lean_dec(v_m_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_setTu___redArg(lean_object* v_Fm_43_, lean_object* v_t_44_){
_start:
{
lean_object* v_toFamCore_45_; lean_object* v_params_46_; lean_object* v_PK_47_; lean_object* v_parT_48_; lean_object* v_PT_49_; lean_object* v_gatT_50_; lean_object* v_X_51_; lean_object* v_Gx_52_; lean_object* v_Gy_53_; lean_object* v_GK_54_; lean_object* v_Csz_55_; lean_object* v_cX_56_; lean_object* v_ex_57_; lean_object* v_Cr_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_toFamCore_45_ = lean_ctor_get(v_Fm_43_, 0);
v_params_46_ = lean_ctor_get(v_Fm_43_, 1);
v_PK_47_ = lean_ctor_get(v_Fm_43_, 2);
v_parT_48_ = lean_ctor_get(v_Fm_43_, 3);
v_PT_49_ = lean_ctor_get(v_Fm_43_, 4);
v_gatT_50_ = lean_ctor_get(v_Fm_43_, 6);
v_X_51_ = lean_ctor_get(v_Fm_43_, 7);
v_Gx_52_ = lean_ctor_get(v_Fm_43_, 8);
v_Gy_53_ = lean_ctor_get(v_Fm_43_, 9);
v_GK_54_ = lean_ctor_get(v_Fm_43_, 10);
v_Csz_55_ = lean_ctor_get(v_Fm_43_, 11);
v_cX_56_ = lean_ctor_get(v_Fm_43_, 12);
v_ex_57_ = lean_ctor_get(v_Fm_43_, 13);
v_Cr_58_ = lean_ctor_get(v_Fm_43_, 14);
v_isSharedCheck_65_ = !lean_is_exclusive(v_Fm_43_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v_Fm_43_, 5);
lean_dec(v_unused_66_);
v___x_60_ = v_Fm_43_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_Cr_58_);
lean_inc(v_ex_57_);
lean_inc(v_cX_56_);
lean_inc(v_Csz_55_);
lean_inc(v_GK_54_);
lean_inc(v_Gy_53_);
lean_inc(v_Gx_52_);
lean_inc(v_X_51_);
lean_inc(v_gatT_50_);
lean_inc(v_PT_49_);
lean_inc(v_parT_48_);
lean_inc(v_PK_47_);
lean_inc(v_params_46_);
lean_inc(v_toFamCore_45_);
lean_dec(v_Fm_43_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 5, v_t_44_);
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_toFamCore_45_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_params_46_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_PK_47_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_parT_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_PT_49_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v_t_44_);
lean_ctor_set(v_reuseFailAlloc_64_, 6, v_gatT_50_);
lean_ctor_set(v_reuseFailAlloc_64_, 7, v_X_51_);
lean_ctor_set(v_reuseFailAlloc_64_, 8, v_Gx_52_);
lean_ctor_set(v_reuseFailAlloc_64_, 9, v_Gy_53_);
lean_ctor_set(v_reuseFailAlloc_64_, 10, v_GK_54_);
lean_ctor_set(v_reuseFailAlloc_64_, 11, v_Csz_55_);
lean_ctor_set(v_reuseFailAlloc_64_, 12, v_cX_56_);
lean_ctor_set(v_reuseFailAlloc_64_, 13, v_ex_57_);
lean_ctor_set(v_reuseFailAlloc_64_, 14, v_Cr_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_setTu(lean_object* v_eps_67_, lean_object* v_Fm_68_, lean_object* v_t_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lp_tree_GlobalTheory_EX_DC_setTu___redArg(v_Fm_68_, v_t_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_setTu___boxed(lean_object* v_eps_71_, lean_object* v_Fm_72_, lean_object* v_t_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_GlobalTheory_EX_DC_setTu(v_eps_71_, v_Fm_72_, v_t_73_);
lean_dec(v_eps_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_thrTu___lam__0(lean_object* v_t_77_, lean_object* v_mid_78_, lean_object* v_l_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(13u);
v___x_81_ = ((lean_object*)(lp_tree_GlobalTheory_EX_DC_thrTu___lam__0___closed__0));
lean_inc(v_l_79_);
v___x_82_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_79_, v_t_77_, v_l_79_, v___x_80_, v___x_81_);
lean_dec(v_l_79_);
v___x_83_ = lean_apply_1(v_mid_78_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_thrTu___lam__1(lean_object* v_t_84_, lean_object* v_last_85_, lean_object* v_l_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_unsigned_to_nat(13u);
v___x_88_ = ((lean_object*)(lp_tree_GlobalTheory_EX_DC_thrTu___lam__0___closed__0));
lean_inc(v_l_86_);
v___x_89_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_86_, v_t_84_, v_l_86_, v___x_87_, v___x_88_);
lean_dec(v_l_86_);
v___x_90_ = lean_apply_1(v_last_85_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_GlobalTheory_EX_DC_thrTu(lean_object* v_K_91_, lean_object* v_t_92_){
_start:
{
lean_object* v_pre_93_; lean_object* v_t_94_; lean_object* v_mid_95_; lean_object* v_last_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_105_; 
v_pre_93_ = lean_ctor_get(v_K_91_, 0);
v_t_94_ = lean_ctor_get(v_K_91_, 1);
v_mid_95_ = lean_ctor_get(v_K_91_, 2);
v_last_96_ = lean_ctor_get(v_K_91_, 3);
v_isSharedCheck_105_ = !lean_is_exclusive(v_K_91_);
if (v_isSharedCheck_105_ == 0)
{
v___x_98_ = v_K_91_;
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_last_96_);
lean_inc(v_mid_95_);
lean_inc(v_t_94_);
lean_inc(v_pre_93_);
lean_dec(v_K_91_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_103_; 
lean_inc(v_t_92_);
v___f_100_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_EX_DC_thrTu___lam__0), 3, 2);
lean_closure_set(v___f_100_, 0, v_t_92_);
lean_closure_set(v___f_100_, 1, v_mid_95_);
v___f_101_ = lean_alloc_closure((void*)(lp_tree_GlobalTheory_EX_DC_thrTu___lam__1), 3, 2);
lean_closure_set(v___f_101_, 0, v_t_92_);
lean_closure_set(v___f_101_, 1, v_last_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 3, v___f_101_);
lean_ctor_set(v___x_98_, 2, v___f_100_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_pre_93_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_t_94_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v___f_100_);
lean_ctor_set(v_reuseFailAlloc_104_, 3, v___f_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_MainIn(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataMink(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementI(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(uint8_t builtin);
lean_object* initialize_tree_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_TameGeneratorWindow(uint8_t builtin);
lean_object* initialize_tree_Development_AutomorphicArithmetic_PrimeDiscriminants_Scales(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_AuxiliaryPrimeMemAvoidedPrimes(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_InertJacobiLevels_AsmIface(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_GlobalTheory_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_SmallOrderPrimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LocalQuadraticParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_MainIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataMink(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_StatementI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_PairRowIffQdRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_DisjointExceptional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ThinScalesIffHostBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_TameGeneratorWindow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Development_AutomorphicArithmetic_PrimeDiscriminants_Scales(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
