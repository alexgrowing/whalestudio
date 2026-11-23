// Lean compiler output
// Module: Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
lean_object* lp_tree_Formalism_HC_Frame_iota___redArg(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_iotaInv___redArg(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_tree_Formalism_FrobeniusOrbits_cc(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_FrobeniusOrbits_chD(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_FrobeniusOrbits_chQ(lean_object*);
extern lean_object* lp_tree_Formalism_FrobeniusOrbits_c0;
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_Multiplicative_ofAdd(lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_cc(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ch(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ch___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ps(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ps___boxed(lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco___redArg(lean_object* v_g_1_){
_start:
{
lean_object* v_snd_2_; lean_object* v___x_3_; 
v_snd_2_ = lean_ctor_get(v_g_1_, 1);
lean_inc(v_snd_2_);
lean_dec_ref(v_g_1_);
v___x_3_ = lp_tree_Formalism_HC_Frame_iotaInv___redArg(v_snd_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco(lean_object* v_D_4_, lean_object* v_g_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco___redArg(v_g_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco___boxed(lean_object* v_D_7_, lean_object* v_g_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_hco(v_D_7_, v_g_8_);
lean_dec_ref(v_D_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf___redArg(lean_object* v_g_u2080_10_, lean_object* v_h_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lp_tree_Formalism_HC_Frame_iota___redArg(v_h_11_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v_g_u2080_10_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf(lean_object* v_D_14_, lean_object* v_g_u2080_15_, lean_object* v_h_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf___redArg(v_g_u2080_15_, v_h_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf___boxed(lean_object* v_D_18_, lean_object* v_g_u2080_19_, lean_object* v_h_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_gOf(v_D_18_, v_g_u2080_19_, v_h_20_);
lean_dec_ref(v_D_18_);
return v_res_21_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__0(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_22_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__1(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_mathlib_Multiplicative_ofAdd(lean_box(0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho(lean_object* v_D_24_, lean_object* v_00_u03c4_25_, lean_object* v_g_26_){
_start:
{
lean_object* v_R_27_; lean_object* v_toFrame_28_; lean_object* v_grp_29_; lean_object* v_toAddMonoid_30_; lean_object* v_toAddSemigroup_31_; lean_object* v___x_32_; lean_object* v_fst_33_; lean_object* v_fst_34_; lean_object* v_fst_35_; lean_object* v_fst_36_; lean_object* v_snd_37_; lean_object* v_snd_38_; lean_object* v_snd_39_; lean_object* v_snd_40_; lean_object* v_val_41_; lean_object* v_inv_42_; lean_object* v_val_43_; lean_object* v_inv_44_; lean_object* v_val_45_; lean_object* v_inv_46_; lean_object* v_val_47_; lean_object* v_inv_48_; lean_object* v___x_49_; lean_object* v_toFun_50_; lean_object* v___x_51_; lean_object* v_fst_52_; lean_object* v_fst_53_; lean_object* v_snd_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_105_; 
v_R_27_ = lean_ctor_get(v_D_24_, 0);
lean_inc_ref(v_R_27_);
lean_dec_ref(v_D_24_);
v_toFrame_28_ = lean_ctor_get(v_R_27_, 0);
lean_inc_ref(v_toFrame_28_);
lean_dec_ref(v_R_27_);
v_grp_29_ = lean_ctor_get(v_toFrame_28_, 2);
v_toAddMonoid_30_ = lean_ctor_get(v_grp_29_, 0);
v_toAddSemigroup_31_ = lean_ctor_get(v_toAddMonoid_30_, 0);
lean_inc(v_toAddSemigroup_31_);
v___x_32_ = lp_tree_Formalism_HC_Frame_cc(v_toFrame_28_);
lean_dec_ref(v_toFrame_28_);
v_fst_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_fst_33_);
v_fst_34_ = lean_ctor_get(v_g_26_, 0);
v_fst_35_ = lean_ctor_get(v_fst_33_, 0);
lean_inc(v_fst_35_);
v_fst_36_ = lean_ctor_get(v_fst_34_, 0);
lean_inc(v_fst_36_);
v_snd_37_ = lean_ctor_get(v_fst_33_, 1);
lean_inc(v_snd_37_);
lean_dec(v_fst_33_);
v_snd_38_ = lean_ctor_get(v_fst_34_, 1);
lean_inc(v_snd_38_);
v_snd_39_ = lean_ctor_get(v___x_32_, 1);
lean_inc(v_snd_39_);
lean_dec_ref(v___x_32_);
v_snd_40_ = lean_ctor_get(v_g_26_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v_g_26_);
v_val_41_ = lean_ctor_get(v_fst_35_, 0);
lean_inc(v_val_41_);
v_inv_42_ = lean_ctor_get(v_fst_35_, 1);
lean_inc(v_inv_42_);
lean_dec(v_fst_35_);
v_val_43_ = lean_ctor_get(v_fst_36_, 0);
lean_inc(v_val_43_);
v_inv_44_ = lean_ctor_get(v_fst_36_, 1);
lean_inc(v_inv_44_);
lean_dec(v_fst_36_);
v_val_45_ = lean_ctor_get(v_snd_37_, 0);
lean_inc(v_val_45_);
v_inv_46_ = lean_ctor_get(v_snd_37_, 1);
lean_inc(v_inv_46_);
lean_dec(v_snd_37_);
v_val_47_ = lean_ctor_get(v_snd_38_, 0);
lean_inc(v_val_47_);
v_inv_48_ = lean_ctor_get(v_snd_38_, 1);
lean_inc(v_inv_48_);
lean_dec(v_snd_38_);
v___x_49_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__0);
v_toFun_50_ = lean_ctor_get(v___x_49_, 0);
v___x_51_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__1, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__1_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_rho___closed__1);
v_fst_52_ = lean_ctor_get(v_00_u03c4_25_, 0);
lean_inc(v_fst_52_);
v_fst_53_ = lean_ctor_get(v_fst_52_, 0);
v_snd_54_ = lean_ctor_get(v_fst_52_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_fst_52_);
if (v_isSharedCheck_105_ == 0)
{
v___x_56_ = v_fst_52_;
v_isShared_57_ = v_isSharedCheck_105_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_snd_54_);
lean_inc(v_fst_53_);
lean_dec(v_fst_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_105_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_toFun_58_; lean_object* v_snd_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_103_; 
v_toFun_58_ = lean_ctor_get(v___x_51_, 0);
v_snd_59_ = lean_ctor_get(v_00_u03c4_25_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_00_u03c4_25_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v_00_u03c4_25_, 0);
lean_dec(v_unused_104_);
v___x_61_ = v_00_u03c4_25_;
v_isShared_62_ = v_isSharedCheck_103_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_snd_59_);
lean_dec(v_00_u03c4_25_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_103_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_val_63_; lean_object* v_inv_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_102_; 
v_val_63_ = lean_ctor_get(v_fst_53_, 0);
v_inv_64_ = lean_ctor_get(v_fst_53_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_fst_53_);
if (v_isSharedCheck_102_ == 0)
{
v___x_66_ = v_fst_53_;
v_isShared_67_ = v_isSharedCheck_102_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_inv_64_);
lean_inc(v_val_63_);
lean_dec(v_fst_53_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_102_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_val_68_; lean_object* v_inv_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_101_; 
v_val_68_ = lean_ctor_get(v_snd_54_, 0);
v_inv_69_ = lean_ctor_get(v_snd_54_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_snd_54_);
if (v_isSharedCheck_101_ == 0)
{
v___x_71_ = v_snd_54_;
v_isShared_72_ = v_isSharedCheck_101_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_inv_69_);
lean_inc(v_val_68_);
lean_dec(v_snd_54_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_101_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_inc_n(v_toFun_50_, 2);
v___x_73_ = lean_apply_1(v_toFun_50_, v_snd_39_);
v___x_74_ = lean_int_mul(v_val_41_, v_val_43_);
lean_dec(v_val_43_);
lean_dec(v_val_41_);
v___x_75_ = lean_int_mul(v_inv_44_, v_inv_42_);
lean_dec(v_inv_42_);
lean_dec(v_inv_44_);
v___x_76_ = lean_int_mul(v_val_45_, v_val_47_);
lean_dec(v_val_47_);
lean_dec(v_val_45_);
v___x_77_ = lean_int_mul(v_inv_48_, v_inv_46_);
lean_dec(v_inv_46_);
lean_dec(v_inv_48_);
v___x_78_ = lean_apply_1(v_toFun_50_, v_snd_40_);
lean_inc(v_toAddSemigroup_31_);
v___x_79_ = lean_apply_2(v_toAddSemigroup_31_, v___x_73_, v___x_78_);
lean_inc(v_toFun_58_);
v___x_80_ = lean_apply_1(v_toFun_58_, v___x_79_);
v___x_81_ = lean_int_mul(v___x_74_, v_val_63_);
lean_dec(v_val_63_);
lean_dec(v___x_74_);
v___x_82_ = lean_int_mul(v_inv_64_, v___x_75_);
lean_dec(v___x_75_);
lean_dec(v_inv_64_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_82_);
lean_ctor_set(v___x_71_, 0, v___x_81_);
v___x_84_ = v___x_71_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_100_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_85_ = lean_int_mul(v___x_76_, v_val_68_);
lean_dec(v_val_68_);
lean_dec(v___x_76_);
v___x_86_ = lean_int_mul(v_inv_69_, v___x_77_);
lean_dec(v___x_77_);
lean_dec(v_inv_69_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_86_);
lean_ctor_set(v___x_66_, 0, v___x_85_);
v___x_88_ = v___x_66_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_86_);
v___x_88_ = v_reuseFailAlloc_99_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___x_88_);
lean_ctor_set(v___x_56_, 0, v___x_84_);
v___x_90_ = v___x_56_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_98_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_inc_n(v_toFun_50_, 2);
v___x_91_ = lean_apply_1(v_toFun_50_, v___x_80_);
v___x_92_ = lean_apply_1(v_toFun_50_, v_snd_59_);
v___x_93_ = lean_apply_2(v_toAddSemigroup_31_, v___x_91_, v___x_92_);
lean_inc(v_toFun_58_);
v___x_94_ = lean_apply_1(v_toFun_58_, v___x_93_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_94_);
lean_ctor_set(v___x_61_, 0, v___x_90_);
v___x_96_ = v___x_61_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_to_int(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__1(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow(lean_object* v_e_110_, lean_object* v_g_111_){
_start:
{
lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_fst_112_ = lean_ctor_get(v_g_111_, 0);
v_snd_113_ = lean_ctor_get(v_g_111_, 1);
lean_inc(v_snd_113_);
v_fst_114_ = lean_ctor_get(v_fst_112_, 0);
v_snd_115_ = lean_ctor_get(v_fst_112_, 1);
lean_inc_n(v_snd_115_, 2);
v___x_116_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_117_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__1, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__1_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__1);
v___x_118_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_116_, v_snd_115_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_toSemiring_123_; lean_object* v_toMonoid_124_; lean_object* v___x_125_; lean_object* v_fst_126_; lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_185_; 
lean_inc(v_fst_114_);
lean_dec_ref(v_g_111_);
v___x_119_ = lean_unsigned_to_nat(2u);
v___x_120_ = lean_nat_add(v_e_110_, v___x_119_);
v___x_121_ = lean_nat_pow(v___x_119_, v___x_120_);
lean_dec(v___x_120_);
v___x_122_ = lp_mathlib_ZMod_commRing(v___x_121_);
v_toSemiring_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref(v_toSemiring_123_);
lean_dec_ref(v___x_122_);
v_toMonoid_124_ = lean_ctor_get(v_toSemiring_123_, 1);
lean_inc_ref(v_toMonoid_124_);
lean_dec_ref(v_toSemiring_123_);
v___x_125_ = lp_tree_Formalism_FrobeniusOrbits_cc(v_e_110_);
v_fst_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_fst_126_);
v_fst_127_ = lean_ctor_get(v_fst_126_, 0);
v_snd_128_ = lean_ctor_get(v_fst_126_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_fst_126_);
if (v_isSharedCheck_185_ == 0)
{
v___x_130_ = v_fst_126_;
v_isShared_131_ = v_isSharedCheck_185_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_128_);
lean_inc(v_fst_127_);
lean_dec(v_fst_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_185_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_snd_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_183_; 
v_snd_132_ = lean_ctor_get(v___x_125_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_125_, 0);
lean_dec(v_unused_184_);
v___x_134_ = v___x_125_;
v_isShared_135_ = v_isSharedCheck_183_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_snd_132_);
lean_dec(v___x_125_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_183_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_val_136_; lean_object* v_inv_137_; lean_object* v_val_138_; lean_object* v_inv_139_; lean_object* v_val_140_; lean_object* v_inv_141_; lean_object* v_val_142_; lean_object* v_inv_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_182_; 
v_val_136_ = lean_ctor_get(v_fst_127_, 0);
lean_inc(v_val_136_);
v_inv_137_ = lean_ctor_get(v_fst_127_, 1);
lean_inc(v_inv_137_);
lean_dec(v_fst_127_);
v_val_138_ = lean_ctor_get(v_fst_114_, 0);
lean_inc(v_val_138_);
v_inv_139_ = lean_ctor_get(v_fst_114_, 1);
lean_inc(v_inv_139_);
lean_dec(v_fst_114_);
v_val_140_ = lean_ctor_get(v_snd_128_, 0);
lean_inc(v_val_140_);
v_inv_141_ = lean_ctor_get(v_snd_128_, 1);
lean_inc(v_inv_141_);
lean_dec(v_snd_128_);
v_val_142_ = lean_ctor_get(v_snd_115_, 0);
v_inv_143_ = lean_ctor_get(v_snd_115_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_snd_115_);
if (v_isSharedCheck_182_ == 0)
{
v___x_145_ = v_snd_115_;
v_isShared_146_ = v_isSharedCheck_182_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_inv_143_);
lean_inc(v_val_142_);
lean_dec(v_snd_115_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_182_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v_toMul_148_; lean_object* v_val_149_; lean_object* v_inv_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_181_; 
v___x_147_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_124_);
lean_dec_ref(v_toMonoid_124_);
v_toMul_148_ = lean_ctor_get(v___x_147_, 1);
lean_inc(v_toMul_148_);
lean_dec_ref(v___x_147_);
v_val_149_ = lean_ctor_get(v_snd_132_, 0);
v_inv_150_ = lean_ctor_get(v_snd_132_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_snd_132_);
if (v_isSharedCheck_181_ == 0)
{
v___x_152_ = v_snd_132_;
v_isShared_153_ = v_isSharedCheck_181_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_inv_150_);
lean_inc(v_val_149_);
lean_dec(v_snd_132_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_181_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_val_154_; lean_object* v_inv_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_180_; 
v_val_154_ = lean_ctor_get(v_snd_113_, 0);
v_inv_155_ = lean_ctor_get(v_snd_113_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_snd_113_);
if (v_isSharedCheck_180_ == 0)
{
v___x_157_ = v_snd_113_;
v_isShared_158_ = v_isSharedCheck_180_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_inv_155_);
lean_inc(v_val_154_);
lean_dec(v_snd_113_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_180_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = lean_int_mul(v_val_136_, v_val_138_);
lean_dec(v_val_138_);
lean_dec(v_val_136_);
v___x_160_ = lean_int_mul(v_inv_139_, v_inv_137_);
lean_dec(v_inv_137_);
lean_dec(v_inv_139_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___x_160_);
lean_ctor_set(v___x_157_, 0, v___x_159_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_179_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_163_ = lean_int_mul(v_val_140_, v_val_142_);
lean_dec(v_val_142_);
lean_dec(v_val_140_);
v___x_164_ = lean_int_mul(v_inv_143_, v_inv_141_);
lean_dec(v_inv_141_);
lean_dec(v_inv_143_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_164_);
lean_ctor_set(v___x_152_, 0, v___x_163_);
v___x_166_ = v___x_152_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_178_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_166_);
lean_ctor_set(v___x_130_, 0, v___x_162_);
v___x_168_ = v___x_130_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_177_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
lean_inc(v_toMul_148_);
v___x_169_ = lean_apply_2(v_toMul_148_, v_val_149_, v_val_154_);
v___x_170_ = lean_apply_2(v_toMul_148_, v_inv_155_, v_inv_150_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_170_);
lean_ctor_set(v___x_145_, 0, v___x_169_);
v___x_172_ = v___x_145_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_172_);
lean_ctor_set(v___x_134_, 0, v___x_168_);
v___x_174_ = v___x_134_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v_snd_115_);
lean_dec(v_snd_113_);
return v_g_111_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___boxed(lean_object* v_e_186_, lean_object* v_g_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow(v_e_186_, v_g_187_);
lean_dec(v_e_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ch(lean_object* v_e_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lp_tree_Formalism_FrobeniusOrbits_chD(v_e_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ch___boxed(lean_object* v_e_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ch(v_e_191_);
lean_dec(v_e_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ps(lean_object* v_e_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_tree_Formalism_FrobeniusOrbits_chQ(v_e_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ps___boxed(lean_object* v_e_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_ps(v_e_195_);
lean_dec(v_e_195_);
return v_res_196_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0___closed__0(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0);
v___x_198_ = lean_int_neg(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0(void){
_start:
{
lean_object* v___x_199_; lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v_val_202_; lean_object* v_inv_203_; lean_object* v_val_204_; lean_object* v_inv_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_199_ = lp_tree_Formalism_FrobeniusOrbits_c0;
v_fst_200_ = lean_ctor_get(v___x_199_, 0);
v_snd_201_ = lean_ctor_get(v___x_199_, 1);
v_val_202_ = lean_ctor_get(v_fst_200_, 0);
v_inv_203_ = lean_ctor_get(v_fst_200_, 1);
v_val_204_ = lean_ctor_get(v_snd_201_, 0);
v_inv_205_ = lean_ctor_get(v_snd_201_, 1);
v___x_206_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_placeBelow___closed__0);
v___x_207_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0___closed__0);
v___x_208_ = lean_int_mul(v___x_207_, v_val_202_);
v___x_209_ = lean_int_mul(v_inv_203_, v___x_207_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_int_mul(v___x_206_, v_val_204_);
v___x_212_ = lean_int_mul(v_inv_205_, v___x_206_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_210_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lp_mathlib_Complex_commRing;
v___x_216_ = lp_mathlib_Ring_toNonAssocRing___redArg(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__0, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__0_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__0);
v___x_218_ = lp_mathlib_Int_castRingHom___redArg(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__2(void){
_start:
{
lean_object* v___x_219_; lean_object* v___f_220_; 
v___x_219_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__1, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__1_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__1);
v___f_220_ = lean_alloc_closure((void*)(lp_tree_Units_map___at___00Formalism_FrobeniusOrbits_chC_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_220_, 0, v___x_219_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx(lean_object* v_e_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___f_224_; 
v___f_222_ = lean_obj_once(&lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__2, &lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__2_once, _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___closed__2);
v___x_223_ = lp_tree_Formalism_FrobeniusOrbits_chD(v_e_221_);
v___f_224_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_224_, 0, v___x_223_);
lean_closure_set(v___f_224_, 1, v___f_222_);
return v___f_224_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx___boxed(lean_object* v_e_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = lp_tree_Formalism_MainNotions_GlobalTheoryTheory_chCx(v_e_225_);
lean_dec(v_e_225_);
return v_res_226_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FiltrationBoundaryCriterion(uint8_t builtin) {
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
lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0 = _init_lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0();
lean_mark_persistent(lp_tree_Formalism_MainNotions_GlobalTheoryTheory_sgc0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
