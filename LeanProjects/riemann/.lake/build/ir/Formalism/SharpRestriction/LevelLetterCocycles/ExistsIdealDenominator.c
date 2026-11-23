// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalRingHom_id___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Multiplicative_toAdd(lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_nonZeroDivisors___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_nonZeroDivisors___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_NonUnitalRingHom_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_OreLocalization_one___at___00Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_nonZeroDivisors___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__0(lean_object* v___x_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_nonZeroDivisors___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__0___boxed(lean_object* v___x_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_nonZeroDivisors___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__0(v___x_4_, v_i_5_);
lean_dec(v_i_5_);
lean_dec_ref(v___x_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1___redArg(lean_object* v_r_7_, lean_object* v_s_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_r_7_);
lean_ctor_set(v___x_9_, 1, v_s_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1(lean_object* v___x_10_, lean_object* v_i_11_, lean_object* v___x_12_, lean_object* v_S_13_, lean_object* v_r_14_, lean_object* v_s_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_r_14_);
lean_ctor_set(v___x_16_, 1, v_s_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1___boxed(lean_object* v___x_17_, lean_object* v_i_18_, lean_object* v___x_19_, lean_object* v_S_20_, lean_object* v_r_21_, lean_object* v_s_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_dat_spec__1(v___x_17_, v_i_18_, v___x_19_, v_S_20_, v_r_21_, v_s_22_);
lean_dec(v_i_18_);
lean_dec_ref(v___x_17_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___lam__0(lean_object* v_toOne_24_, lean_object* v_r_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_r_25_);
lean_ctor_set(v___x_26_, 1, v_toOne_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg(lean_object* v_D_28_, lean_object* v_i_29_, lean_object* v_00_u03c6l_30_, lean_object* v_00_u03c6n_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_ntw_33_; lean_object* v_crO_34_; lean_object* v___x_35_; lean_object* v_toSemiring_36_; lean_object* v_toMonoid_37_; lean_object* v___x_38_; lean_object* v_toOne_39_; lean_object* v___x_40_; lean_object* v_toMul_41_; lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_ntw_33_ = lean_ctor_get(v_D_28_, 42);
lean_inc_ref(v_ntw_33_);
lean_dec_ref(v_D_28_);
v_crO_34_ = lean_ctor_get(v_ntw_33_, 7);
lean_inc_ref(v_crO_34_);
lean_dec_ref(v_ntw_33_);
v___x_35_ = lean_apply_1(v_crO_34_, v_i_29_);
v_toSemiring_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_toSemiring_36_);
lean_dec_ref(v___x_35_);
v_toMonoid_37_ = lean_ctor_get(v_toSemiring_36_, 1);
v___x_38_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_37_);
v_toOne_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_toOne_39_);
lean_dec_ref(v___x_38_);
v___x_40_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_36_);
v_toMul_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_toMul_41_);
lean_dec_ref(v___x_40_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___lam__0), 2, 1);
lean_closure_set(v___f_42_, 0, v_toOne_39_);
v___f_43_ = ((lean_object*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg___closed__0));
lean_inc(v_x_32_);
v___x_44_ = lean_apply_1(v_00_u03c6l_30_, v_x_32_);
v___x_45_ = lean_apply_1(v_00_u03c6n_31_, v_x_32_);
v___x_46_ = lean_apply_2(v_toMul_41_, v___x_44_, v___x_45_);
v___x_47_ = lp_mathlib_RingHom_comp___redArg___lam__0(v___f_43_, v___f_42_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat(lean_object* v_D_48_, lean_object* v_i_49_, lean_object* v_j_50_, lean_object* v_00_u03c6l_51_, lean_object* v_00_u03c6n_52_, lean_object* v_x_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg(v_D_48_, v_i_49_, v_00_u03c6l_51_, v_00_u03c6n_52_, v_x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___boxed(lean_object* v_D_55_, lean_object* v_i_56_, lean_object* v_j_57_, lean_object* v_00_u03c6l_58_, lean_object* v_00_u03c6n_59_, lean_object* v_x_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat(v_D_55_, v_i_56_, v_j_57_, v_00_u03c6l_58_, v_00_u03c6n_59_, v_x_60_);
lean_dec(v_j_57_);
return v_res_61_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg___closed__0(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lp_mathlib_Multiplicative_toAdd(lean_box(0));
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg(lean_object* v_D_63_, lean_object* v_i_64_, lean_object* v_j_65_, lean_object* v_00_u03b4_66_, lean_object* v_y_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_nth_69_; lean_object* v_recDet_70_; lean_object* v___x_71_; lean_object* v_toFun_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_nth_69_ = lean_ctor_get(v_D_63_, 47);
lean_inc_ref(v_nth_69_);
lean_dec_ref(v_D_63_);
v_recDet_70_ = lean_ctor_get(v_nth_69_, 10);
lean_inc_ref(v_recDet_70_);
lean_dec_ref(v_nth_69_);
v___x_71_ = lean_obj_once(&lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg___closed__0, &lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg___closed__0);
v_toFun_72_ = lean_ctor_get(v___x_71_, 0);
v___x_73_ = lean_apply_3(v_recDet_70_, v_i_64_, v_j_65_, v_y_67_);
v___x_74_ = lean_apply_1(v_00_u03b4_66_, v___x_73_);
lean_inc(v_toFun_72_);
v___x_75_ = lean_apply_2(v_toFun_72_, v___x_74_, v_a_68_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY(lean_object* v_D_76_, lean_object* v_i_77_, lean_object* v_j_78_, lean_object* v_M_79_, lean_object* v_Q_80_, lean_object* v_00_u03b4_81_, lean_object* v_y_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg(v_D_76_, v_i_77_, v_j_78_, v_00_u03b4_81_, v_y_82_, v_a_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___boxed(lean_object* v_D_85_, lean_object* v_i_86_, lean_object* v_j_87_, lean_object* v_M_88_, lean_object* v_Q_89_, lean_object* v_00_u03b4_90_, lean_object* v_y_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY(v_D_85_, v_i_86_, v_j_87_, v_M_88_, v_Q_89_, v_00_u03b4_90_, v_y_91_, v_a_92_);
lean_dec(v_Q_89_);
lean_dec(v_M_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___redArg(lean_object* v_r_94_){
_start:
{
lean_inc(v_r_94_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___redArg___boxed(lean_object* v_r_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___redArg(v_r_95_);
lean_dec(v_r_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1(lean_object* v___x_97_, lean_object* v_i_98_, lean_object* v___x_99_, lean_object* v_S_100_, lean_object* v_r_101_, lean_object* v_s_102_){
_start:
{
lean_inc(v_r_101_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1___boxed(lean_object* v___x_103_, lean_object* v_i_104_, lean_object* v___x_105_, lean_object* v_S_106_, lean_object* v_r_107_, lean_object* v_s_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_OreLocalization_oreNum___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__1(v___x_103_, v_i_104_, v___x_105_, v_S_106_, v_r_107_, v_s_108_);
lean_dec(v_s_108_);
lean_dec(v_r_107_);
lean_dec(v_i_104_);
lean_dec_ref(v___x_103_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___redArg(lean_object* v_s_110_){
_start:
{
lean_inc(v_s_110_);
return v_s_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___redArg___boxed(lean_object* v_s_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___redArg(v_s_111_);
lean_dec(v_s_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2(lean_object* v___x_113_, lean_object* v_i_114_, lean_object* v___x_115_, lean_object* v_S_116_, lean_object* v_r_117_, lean_object* v_s_118_){
_start:
{
lean_inc(v_s_118_);
return v_s_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2___boxed(lean_object* v___x_119_, lean_object* v_i_120_, lean_object* v___x_121_, lean_object* v_S_122_, lean_object* v_r_123_, lean_object* v_s_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_tree_OreLocalization_oreDenom___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__2(v___x_119_, v_i_120_, v___x_121_, v_S_122_, v_r_123_, v_s_124_);
lean_dec(v_s_124_);
lean_dec(v_r_123_);
lean_dec(v_i_120_);
lean_dec_ref(v___x_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3___redArg(lean_object* v_r_126_, lean_object* v_s_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_r_126_);
lean_ctor_set(v___x_128_, 1, v_s_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3(lean_object* v___x_129_, lean_object* v_i_130_, lean_object* v___x_131_, lean_object* v_S_132_, lean_object* v_r_133_, lean_object* v_s_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_r_133_);
lean_ctor_set(v___x_135_, 1, v_s_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3___boxed(lean_object* v___x_136_, lean_object* v_i_137_, lean_object* v___x_138_, lean_object* v_S_139_, lean_object* v_r_140_, lean_object* v_s_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_tree_OreLocalization_oreDiv___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__3(v___x_136_, v_i_137_, v___x_138_, v_S_139_, v_r_140_, v_s_141_);
lean_dec(v_i_137_);
lean_dec_ref(v___x_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(lean_object* v_P_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_fst_145_; lean_object* v_snd_146_; lean_object* v___x_147_; 
v_fst_145_ = lean_ctor_get(v_a_144_, 0);
lean_inc(v_fst_145_);
v_snd_146_ = lean_ctor_get(v_a_144_, 1);
lean_inc(v_snd_146_);
lean_dec(v_a_144_);
v___x_147_ = lean_apply_2(v_P_143_, v_fst_145_, v_snd_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4(lean_object* v___x_148_, lean_object* v_i_149_, lean_object* v___x_150_, lean_object* v_S_151_, lean_object* v_C_152_, lean_object* v_P_153_, lean_object* v_hP_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(v_P_153_, v_a_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___boxed(lean_object* v___x_157_, lean_object* v_i_158_, lean_object* v___x_159_, lean_object* v_S_160_, lean_object* v_C_161_, lean_object* v_P_162_, lean_object* v_hP_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4(v___x_157_, v_i_158_, v___x_159_, v_S_160_, v_C_161_, v_P_162_, v_hP_163_, v_a_164_);
lean_dec(v_i_158_);
lean_dec_ref(v___x_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__0(lean_object* v_l_166_, lean_object* v_i_167_, lean_object* v_M_168_, lean_object* v_b_169_, lean_object* v_D_170_, lean_object* v_j_171_, lean_object* v_00_u03b4_172_, lean_object* v_y_173_, lean_object* v_00_u03a6_174_, lean_object* v_x_175_, lean_object* v_q_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_toSub_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc(v_i_167_);
v___x_177_ = lean_apply_1(v_l_166_, v_i_167_);
v___x_178_ = lean_nat_pow(v___x_177_, v_M_168_);
lean_dec(v___x_177_);
v___x_179_ = lp_mathlib_ZMod_commRing(v___x_178_);
v___x_180_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v___x_179_);
v___x_181_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_180_);
lean_dec_ref(v___x_180_);
v_toSub_182_ = lean_ctor_get(v___x_181_, 2);
lean_inc(v_toSub_182_);
lean_dec_ref(v___x_181_);
v___x_183_ = lean_apply_1(v_b_169_, v_q_176_);
v___x_184_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_delY___redArg(v_D_170_, v_i_167_, v_j_171_, v_00_u03b4_172_, v_y_173_, v_q_176_);
v___x_185_ = lean_apply_2(v_toSub_182_, v___x_183_, v___x_184_);
v___x_186_ = lean_apply_3(v_00_u03a6_174_, v_q_176_, v___x_185_, v_x_175_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__0___boxed(lean_object* v_l_187_, lean_object* v_i_188_, lean_object* v_M_189_, lean_object* v_b_190_, lean_object* v_D_191_, lean_object* v_j_192_, lean_object* v_00_u03b4_193_, lean_object* v_y_194_, lean_object* v_00_u03a6_195_, lean_object* v_x_196_, lean_object* v_q_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__0(v_l_187_, v_i_188_, v_M_189_, v_b_190_, v_D_191_, v_j_192_, v_00_u03b4_193_, v_y_194_, v_00_u03a6_195_, v_x_196_, v_q_197_);
lean_dec(v_M_189_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1(lean_object* v___x_199_, lean_object* v_x1_200_, lean_object* v_x2_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_204_; lean_object* v_toMul_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_214_; 
v___x_204_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_199_);
v_toMul_205_ = lean_ctor_get(v___x_204_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v___x_204_, 0);
lean_dec(v_unused_215_);
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_toMul_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
lean_inc(v_toMul_205_);
v___x_209_ = lean_apply_2(v_toMul_205_, v_x1_200_, v___y_202_);
v___x_210_ = lean_apply_2(v_toMul_205_, v___y_203_, v_x2_201_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v___x_210_);
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_212_ = v___x_207_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1___boxed(lean_object* v___x_216_, lean_object* v_x1_217_, lean_object* v_x2_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1(v___x_216_, v_x1_217_, v_x2_218_, v___y_219_, v___y_220_);
lean_dec_ref(v___x_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__2(lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v_x1_224_, lean_object* v_x2_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; 
v___f_226_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1___boxed), 5, 3);
lean_closure_set(v___f_226_, 0, v___x_222_);
lean_closure_set(v___f_226_, 1, v_x1_224_);
lean_closure_set(v___f_226_, 2, v_x2_225_);
v___x_227_ = lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(v___f_226_, v___x_223_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_tree_OreLocalization_one___at___00Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0_spec__5(lean_object* v___x_228_, lean_object* v_i_229_, lean_object* v___x_230_, lean_object* v_S_231_){
_start:
{
lean_object* v_crO_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toOne_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_crO_232_ = lean_ctor_get(v___x_228_, 7);
lean_inc_ref(v_crO_232_);
lean_dec_ref(v___x_228_);
v___x_233_ = lean_apply_1(v_crO_232_, v_i_229_);
v___x_234_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_234_);
lean_dec_ref(v___x_234_);
v_toOne_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_244_);
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toOne_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
lean_inc(v_toOne_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_toOne_236_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_toOne_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_toOne_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0___lam__1(lean_object* v___x_245_, lean_object* v_x2_246_, lean_object* v_x1_247_, lean_object* v_x2_248_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; 
v___f_249_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__1___boxed), 5, 3);
lean_closure_set(v___f_249_, 0, v___x_245_);
lean_closure_set(v___f_249_, 1, v_x1_247_);
lean_closure_set(v___f_249_, 2, v_x2_248_);
v___x_250_ = lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(v___f_249_, v_x2_246_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0___lam__0(lean_object* v___x_251_, lean_object* v_x1_252_, lean_object* v_x2_253_){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; 
v___f_254_ = lean_alloc_closure((void*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0___lam__1), 4, 2);
lean_closure_set(v___f_254_, 0, v___x_251_);
lean_closure_set(v___f_254_, 1, v_x2_253_);
v___x_255_ = lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(v___f_254_, v_x1_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0(lean_object* v___x_256_, lean_object* v_i_257_, lean_object* v___x_258_, lean_object* v_s_259_){
_start:
{
lean_object* v_crO_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_crO_260_ = lean_ctor_get(v___x_256_, 7);
lean_inc_ref(v_crO_260_);
lean_inc(v_i_257_);
v___x_261_ = lean_apply_1(v_crO_260_, v_i_257_);
v___x_262_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_261_);
lean_dec_ref(v___x_261_);
v___f_263_ = lean_alloc_closure((void*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_263_, 0, v___x_262_);
v___x_264_ = lp_tree_OreLocalization_one___at___00Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0_spec__5(v___x_256_, v_i_257_, v___x_258_, v___x_258_);
v___x_265_ = l_List_foldrTR___redArg(v___f_263_, v___x_264_, v_s_259_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0___redArg(lean_object* v___x_266_, lean_object* v_i_267_, lean_object* v___x_268_, lean_object* v_s_269_, lean_object* v_f_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lp_mathlib_Multiset_map___redArg(v_f_270_, v_s_269_);
v___x_272_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0_spec__0(v___x_266_, v_i_267_, v___x_268_, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__3(lean_object* v_ntw_273_, lean_object* v_i_274_, lean_object* v_M_275_, lean_object* v_b_276_, lean_object* v_D_277_, lean_object* v_j_278_, lean_object* v_00_u03b4_279_, lean_object* v_y_280_, lean_object* v_00_u03a6_281_, lean_object* v_00_u03c6l_282_, lean_object* v_00_u03c6n_283_, lean_object* v_Q_284_, lean_object* v_x_285_){
_start:
{
lean_object* v_l_286_; lean_object* v_crO_287_; lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
v_l_286_ = lean_ctor_get(v_ntw_273_, 1);
v_crO_287_ = lean_ctor_get(v_ntw_273_, 7);
lean_inc(v_x_285_);
lean_inc_ref(v_D_277_);
lean_inc_n(v_i_274_, 3);
lean_inc_ref(v_l_286_);
v___f_288_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__0___boxed), 11, 10);
lean_closure_set(v___f_288_, 0, v_l_286_);
lean_closure_set(v___f_288_, 1, v_i_274_);
lean_closure_set(v___f_288_, 2, v_M_275_);
lean_closure_set(v___f_288_, 3, v_b_276_);
lean_closure_set(v___f_288_, 4, v_D_277_);
lean_closure_set(v___f_288_, 5, v_j_278_);
lean_closure_set(v___f_288_, 6, v_00_u03b4_279_);
lean_closure_set(v___f_288_, 7, v_y_280_);
lean_closure_set(v___f_288_, 8, v_00_u03a6_281_);
lean_closure_set(v___f_288_, 9, v_x_285_);
lean_inc_ref(v_crO_287_);
v___x_289_ = lean_apply_1(v_crO_287_, v_i_274_);
v___x_290_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_289_);
lean_dec_ref(v___x_289_);
v___x_291_ = lean_box(0);
v___x_292_ = lp_tree_Formalism_MainNotions_ExistsIdealDenominator_dat___redArg(v_D_277_, v_i_274_, v_00_u03c6l_282_, v_00_u03c6n_283_, v_x_285_);
v___x_293_ = lp_mathlib_Multiset_attach___redArg(v_Q_284_);
v___x_294_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0___redArg(v_ntw_273_, v_i_274_, v___x_291_, v___x_293_, v___f_288_);
v___f_295_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__2), 4, 2);
lean_closure_set(v___f_295_, 0, v___x_290_);
lean_closure_set(v___f_295_, 1, v___x_294_);
v___x_296_ = lp_tree_OreLocalization_liftExpand___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__4___redArg(v___f_295_, v___x_292_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef(lean_object* v_D_297_, lean_object* v_i_298_, lean_object* v_j_299_, lean_object* v_M_300_, lean_object* v_Q_301_, lean_object* v_00_u03b4_302_, lean_object* v_00_u03a6_303_, lean_object* v_00_u03c6l_304_, lean_object* v_00_u03c6n_305_, lean_object* v_P_306_, lean_object* v_b_307_, lean_object* v_y_308_){
_start:
{
lean_object* v_nth_309_; lean_object* v_ntw_310_; lean_object* v_thV_311_; lean_object* v___f_312_; lean_object* v___x_313_; 
v_nth_309_ = lean_ctor_get(v_D_297_, 47);
v_ntw_310_ = lean_ctor_get(v_D_297_, 42);
lean_inc_ref(v_ntw_310_);
v_thV_311_ = lean_ctor_get(v_nth_309_, 7);
lean_inc(v_thV_311_);
lean_inc(v_y_308_);
lean_inc(v_j_299_);
lean_inc(v_i_298_);
v___f_312_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_ExistsIdealDenominator_coef___lam__3), 13, 12);
lean_closure_set(v___f_312_, 0, v_ntw_310_);
lean_closure_set(v___f_312_, 1, v_i_298_);
lean_closure_set(v___f_312_, 2, v_M_300_);
lean_closure_set(v___f_312_, 3, v_b_307_);
lean_closure_set(v___f_312_, 4, v_D_297_);
lean_closure_set(v___f_312_, 5, v_j_299_);
lean_closure_set(v___f_312_, 6, v_00_u03b4_302_);
lean_closure_set(v___f_312_, 7, v_y_308_);
lean_closure_set(v___f_312_, 8, v_00_u03a6_303_);
lean_closure_set(v___f_312_, 9, v_00_u03c6l_304_);
lean_closure_set(v___f_312_, 10, v_00_u03c6n_305_);
lean_closure_set(v___f_312_, 11, v_Q_301_);
v___x_313_ = lean_apply_5(v_thV_311_, v_i_298_, v_j_299_, v___f_312_, v_P_306_, v_y_308_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0(lean_object* v___x_314_, lean_object* v_i_315_, lean_object* v___x_316_, lean_object* v_00_u03b9_317_, lean_object* v_s_318_, lean_object* v_f_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lp_tree_Finset_prod___at___00Formalism_MainNotions_ExistsIdealDenominator_coef_spec__0___redArg(v___x_314_, v_i_315_, v___x_316_, v_s_318_, v_f_319_);
return v___x_320_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_ExistsIdealDenominator(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
