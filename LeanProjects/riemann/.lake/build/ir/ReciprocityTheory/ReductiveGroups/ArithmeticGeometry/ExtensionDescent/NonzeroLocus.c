// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
lean_object* lp_mathlib_TopologicalSpace_Opens_map___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_AlgebraicGeometry_Scheme_Opens_00_u03b9(lean_object*, lean_object*);
lean_object* lp_mathlib_AlgebraicGeometry_Scheme_Opens_toScheme(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_pullU___redArg(lean_object*, lean_object*);
lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_wchart___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_wchart___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___closed__0 = (const lean_object*)&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iSup___at___00ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_iSup___at___00ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__0(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__1(lean_object* v_left_7_, lean_object* v___x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lp_mathlib_AlgebraicGeometry_Scheme_Opens_00_u03b9(v_left_7_, v___x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__1___boxed(lean_object* v_left_11_, lean_object* v___x_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__1(v_left_11_, v___x_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_wchart___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__1(lean_object* v_N_15_, lean_object* v_X_16_, lean_object* v_Y_17_, lean_object* v_L_18_, lean_object* v_00_u03c6_19_, lean_object* v_j_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_wchart___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__1___boxed(lean_object* v_N_22_, lean_object* v_X_23_, lean_object* v_Y_24_, lean_object* v_L_25_, lean_object* v_00_u03c6_26_, lean_object* v_j_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_wchart___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__1(v_N_22_, v_X_23_, v_Y_24_, v_L_25_, v_00_u03c6_26_, v_j_27_);
lean_dec(v_j_27_);
lean_dec_ref(v_00_u03c6_26_);
lean_dec_ref(v_L_25_);
lean_dec_ref(v_Y_24_);
lean_dec_ref(v_X_23_);
lean_dec(v_N_22_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__2(lean_object* v_N_29_, lean_object* v_X_30_, lean_object* v_Y_31_, lean_object* v_L_32_, lean_object* v_00_u03c6_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__2___boxed(lean_object* v_N_36_, lean_object* v_X_37_, lean_object* v_Y_38_, lean_object* v_L_39_, lean_object* v_00_u03c6_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__2(v_N_36_, v_X_37_, v_Y_38_, v_L_39_, v_00_u03c6_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v_00_u03c6_40_);
lean_dec_ref(v_L_39_);
lean_dec_ref(v_Y_38_);
lean_dec_ref(v_X_37_);
lean_dec(v_N_36_);
return v_res_42_;
}
}
static lean_object* _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_43_; lean_object* v_intZero_44_; 
v_natZero_43_ = lean_unsigned_to_nat(0u);
v_intZero_44_ = lean_nat_to_int(v_natZero_43_);
return v_intZero_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0(lean_object* v_00_u03c6_45_, lean_object* v_L_46_, lean_object* v_j_47_, lean_object* v_j_x27_48_, lean_object* v_Y_49_, lean_object* v___x_50_, lean_object* v_00_u03b5_51_, lean_object* v_toMonoid_52_, lean_object* v_k_53_){
_start:
{
lean_object* v___x_54_; lean_object* v_g_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_499__overap_60_; lean_object* v___x_61_; lean_object* v___x_500__overap_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_intZero_65_; uint8_t v_isNeg_66_; 
lean_inc_n(v_k_53_, 3);
v___x_54_ = lean_apply_1(v_00_u03c6_45_, v_k_53_);
v_g_55_ = lean_ctor_get(v_L_46_, 1);
lean_inc_ref(v_g_55_);
lean_dec_ref(v_L_46_);
v___x_56_ = lean_apply_1(v_j_47_, v_k_53_);
v___x_57_ = lean_apply_1(v_j_x27_48_, v_k_53_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_2(v_g_55_, v___x_56_, v___x_57_);
v___x_499__overap_60_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_pullU___redArg(v___x_54_, v___x_58_);
v___x_61_ = lean_apply_1(v___x_499__overap_60_, v___x_59_);
v___x_500__overap_62_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_res___redArg(v_Y_49_, v___x_50_, v___x_50_);
v___x_63_ = lean_apply_1(v___x_500__overap_62_, v___x_61_);
v___x_64_ = lean_apply_1(v_00_u03b5_51_, v_k_53_);
v_intZero_65_ = lean_obj_once(&lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0___closed__0, &lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0___closed__0_once, _init_lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0___closed__0);
v_isNeg_66_ = lean_int_dec_lt(v___x_64_, v_intZero_65_);
if (v_isNeg_66_ == 0)
{
lean_object* v_toNPow_67_; lean_object* v_val_68_; lean_object* v_inv_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
v_toNPow_67_ = lean_ctor_get(v_toMonoid_52_, 2);
lean_inc(v_toNPow_67_);
lean_dec_ref(v_toMonoid_52_);
v_val_68_ = lean_ctor_get(v___x_63_, 0);
v_inv_69_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_79_ == 0)
{
v___x_71_ = v___x_63_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_inv_69_);
lean_inc(v_val_68_);
lean_dec(v___x_63_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_a_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v_a_73_ = lean_nat_abs(v___x_64_);
lean_dec(v___x_64_);
lean_inc(v_toNPow_67_);
lean_inc(v_a_73_);
v___x_74_ = lean_apply_2(v_toNPow_67_, v_a_73_, v_val_68_);
v___x_75_ = lean_apply_2(v_toNPow_67_, v_a_73_, v_inv_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_75_);
lean_ctor_set(v___x_71_, 0, v___x_74_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_object* v_toNPow_80_; lean_object* v_val_81_; lean_object* v_inv_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_95_; 
v_toNPow_80_ = lean_ctor_get(v_toMonoid_52_, 2);
lean_inc(v_toNPow_80_);
lean_dec_ref(v_toMonoid_52_);
v_val_81_ = lean_ctor_get(v___x_63_, 0);
v_inv_82_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_95_ == 0)
{
v___x_84_ = v___x_63_;
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_inv_82_);
lean_inc(v_val_81_);
lean_dec(v___x_63_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_abs_86_; lean_object* v_one_87_; lean_object* v_a_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v_abs_86_ = lean_nat_abs(v___x_64_);
lean_dec(v___x_64_);
v_one_87_ = lean_unsigned_to_nat(1u);
v_a_88_ = lean_nat_sub(v_abs_86_, v_one_87_);
lean_dec(v_abs_86_);
v___x_89_ = lean_nat_add(v_a_88_, v_one_87_);
lean_dec(v_a_88_);
lean_inc(v_toNPow_80_);
lean_inc(v___x_89_);
v___x_90_ = lean_apply_2(v_toNPow_80_, v___x_89_, v_val_81_);
v___x_91_ = lean_apply_2(v_toNPow_80_, v___x_89_, v_inv_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_90_);
lean_ctor_set(v___x_84_, 0, v___x_91_);
v___x_93_ = v___x_84_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_90_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___lam__0(lean_object* v___x_96_, lean_object* v_x1_97_, lean_object* v_x2_98_){
_start:
{
lean_object* v___x_99_; lean_object* v_toMul_100_; lean_object* v_val_101_; lean_object* v_inv_102_; lean_object* v_val_103_; lean_object* v_inv_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_113_; 
v___x_99_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_96_);
v_toMul_100_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_toMul_100_);
lean_dec_ref(v___x_99_);
v_val_101_ = lean_ctor_get(v_x1_97_, 0);
lean_inc(v_val_101_);
v_inv_102_ = lean_ctor_get(v_x1_97_, 1);
lean_inc(v_inv_102_);
lean_dec_ref(v_x1_97_);
v_val_103_ = lean_ctor_get(v_x2_98_, 0);
v_inv_104_ = lean_ctor_get(v_x2_98_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x2_98_);
if (v_isSharedCheck_113_ == 0)
{
v___x_106_ = v_x2_98_;
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_inv_104_);
lean_inc(v_val_103_);
lean_dec(v_x2_98_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_inc(v_toMul_100_);
v___x_108_ = lean_apply_2(v_toMul_100_, v_val_101_, v_val_103_);
v___x_109_ = lean_apply_2(v_toMul_100_, v_inv_104_, v_inv_102_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_109_);
lean_ctor_set(v___x_106_, 0, v___x_108_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___x_114_, lean_object* v_x1_115_, lean_object* v_x2_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___lam__0(v___x_114_, v_x1_115_, v_x2_116_);
lean_dec_ref(v___x_114_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1(lean_object* v___x_118_, lean_object* v_s_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_toOne_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
v___x_120_ = lp_mathlib_CommRing_toCommMonoid___redArg(v___x_118_);
v___x_121_ = lp_mathlib_Monoid_toMulOneClass___redArg(v___x_120_);
v_toOne_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_121_, 1);
lean_dec(v_unused_132_);
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_toOne_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___f_126_; lean_object* v___x_128_; 
v___f_126_ = lean_alloc_closure((void*)(lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_126_, 0, v___x_120_);
lean_inc(v_toOne_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v_toOne_122_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_toOne_122_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_toOne_122_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; 
v___x_129_ = l_List_foldrTR___redArg(v___f_126_, v___x_128_, v_s_119_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1___boxed(lean_object* v___x_133_, lean_object* v_s_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1(v___x_133_, v_s_134_);
lean_dec_ref(v___x_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg(lean_object* v___x_136_, lean_object* v_s_137_, lean_object* v_f_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lp_mathlib_Multiset_map___redArg(v_f_138_, v_s_137_);
v___x_140_ = lp_tree_Multiset_prod___at___00Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0_spec__1(v___x_136_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg___boxed(lean_object* v___x_141_, lean_object* v_s_142_, lean_object* v_f_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg(v___x_141_, v_s_142_, v_f_143_);
lean_dec_ref(v___x_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__1(lean_object* v_Y_145_, lean_object* v_N_146_, lean_object* v_00_u03c6_147_, lean_object* v_L_148_, lean_object* v_00_u03b5_149_, lean_object* v_j_150_, lean_object* v_j_x27_151_){
_start:
{
lean_object* v_presheaf_152_; lean_object* v_obj_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_toSemiring_156_; lean_object* v_toMonoid_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; 
v_presheaf_152_ = lean_ctor_get(v_Y_145_, 1);
v_obj_153_ = lean_ctor_get(v_presheaf_152_, 0);
v___x_154_ = lean_box(0);
lean_inc(v_obj_153_);
v___x_155_ = lean_apply_1(v_obj_153_, v___x_154_);
v_toSemiring_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_toSemiring_156_);
v_toMonoid_157_ = lean_ctor_get(v_toSemiring_156_, 1);
lean_inc_ref(v_toMonoid_157_);
lean_dec_ref(v_toSemiring_156_);
v___x_158_ = l_List_finRange(v_N_146_);
v___f_159_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__0), 9, 8);
lean_closure_set(v___f_159_, 0, v_00_u03c6_147_);
lean_closure_set(v___f_159_, 1, v_L_148_);
lean_closure_set(v___f_159_, 2, v_j_150_);
lean_closure_set(v___f_159_, 3, v_j_x27_151_);
lean_closure_set(v___f_159_, 4, v_Y_145_);
lean_closure_set(v___f_159_, 5, v___x_154_);
lean_closure_set(v___f_159_, 6, v_00_u03b5_149_);
lean_closure_set(v___f_159_, 7, v_toMonoid_157_);
v___x_160_ = lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg(v___x_155_, v___x_158_, v___f_159_);
lean_dec_ref(v___x_155_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0(lean_object* v_N_161_, lean_object* v_X_162_, lean_object* v_Y_163_, lean_object* v_L_164_, lean_object* v_00_u03c6_165_, lean_object* v_00_u03b5_166_){
_start:
{
lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
lean_inc_ref(v_L_164_);
lean_inc_ref(v_00_u03c6_165_);
lean_inc(v_N_161_);
lean_inc_ref(v_Y_163_);
v___f_167_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__1), 7, 5);
lean_closure_set(v___f_167_, 0, v_Y_163_);
lean_closure_set(v___f_167_, 1, v_N_161_);
lean_closure_set(v___f_167_, 2, v_00_u03c6_165_);
lean_closure_set(v___f_167_, 3, v_L_164_);
lean_closure_set(v___f_167_, 4, v_00_u03b5_166_);
v___f_168_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0___lam__2___boxed), 6, 5);
lean_closure_set(v___f_168_, 0, v_N_161_);
lean_closure_set(v___f_168_, 1, v_X_162_);
lean_closure_set(v___f_168_, 2, v_Y_163_);
lean_closure_set(v___f_168_, 3, v_L_164_);
lean_closure_set(v___f_168_, 4, v_00_u03c6_165_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___f_168_);
lean_ctor_set(v___x_169_, 1, v___f_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver(lean_object* v_S_171_, lean_object* v_A_172_, lean_object* v_L_173_, lean_object* v_U_174_, lean_object* v_N_175_){
_start:
{
lean_object* v_left_176_; lean_object* v_carrier_177_; lean_object* v_carrier_178_; lean_object* v___x_179_; lean_object* v_obj_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_left_176_ = lean_ctor_get(v_A_172_, 0);
lean_inc_n(v_left_176_, 3);
lean_dec_ref(v_A_172_);
v_carrier_177_ = lean_ctor_get(v_left_176_, 0);
lean_inc(v_carrier_177_);
v_carrier_178_ = lean_ctor_get(v_S_171_, 0);
lean_inc(v_carrier_178_);
lean_dec_ref(v_S_171_);
v___x_179_ = lp_mathlib_TopologicalSpace_Opens_map___redArg(v_carrier_177_, v_carrier_178_);
v_obj_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_obj_180_);
lean_dec_ref(v___x_179_);
v___f_181_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___closed__0));
v___x_182_ = lean_apply_1(v_obj_180_, v_U_174_);
v___f_183_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_Out_powOver___lam__1___boxed), 3, 2);
lean_closure_set(v___f_183_, 0, v_left_176_);
lean_closure_set(v___f_183_, 1, v___x_182_);
v___x_184_ = lp_mathlib_AlgebraicGeometry_Scheme_Opens_toScheme(v_left_176_, v___x_182_);
v___x_185_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0(v_N_175_, v_left_176_, v___x_184_, v_L_173_, v___f_183_, v___f_181_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0(lean_object* v___x_186_, lean_object* v_00_u03b9_187_, lean_object* v_s_188_, lean_object* v_f_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___redArg(v___x_186_, v_s_188_, v_f_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0___boxed(lean_object* v___x_191_, lean_object* v_00_u03b9_192_, lean_object* v_s_193_, lean_object* v_f_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = lp_tree_Finset_prod___at___00ReciprocityTheory_ChartRestriction_G_Semi_LB_LinComb___at___00ReciprocityTheory_ChartRestriction_G_Out_powOver_spec__0_spec__0(v___x_191_, v_00_u03b9_192_, v_s_193_, v_f_194_);
lean_dec_ref(v___x_191_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* lp_tree_iSup___at___00ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus_spec__0(lean_object* v___x_196_, lean_object* v_00_u03b9_197_, lean_object* v_s_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* lp_tree_iSup___at___00ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus_spec__0___boxed(lean_object* v___x_200_, lean_object* v_00_u03b9_201_, lean_object* v_s_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_tree_iSup___at___00ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus_spec__0(v___x_200_, v_00_u03b9_201_, v_s_202_);
lean_dec_ref(v_s_202_);
lean_dec_ref(v___x_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___lam__0(lean_object* v_k_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___lam__0___boxed(lean_object* v_k_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___lam__0(v_k_206_);
lean_dec(v_k_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg(lean_object* v_Y_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg___boxed(lean_object* v_Y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___redArg(v_Y_210_);
lean_dec_ref(v_Y_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus(lean_object* v_Y_212_, lean_object* v_M_213_, lean_object* v_s_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus___boxed(lean_object* v_Y_216_, lean_object* v_M_217_, lean_object* v_s_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = lp_tree_ReciprocityTheory_ChartRestriction_G_Out_nonzeroLocus(v_Y_216_, v_M_217_, v_s_218_);
lean_dec(v_s_218_);
lean_dec_ref(v_M_217_);
lean_dec_ref(v_Y_216_);
return v_res_219_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
