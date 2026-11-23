// Lean compiler output
// Module: Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal public import Formalism.LocalRingCardinality.Lemmas public import Formalism.LocalRingCardinality.DataParamsT
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
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_fdiv(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_tree_Formalism_MainNotions_WeightFamilies_dimY(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps___lam__0(lean_object* v_g_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_g_1_, v_k_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg(lean_object* v_i_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
if (lean_obj_tag(v_a_5_) == 0)
{
lean_object* v___x_7_; 
v___x_7_ = l_List_reverse___redArg(v_a_6_);
return v___x_7_;
}
else
{
lean_object* v_head_8_; lean_object* v_tail_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_19_; 
v_head_8_ = lean_ctor_get(v_a_5_, 0);
v_tail_9_ = lean_ctor_get(v_a_5_, 1);
v_isSharedCheck_19_ = !lean_is_exclusive(v_a_5_);
if (v_isSharedCheck_19_ == 0)
{
v___x_11_ = v_a_5_;
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_tail_9_);
lean_inc(v_head_8_);
lean_dec(v_a_5_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
uint8_t v___x_13_; 
v___x_13_ = lean_nat_dec_le(v_i_4_, v_head_8_);
if (v___x_13_ == 0)
{
lean_del_object(v___x_11_);
lean_dec(v_head_8_);
v_a_5_ = v_tail_9_;
goto _start;
}
else
{
lean_object* v___x_16_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v_a_6_);
v___x_16_ = v___x_11_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_head_8_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_a_6_);
v___x_16_ = v_reuseFailAlloc_18_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
v_a_5_ = v_tail_9_;
v_a_6_ = v___x_16_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_i_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg(v_i_20_, v_a_21_, v_a_22_);
lean_dec(v_i_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(lean_object* v_p_24_, lean_object* v_i_25_, lean_object* v_s_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(0);
v___x_28_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg(v_i_25_, v_s_26_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg___boxed(lean_object* v_p_29_, lean_object* v_i_30_, lean_object* v_s_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(v_p_29_, v_i_30_, v_s_31_);
lean_dec(v_i_30_);
lean_dec(v_p_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(lean_object* v_p_33_, lean_object* v_g_34_, lean_object* v_i_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps___lam__0), 2, 1);
lean_closure_set(v___f_36_, 0, v_g_34_);
lean_inc(v_p_33_);
v___x_37_ = l_List_finRange(v_p_33_);
v___x_38_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(v_p_33_, v_i_35_, v___x_37_);
lean_dec(v_p_33_);
v___x_39_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_38_, v___f_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps___boxed(lean_object* v_p_40_, lean_object* v_g_41_, lean_object* v_i_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(v_p_40_, v_g_41_, v_i_42_);
lean_dec(v_i_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___redArg(lean_object* v_p_44_, lean_object* v_i_45_, lean_object* v_s_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(v_p_44_, v_i_45_, v_s_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___redArg___boxed(lean_object* v_p_48_, lean_object* v_i_49_, lean_object* v_s_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___redArg(v_p_48_, v_i_49_, v_s_50_);
lean_dec(v_i_49_);
lean_dec(v_p_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0(lean_object* v_p_52_, lean_object* v_i_53_, lean_object* v_p_54_, lean_object* v_s_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(v_p_52_, v_i_53_, v_s_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0___boxed(lean_object* v_p_57_, lean_object* v_i_58_, lean_object* v_p_59_, lean_object* v_s_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0(v_p_57_, v_i_58_, v_p_59_, v_s_60_);
lean_dec(v_i_58_);
lean_dec(v_p_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0(lean_object* v_p_62_, lean_object* v_i_63_, lean_object* v_p_64_, lean_object* v_s_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___redArg(v_p_62_, v_i_63_, v_s_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0___boxed(lean_object* v_p_67_, lean_object* v_i_68_, lean_object* v_p_69_, lean_object* v_s_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_tree_Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0(v_p_67_, v_i_68_, v_p_69_, v_s_70_);
lean_dec(v_i_68_);
lean_dec(v_p_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1(lean_object* v_p_72_, lean_object* v_i_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___redArg(v_i_73_, v_a_74_, v_a_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1___boxed(lean_object* v_p_77_, lean_object* v_i_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00Formalism_MainNotions_DIV_Cons_ofGaps_spec__0_spec__0_spec__1(v_p_77_, v_i_78_, v_a_79_, v_a_80_);
lean_dec(v_i_78_);
lean_dec(v_p_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__0(lean_object* v_what_u2082_82_, lean_object* v_j_83_, lean_object* v_00_u03c4_84_, lean_object* v_i_85_){
_start:
{
lean_object* v_kaBig_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_kaBig_86_ = lean_ctor_get(v_what_u2082_82_, 44);
lean_inc_ref(v_kaBig_86_);
lean_dec_ref(v_what_u2082_82_);
v___x_87_ = lean_apply_3(v_kaBig_86_, v_j_83_, v_00_u03c4_84_, v_i_85_);
v___x_88_ = l_Int_toNat(v___x_87_);
lean_dec(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__1(lean_object* v_what_u2082_89_, lean_object* v_R_90_, lean_object* v_j_91_, lean_object* v_00_u03c4_92_, lean_object* v_c_93_){
_start:
{
lean_object* v_kaSmall_94_; lean_object* v___x_95_; lean_object* v_snd_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_kaSmall_94_ = lean_ctor_get(v_what_u2082_89_, 45);
lean_inc_ref(v_kaSmall_94_);
lean_dec_ref(v_what_u2082_89_);
v___x_95_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_90_, v_j_91_);
v_snd_96_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_snd_96_);
lean_dec_ref(v___x_95_);
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_c_93_, v___x_97_);
v___x_99_ = lean_nat_sub(v_snd_96_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v_snd_96_);
v___x_100_ = lean_apply_3(v_kaSmall_94_, v_j_91_, v_00_u03c4_92_, v___x_99_);
v___x_101_ = lean_int_neg(v___x_100_);
lean_dec(v___x_100_);
v___x_102_ = l_Int_toNat(v___x_101_);
lean_dec(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__1___boxed(lean_object* v_what_u2082_103_, lean_object* v_R_104_, lean_object* v_j_105_, lean_object* v_00_u03c4_106_, lean_object* v_c_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__1(v_what_u2082_103_, v_R_104_, v_j_105_, v_00_u03c4_106_, v_c_107_);
lean_dec(v_c_107_);
lean_dec_ref(v_R_104_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg(lean_object* v_D_109_, lean_object* v_j_110_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_dec_le(v___x_115_, v_j_110_);
if (v___x_116_ == 0)
{
lean_dec(v_j_110_);
goto v___jp_111_;
}
else
{
lean_object* v_R_117_; lean_object* v_what_u2082_118_; lean_object* v_m_119_; uint8_t v___x_120_; 
v_R_117_ = lean_ctor_get(v_D_109_, 0);
v_what_u2082_118_ = lean_ctor_get(v_D_109_, 4);
v_m_119_ = lean_ctor_get(v_R_117_, 2);
v___x_120_ = lean_nat_dec_le(v_j_110_, v_m_119_);
if (v___x_120_ == 0)
{
lean_dec(v_j_110_);
goto v___jp_111_;
}
else
{
lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_inc_ref_n(v_what_u2082_118_, 2);
lean_inc_ref_n(v_R_117_, 2);
lean_dec_ref(v_D_109_);
lean_inc(v_j_110_);
v___f_121_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__0), 4, 2);
lean_closure_set(v___f_121_, 0, v_what_u2082_118_);
lean_closure_set(v___f_121_, 1, v_j_110_);
v___f_122_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_122_, 0, v_what_u2082_118_);
lean_closure_set(v___f_122_, 1, v_R_117_);
lean_closure_set(v___f_122_, 2, v_j_110_);
v___x_123_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_117_);
lean_dec_ref(v_R_117_);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v___f_121_);
lean_ctor_set(v___x_124_, 1, v___f_122_);
lean_ctor_set(v___x_124_, 2, v___x_123_);
return v___x_124_;
}
}
v___jp_111_:
{
lean_object* v_R_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_R_112_ = lean_ctor_get(v_D_109_, 0);
lean_inc_ref(v_R_112_);
lean_dec_ref(v_D_109_);
v___x_113_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_112_);
lean_dec_ref(v_R_112_);
v___x_114_ = lp_tree_Formalism_MainNotions_WeightAlgebra_wscalar___redArg(v___x_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_kaWt(lean_object* v_D_125_, lean_object* v_hK_126_, lean_object* v_hn_127_, lean_object* v_j_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_tree_Formalism_MainNotions_DIV_Cons_kaWt___redArg(v_D_125_, v_j_128_);
return v___x_129_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(2u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapP(lean_object* v_D_132_, lean_object* v_j_133_, lean_object* v_ka_134_, lean_object* v_T_135_, lean_object* v_nW_136_, lean_object* v_00_u03c4_137_, lean_object* v_i_138_){
_start:
{
lean_object* v_R_139_; lean_object* v___x_140_; lean_object* v_fst_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_R_139_ = lean_ctor_get(v_D_132_, 0);
v___x_140_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_139_, v_j_133_);
v_fst_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_fst_141_);
lean_dec_ref(v___x_140_);
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v_i_138_, v___x_142_);
v___x_144_ = lean_nat_dec_lt(v___x_143_, v_fst_141_);
lean_dec(v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v_aP_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_fst_141_);
v_aP_145_ = lean_ctor_get(v_ka_134_, 0);
lean_inc_ref(v_aP_145_);
lean_dec_ref(v_ka_134_);
v___x_146_ = lean_apply_2(v_aP_145_, v_00_u03c4_137_, v_i_138_);
v___x_147_ = lean_nat_to_int(v___x_146_);
v___x_148_ = lp_tree_Formalism_MainNotions_WeightFamilies_dimY(v_D_132_, v_j_133_);
v___x_149_ = lean_nat_to_int(v___x_148_);
v___x_150_ = lean_obj_once(&lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0, &lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0_once, _init_lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0);
v___x_151_ = lean_int_add(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_nat_to_int(v_nW_136_);
v___x_153_ = lean_int_mul(v___x_151_, v___x_152_);
lean_dec(v___x_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_int_sub(v___x_147_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_147_);
v___x_155_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_139_);
v___x_156_ = lean_nat_to_int(v___x_155_);
v___x_157_ = lean_int_mul(v___x_150_, v___x_156_);
lean_dec(v___x_156_);
v___x_158_ = lean_int_sub(v___x_154_, v___x_157_);
lean_dec(v___x_157_);
lean_dec(v___x_154_);
v___x_159_ = lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(v_D_132_, v_j_133_, v_T_135_);
v___x_160_ = lean_nat_to_int(v___x_159_);
v___x_161_ = l_Int_fdiv(v___x_158_, v___x_160_);
lean_dec(v___x_160_);
lean_dec(v___x_158_);
v___x_162_ = l_Int_toNat(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
else
{
lean_object* v_aP_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_nW_136_);
v_aP_163_ = lean_ctor_get(v_ka_134_, 0);
lean_inc_ref(v_aP_163_);
lean_dec_ref(v_ka_134_);
v___x_164_ = lean_apply_1(v_aP_163_, v_00_u03c4_137_);
v___x_165_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_fst_141_, v___x_164_, v_i_138_);
lean_dec(v_fst_141_);
v___x_166_ = lean_obj_once(&lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0, &lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0_once, _init_lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0);
v___x_167_ = lean_int_add(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
v___x_168_ = lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(v_D_132_, v_j_133_, v_T_135_);
v___x_169_ = lean_nat_to_int(v___x_168_);
v___x_170_ = l_Int_fdiv(v___x_167_, v___x_169_);
lean_dec(v___x_169_);
lean_dec(v___x_167_);
v___x_171_ = l_Int_toNat(v___x_170_);
lean_dec(v___x_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___boxed(lean_object* v_D_172_, lean_object* v_j_173_, lean_object* v_ka_174_, lean_object* v_T_175_, lean_object* v_nW_176_, lean_object* v_00_u03c4_177_, lean_object* v_i_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lp_tree_Formalism_MainNotions_DIV_Cons_lGapP(v_D_172_, v_j_173_, v_ka_174_, v_T_175_, v_nW_176_, v_00_u03c4_177_, v_i_178_);
lean_dec(v_T_175_);
lean_dec(v_j_173_);
lean_dec_ref(v_D_172_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapM(lean_object* v_D_180_, lean_object* v_j_181_, lean_object* v_ka_182_, lean_object* v_T_183_, lean_object* v_00_u03c4_184_, lean_object* v_i_185_){
_start:
{
lean_object* v_R_186_; lean_object* v___x_187_; lean_object* v_snd_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_R_186_ = lean_ctor_get(v_D_180_, 0);
v___x_187_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_186_, v_j_181_);
v_snd_188_ = lean_ctor_get(v___x_187_, 1);
lean_inc(v_snd_188_);
lean_dec_ref(v___x_187_);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_add(v_i_185_, v___x_189_);
v___x_191_ = lean_nat_dec_lt(v___x_190_, v_snd_188_);
lean_dec(v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v_aM_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_snd_188_);
v_aM_192_ = lean_ctor_get(v_ka_182_, 1);
lean_inc_ref(v_aM_192_);
lean_dec_ref(v_ka_182_);
v___x_193_ = lean_apply_2(v_aM_192_, v_00_u03c4_184_, v_i_185_);
v___x_194_ = lean_nat_to_int(v___x_193_);
v___x_195_ = lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(v_D_180_, v_j_181_, v_T_183_);
v___x_196_ = lean_nat_to_int(v___x_195_);
v___x_197_ = l_Int_fdiv(v___x_194_, v___x_196_);
lean_dec(v___x_196_);
lean_dec(v___x_194_);
v___x_198_ = l_Int_toNat(v___x_197_);
lean_dec(v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_aM_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_aM_199_ = lean_ctor_get(v_ka_182_, 1);
lean_inc_ref(v_aM_199_);
lean_dec_ref(v_ka_182_);
v___x_200_ = lean_apply_1(v_aM_199_, v_00_u03c4_184_);
v___x_201_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_snd_188_, v___x_200_, v_i_185_);
lean_dec(v_snd_188_);
v___x_202_ = lean_obj_once(&lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0, &lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0_once, _init_lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___closed__0);
v___x_203_ = lean_int_add(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
v___x_204_ = lp_tree_Formalism_MainNotions_WeightAlgebra_Tp(v_D_180_, v_j_181_, v_T_183_);
v___x_205_ = lean_nat_to_int(v___x_204_);
v___x_206_ = l_Int_fdiv(v___x_203_, v___x_205_);
lean_dec(v___x_205_);
lean_dec(v___x_203_);
v___x_207_ = l_Int_toNat(v___x_206_);
lean_dec(v___x_206_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lGapM___boxed(lean_object* v_D_208_, lean_object* v_j_209_, lean_object* v_ka_210_, lean_object* v_T_211_, lean_object* v_00_u03c4_212_, lean_object* v_i_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = lp_tree_Formalism_MainNotions_DIV_Cons_lGapM(v_D_208_, v_j_209_, v_ka_210_, v_T_211_, v_00_u03c4_212_, v_i_213_);
lean_dec(v_T_211_);
lean_dec(v_j_209_);
lean_dec_ref(v_D_208_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__0(lean_object* v_D_215_, lean_object* v_j_216_, lean_object* v_ka_217_, lean_object* v_T_218_, lean_object* v_nW_219_, lean_object* v_00_u03c4_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_R_222_; lean_object* v___x_223_; lean_object* v_fst_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_R_222_ = lean_ctor_get(v_D_215_, 0);
v___x_223_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_222_, v_j_216_);
v_fst_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_fst_224_);
lean_dec_ref(v___x_223_);
v___x_225_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_lGapP___boxed), 7, 6);
lean_closure_set(v___x_225_, 0, v_D_215_);
lean_closure_set(v___x_225_, 1, v_j_216_);
lean_closure_set(v___x_225_, 2, v_ka_217_);
lean_closure_set(v___x_225_, 3, v_T_218_);
lean_closure_set(v___x_225_, 4, v_nW_219_);
lean_closure_set(v___x_225_, 5, v_00_u03c4_220_);
v___x_226_ = lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(v_fst_224_, v___x_225_, v___y_221_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__0___boxed(lean_object* v_D_227_, lean_object* v_j_228_, lean_object* v_ka_229_, lean_object* v_T_230_, lean_object* v_nW_231_, lean_object* v_00_u03c4_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__0(v_D_227_, v_j_228_, v_ka_229_, v_T_230_, v_nW_231_, v_00_u03c4_232_, v___y_233_);
lean_dec(v___y_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__1(lean_object* v_D_235_, lean_object* v_j_236_, lean_object* v_ka_237_, lean_object* v_T_238_, lean_object* v_00_u03c4_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_R_241_; lean_object* v___x_242_; lean_object* v_snd_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_R_241_ = lean_ctor_get(v_D_235_, 0);
v___x_242_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_241_, v_j_236_);
v_snd_243_ = lean_ctor_get(v___x_242_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v___x_242_);
v___x_244_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_lGapM___boxed), 6, 5);
lean_closure_set(v___x_244_, 0, v_D_235_);
lean_closure_set(v___x_244_, 1, v_j_236_);
lean_closure_set(v___x_244_, 2, v_ka_237_);
lean_closure_set(v___x_244_, 3, v_T_238_);
lean_closure_set(v___x_244_, 4, v_00_u03c4_239_);
v___x_245_ = lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(v_snd_243_, v___x_244_, v___y_240_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__1___boxed(lean_object* v_D_246_, lean_object* v_j_247_, lean_object* v_ka_248_, lean_object* v_T_249_, lean_object* v_00_u03c4_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__1(v_D_246_, v_j_247_, v_ka_248_, v_T_249_, v_00_u03c4_250_, v___y_251_);
lean_dec(v___y_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg(lean_object* v_D_253_, lean_object* v_j_254_, lean_object* v_ka_255_, lean_object* v_T_256_, lean_object* v_nW_257_){
_start:
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
lean_inc(v_nW_257_);
lean_inc(v_T_256_);
lean_inc_ref(v_ka_255_);
lean_inc(v_j_254_);
lean_inc_ref(v_D_253_);
v___f_258_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_258_, 0, v_D_253_);
lean_closure_set(v___f_258_, 1, v_j_254_);
lean_closure_set(v___f_258_, 2, v_ka_255_);
lean_closure_set(v___f_258_, 3, v_T_256_);
lean_closure_set(v___f_258_, 4, v_nW_257_);
v___f_259_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg___lam__1___boxed), 6, 4);
lean_closure_set(v___f_259_, 0, v_D_253_);
lean_closure_set(v___f_259_, 1, v_j_254_);
lean_closure_set(v___f_259_, 2, v_ka_255_);
lean_closure_set(v___f_259_, 3, v_T_256_);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v___f_258_);
lean_ctor_set(v___x_260_, 1, v___f_259_);
lean_ctor_set(v___x_260_, 2, v_nW_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_lWt(lean_object* v_D_261_, lean_object* v_j_262_, lean_object* v_ka_263_, lean_object* v_T_264_, lean_object* v_nW_265_, lean_object* v_hW_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lp_tree_Formalism_MainNotions_DIV_Cons_lWt___redArg(v_D_261_, v_j_262_, v_ka_263_, v_T_264_, v_nW_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapP(lean_object* v_D_268_, lean_object* v_j_269_, lean_object* v_ka_270_, lean_object* v_wL_271_, lean_object* v_T_272_, lean_object* v_00_u03c4_273_, lean_object* v_i_274_){
_start:
{
lean_object* v_R_275_; lean_object* v___x_276_; lean_object* v_fst_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_R_275_ = lean_ctor_get(v_D_268_, 0);
v___x_276_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_275_, v_j_269_);
v_fst_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_fst_277_);
lean_dec_ref(v___x_276_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_i_274_, v___x_278_);
v___x_280_ = lean_nat_dec_lt(v___x_279_, v_fst_277_);
lean_dec(v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v_aP_281_; lean_object* v_aP_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_fst_277_);
v_aP_281_ = lean_ctor_get(v_ka_270_, 0);
lean_inc_ref(v_aP_281_);
lean_dec_ref(v_ka_270_);
v_aP_282_ = lean_ctor_get(v_wL_271_, 0);
lean_inc_ref(v_aP_282_);
lean_dec_ref(v_wL_271_);
lean_inc(v_i_274_);
lean_inc(v_00_u03c4_273_);
v___x_283_ = lean_apply_2(v_aP_281_, v_00_u03c4_273_, v_i_274_);
v___x_284_ = lean_nat_to_int(v___x_283_);
v___x_285_ = lean_nat_to_int(v_T_272_);
v___x_286_ = lean_apply_2(v_aP_282_, v_00_u03c4_273_, v_i_274_);
v___x_287_ = lean_nat_to_int(v___x_286_);
v___x_288_ = lean_int_mul(v___x_285_, v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_285_);
v___x_289_ = lean_int_sub(v___x_284_, v___x_288_);
lean_dec(v___x_288_);
lean_dec(v___x_284_);
v___x_290_ = l_Int_toNat(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_aP_291_; lean_object* v_aP_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_aP_291_ = lean_ctor_get(v_ka_270_, 0);
lean_inc_ref(v_aP_291_);
lean_dec_ref(v_ka_270_);
v_aP_292_ = lean_ctor_get(v_wL_271_, 0);
lean_inc_ref(v_aP_292_);
lean_dec_ref(v_wL_271_);
lean_inc(v_00_u03c4_273_);
v___x_293_ = lean_apply_1(v_aP_291_, v_00_u03c4_273_);
lean_inc(v_i_274_);
v___x_294_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_fst_277_, v___x_293_, v_i_274_);
v___x_295_ = lean_nat_to_int(v_T_272_);
v___x_296_ = lean_apply_1(v_aP_292_, v_00_u03c4_273_);
v___x_297_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_fst_277_, v___x_296_, v_i_274_);
lean_dec(v_fst_277_);
v___x_298_ = lean_int_mul(v___x_295_, v___x_297_);
lean_dec(v___x_297_);
lean_dec(v___x_295_);
v___x_299_ = lean_int_sub(v___x_294_, v___x_298_);
lean_dec(v___x_298_);
lean_dec(v___x_294_);
v___x_300_ = l_Int_toNat(v___x_299_);
lean_dec(v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapP___boxed(lean_object* v_D_301_, lean_object* v_j_302_, lean_object* v_ka_303_, lean_object* v_wL_304_, lean_object* v_T_305_, lean_object* v_00_u03c4_306_, lean_object* v_i_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = lp_tree_Formalism_MainNotions_DIV_Cons_fGapP(v_D_301_, v_j_302_, v_ka_303_, v_wL_304_, v_T_305_, v_00_u03c4_306_, v_i_307_);
lean_dec(v_j_302_);
lean_dec_ref(v_D_301_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapM(lean_object* v_D_309_, lean_object* v_j_310_, lean_object* v_ka_311_, lean_object* v_wL_312_, lean_object* v_T_313_, lean_object* v_00_u03c4_314_, lean_object* v_i_315_){
_start:
{
lean_object* v_R_316_; lean_object* v___x_317_; lean_object* v_snd_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_R_316_ = lean_ctor_get(v_D_309_, 0);
v___x_317_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_316_, v_j_310_);
v_snd_318_ = lean_ctor_get(v___x_317_, 1);
lean_inc(v_snd_318_);
lean_dec_ref(v___x_317_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_add(v_i_315_, v___x_319_);
v___x_321_ = lean_nat_dec_lt(v___x_320_, v_snd_318_);
lean_dec(v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v_aM_322_; lean_object* v_aM_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_snd_318_);
v_aM_322_ = lean_ctor_get(v_ka_311_, 1);
lean_inc_ref(v_aM_322_);
lean_dec_ref(v_ka_311_);
v_aM_323_ = lean_ctor_get(v_wL_312_, 1);
lean_inc_ref(v_aM_323_);
lean_dec_ref(v_wL_312_);
lean_inc(v_i_315_);
lean_inc(v_00_u03c4_314_);
v___x_324_ = lean_apply_2(v_aM_322_, v_00_u03c4_314_, v_i_315_);
v___x_325_ = lean_nat_to_int(v___x_324_);
v___x_326_ = lean_nat_to_int(v_T_313_);
v___x_327_ = lean_apply_2(v_aM_323_, v_00_u03c4_314_, v_i_315_);
v___x_328_ = lean_nat_to_int(v___x_327_);
v___x_329_ = lean_int_mul(v___x_326_, v___x_328_);
lean_dec(v___x_328_);
lean_dec(v___x_326_);
v___x_330_ = lean_int_sub(v___x_325_, v___x_329_);
lean_dec(v___x_329_);
lean_dec(v___x_325_);
v___x_331_ = l_Int_toNat(v___x_330_);
lean_dec(v___x_330_);
return v___x_331_;
}
else
{
lean_object* v_aM_332_; lean_object* v_aM_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_aM_332_ = lean_ctor_get(v_ka_311_, 1);
lean_inc_ref(v_aM_332_);
lean_dec_ref(v_ka_311_);
v_aM_333_ = lean_ctor_get(v_wL_312_, 1);
lean_inc_ref(v_aM_333_);
lean_dec_ref(v_wL_312_);
lean_inc(v_00_u03c4_314_);
v___x_334_ = lean_apply_1(v_aM_332_, v_00_u03c4_314_);
lean_inc(v_i_315_);
v___x_335_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_snd_318_, v___x_334_, v_i_315_);
v___x_336_ = lean_nat_to_int(v_T_313_);
v___x_337_ = lean_apply_1(v_aM_333_, v_00_u03c4_314_);
v___x_338_ = lp_tree_Formalism_MainNotions_WeightAlgebra_gapZ(v_snd_318_, v___x_337_, v_i_315_);
lean_dec(v_snd_318_);
v___x_339_ = lean_int_mul(v___x_336_, v___x_338_);
lean_dec(v___x_338_);
lean_dec(v___x_336_);
v___x_340_ = lean_int_sub(v___x_335_, v___x_339_);
lean_dec(v___x_339_);
lean_dec(v___x_335_);
v___x_341_ = l_Int_toNat(v___x_340_);
lean_dec(v___x_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fGapM___boxed(lean_object* v_D_342_, lean_object* v_j_343_, lean_object* v_ka_344_, lean_object* v_wL_345_, lean_object* v_T_346_, lean_object* v_00_u03c4_347_, lean_object* v_i_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = lp_tree_Formalism_MainNotions_DIV_Cons_fGapM(v_D_342_, v_j_343_, v_ka_344_, v_wL_345_, v_T_346_, v_00_u03c4_347_, v_i_348_);
lean_dec(v_j_343_);
lean_dec_ref(v_D_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__0(lean_object* v_D_350_, lean_object* v_j_351_, lean_object* v_ka_352_, lean_object* v_wL_353_, lean_object* v_T_354_, lean_object* v_00_u03c4_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_R_357_; lean_object* v___x_358_; lean_object* v_fst_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_R_357_ = lean_ctor_get(v_D_350_, 0);
v___x_358_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_357_, v_j_351_);
v_fst_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_fst_359_);
lean_dec_ref(v___x_358_);
v___x_360_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_fGapP___boxed), 7, 6);
lean_closure_set(v___x_360_, 0, v_D_350_);
lean_closure_set(v___x_360_, 1, v_j_351_);
lean_closure_set(v___x_360_, 2, v_ka_352_);
lean_closure_set(v___x_360_, 3, v_wL_353_);
lean_closure_set(v___x_360_, 4, v_T_354_);
lean_closure_set(v___x_360_, 5, v_00_u03c4_355_);
v___x_361_ = lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(v_fst_359_, v___x_360_, v___y_356_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__0___boxed(lean_object* v_D_362_, lean_object* v_j_363_, lean_object* v_ka_364_, lean_object* v_wL_365_, lean_object* v_T_366_, lean_object* v_00_u03c4_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__0(v_D_362_, v_j_363_, v_ka_364_, v_wL_365_, v_T_366_, v_00_u03c4_367_, v___y_368_);
lean_dec(v___y_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__1(lean_object* v_D_370_, lean_object* v_j_371_, lean_object* v_ka_372_, lean_object* v_wL_373_, lean_object* v_T_374_, lean_object* v_00_u03c4_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_R_377_; lean_object* v___x_378_; lean_object* v_snd_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_R_377_ = lean_ctor_get(v_D_370_, 0);
v___x_378_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_377_, v_j_371_);
v_snd_379_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_snd_379_);
lean_dec_ref(v___x_378_);
v___x_380_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_fGapM___boxed), 7, 6);
lean_closure_set(v___x_380_, 0, v_D_370_);
lean_closure_set(v___x_380_, 1, v_j_371_);
lean_closure_set(v___x_380_, 2, v_ka_372_);
lean_closure_set(v___x_380_, 3, v_wL_373_);
lean_closure_set(v___x_380_, 4, v_T_374_);
lean_closure_set(v___x_380_, 5, v_00_u03c4_375_);
v___x_381_ = lp_tree_Formalism_MainNotions_DIV_Cons_ofGaps(v_snd_379_, v___x_380_, v___y_376_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__1___boxed(lean_object* v_D_382_, lean_object* v_j_383_, lean_object* v_ka_384_, lean_object* v_wL_385_, lean_object* v_T_386_, lean_object* v_00_u03c4_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__1(v_D_382_, v_j_383_, v_ka_384_, v_wL_385_, v_T_386_, v_00_u03c4_387_, v___y_388_);
lean_dec(v___y_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg(lean_object* v_D_390_, lean_object* v_j_391_, lean_object* v_ka_392_, lean_object* v_wL_393_, lean_object* v_T_394_, lean_object* v_nP_395_){
_start:
{
lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
lean_inc(v_T_394_);
lean_inc_ref(v_wL_393_);
lean_inc_ref(v_ka_392_);
lean_inc(v_j_391_);
lean_inc_ref(v_D_390_);
v___f_396_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_396_, 0, v_D_390_);
lean_closure_set(v___f_396_, 1, v_j_391_);
lean_closure_set(v___f_396_, 2, v_ka_392_);
lean_closure_set(v___f_396_, 3, v_wL_393_);
lean_closure_set(v___f_396_, 4, v_T_394_);
v___f_397_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_397_, 0, v_D_390_);
lean_closure_set(v___f_397_, 1, v_j_391_);
lean_closure_set(v___f_397_, 2, v_ka_392_);
lean_closure_set(v___f_397_, 3, v_wL_393_);
lean_closure_set(v___f_397_, 4, v_T_394_);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v___f_396_);
lean_ctor_set(v___x_398_, 1, v___f_397_);
lean_ctor_set(v___x_398_, 2, v_nP_395_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_DIV_Cons_fWt(lean_object* v_D_399_, lean_object* v_j_400_, lean_object* v_ka_401_, lean_object* v_wL_402_, lean_object* v_T_403_, lean_object* v_nP_404_, lean_object* v_hP_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lp_tree_Formalism_MainNotions_DIV_Cons_fWt___redArg(v_D_399_, v_j_400_, v_ka_401_, v_wL_402_, v_T_403_, v_nP_404_);
return v___x_406_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LiftErrorLocal(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_LocalNonemptiness_LiftErrorLocal(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_Lemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParamsT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_Divisibility_AbelianOpenPart_KaSmallNonpos(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LiftErrorLocal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_Divisibility_LocalNonemptiness_LiftErrorLocal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParamsT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
