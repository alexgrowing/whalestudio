// Lean compiler output
// Module: Formalism.SharpRestriction.FamCore
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.DFam
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_mathlib_ZMod_unitOfCoprime___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_HC_Frame_iotaInv___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_wordBits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_wordBits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_suppAt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_suppAt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_suppAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0___redArg(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_TTwVals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_TTwVals___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_TTwVals___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_TTwVals___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_MainNotions_artNum___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_artNum___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_MainNotions_artNum___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_artNum___redArg___closed__1;
static lean_once_cell_t lp_tree_Formalism_MainNotions_artNum___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_artNum___redArg___closed__2;
static lean_once_cell_t lp_tree_Formalism_MainNotions_artNum___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_artNum___redArg___closed__3;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_artNum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_artNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_artNum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_wordBits(lean_object* v_D_1_, lean_object* v_u_2_, lean_object* v_l_3_){
_start:
{
lean_object* v_R_4_; lean_object* v_s_5_; lean_object* v_k_6_; lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_R_4_ = lean_ctor_get(v_D_1_, 0);
lean_inc_ref(v_R_4_);
v_s_5_ = lean_ctor_get(v_D_1_, 35);
lean_inc_ref(v_s_5_);
lean_dec_ref(v_D_1_);
v_k_6_ = lean_ctor_get(v_R_4_, 1);
lean_inc(v_k_6_);
lean_dec_ref(v_R_4_);
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lean_nat_sub(v_k_6_, v___x_7_);
lean_dec(v_k_6_);
v___x_9_ = lean_nat_dec_lt(v_l_3_, v___x_8_);
lean_dec(v___x_8_);
if (v___x_9_ == 0)
{
lean_dec_ref(v_s_5_);
lean_dec(v_l_3_);
lean_dec(v_u_2_);
return v___x_9_;
}
else
{
lean_object* v_letter_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_letter_10_ = lean_ctor_get(v_s_5_, 2);
lean_inc_ref(v_letter_10_);
lean_dec_ref(v_s_5_);
v___x_11_ = lean_apply_2(v_letter_10_, v_u_2_, v_l_3_);
v___x_12_ = lean_unbox(v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_wordBits___boxed(lean_object* v_D_13_, lean_object* v_u_14_, lean_object* v_l_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = lp_tree_Formalism_MainNotions_wordBits(v_D_13_, v_u_14_, v_l_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_suppAt___lam__0(lean_object* v_D_18_, lean_object* v_p_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_what_u2082_21_; lean_object* v_places_22_; lean_object* v_resChar_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_what_u2082_21_ = lean_ctor_get(v_D_18_, 4);
lean_inc_ref(v_what_u2082_21_);
lean_dec_ref(v_D_18_);
v_places_22_ = lean_ctor_get(v_what_u2082_21_, 2);
lean_inc_ref(v_places_22_);
lean_dec_ref(v_what_u2082_21_);
v_resChar_23_ = lean_ctor_get(v_places_22_, 2);
lean_inc_ref(v_resChar_23_);
lean_dec_ref(v_places_22_);
v___x_24_ = lean_apply_1(v_resChar_23_, v_a_20_);
v___x_25_ = lean_nat_dec_eq(v___x_24_, v_p_19_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_suppAt___lam__0___boxed(lean_object* v_D_26_, lean_object* v_p_27_, lean_object* v_a_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lp_tree_Formalism_MainNotions_suppAt___lam__0(v_D_26_, v_p_27_, v_a_28_);
lean_dec(v_p_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_suppAt(lean_object* v_D_31_, lean_object* v_L_32_, lean_object* v_p_33_){
_start:
{
lean_object* v_supp_34_; lean_object* v___f_35_; lean_object* v___x_36_; 
v_supp_34_ = lean_ctor_get(v_L_32_, 3);
lean_inc(v_supp_34_);
lean_dec_ref(v_L_32_);
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_suppAt___lam__0___boxed), 3, 2);
lean_closure_set(v___f_35_, 0, v_D_31_);
lean_closure_set(v___f_35_, 1, v_p_33_);
v___x_36_ = lp_mathlib_Multiset_filter___redArg(v___f_35_, v_supp_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals___lam__0(lean_object* v_t_37_){
_start:
{
lean_inc(v_t_37_);
return v_t_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals___lam__0___boxed(lean_object* v_t_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_MainNotions_TTwVals___lam__0(v_t_38_);
lean_dec(v_t_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals___lam__1(lean_object* v_L_40_, lean_object* v___f_41_, lean_object* v_w_42_){
_start:
{
lean_object* v_TTw_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_TTw_43_ = lean_ctor_get(v_L_40_, 17);
lean_inc(v_TTw_43_);
lean_dec_ref(v_L_40_);
v___x_44_ = lean_apply_1(v_TTw_43_, v_w_42_);
v___x_45_ = lp_tree_Finset_image___at___00Formalism_G0_window_spec__0___redArg(v___f_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint8_t lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object* v___x_46_, uint8_t v___x_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_50_ = l_List_decidablePerm___redArg(v___x_49_, v___x_46_, v___y_48_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___x_52_, lean_object* v___x_53_, lean_object* v___y_54_){
_start:
{
uint8_t v___x_312__boxed_55_; uint8_t v_res_56_; lean_object* v_r_57_; 
v___x_312__boxed_55_ = lean_unbox(v___x_53_);
v_res_56_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(v___x_52_, v___x_312__boxed_55_, v___y_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_as_58_, size_t v_i_59_, size_t v_stop_60_, lean_object* v_b_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = lean_usize_dec_eq(v_i_59_, v_stop_60_);
if (v___x_62_ == 0)
{
size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___f_67_; uint8_t v___x_68_; 
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_sub(v_i_59_, v___x_63_);
v___x_65_ = lean_array_uget_borrowed(v_as_58_, v___x_64_);
v___x_66_ = lean_box(v___x_62_);
lean_inc(v___x_65_);
v___f_67_ = lean_alloc_closure((void*)(lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_67_, 0, v___x_65_);
lean_closure_set(v___f_67_, 1, v___x_66_);
lean_inc(v_b_61_);
v___x_68_ = l_List_decidableBAll___redArg(v___f_67_, v_b_61_);
if (v___x_68_ == 0)
{
v_i_59_ = v___x_64_;
goto _start;
}
else
{
lean_object* v___x_70_; 
lean_inc(v___x_65_);
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_65_);
lean_ctor_set(v___x_70_, 1, v_b_61_);
v_i_59_ = v___x_64_;
v_b_61_ = v___x_70_;
goto _start;
}
}
else
{
return v_b_61_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_as_72_, lean_object* v_i_73_, lean_object* v_stop_74_, lean_object* v_b_75_){
_start:
{
size_t v_i_boxed_76_; size_t v_stop_boxed_77_; lean_object* v_res_78_; 
v_i_boxed_76_ = lean_unbox_usize(v_i_73_);
lean_dec(v_i_73_);
v_stop_boxed_77_ = lean_unbox_usize(v_stop_74_);
lean_dec(v_stop_74_);
v_res_78_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_as_72_, v_i_boxed_76_, v_stop_boxed_77_, v_b_75_);
lean_dec_ref(v_as_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_init_79_, lean_object* v_l_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_81_ = lean_array_mk(v_l_80_);
v___x_82_ = lean_array_get_size(v___x_81_);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_nat_dec_lt(v___x_83_, v___x_82_);
if (v___x_84_ == 0)
{
lean_dec_ref(v___x_81_);
return v_init_79_;
}
else
{
size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_usize_of_nat(v___x_82_);
v___x_86_ = ((size_t)0ULL);
v___x_87_ = lp_tree___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v___x_81_, v___x_85_, v___x_86_, v_init_79_);
lean_dec_ref(v___x_81_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_l_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(0);
v___x_90_ = lp_tree_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v___x_89_, v_l_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1(lean_object* v_s_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0(lean_object* v_s_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0___redArg(lean_object* v_f_95_, lean_object* v_s_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lp_mathlib_Multiset_map___redArg(v_f_95_, v_s_96_);
v___x_98_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_TTwVals(lean_object* v_D_100_, lean_object* v_L_101_, lean_object* v_p_102_){
_start:
{
lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___f_103_ = ((lean_object*)(lp_tree_Formalism_MainNotions_TTwVals___closed__0));
lean_inc_ref(v_L_101_);
v___f_104_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_TTwVals___lam__1), 3, 2);
lean_closure_set(v___f_104_, 0, v_L_101_);
lean_closure_set(v___f_104_, 1, v___f_103_);
v___x_105_ = lp_tree_Formalism_MainNotions_suppAt(v_D_100_, v_L_101_, v_p_102_);
v___x_106_ = lp_tree_Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0___redArg(v___f_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0(lean_object* v_00_u03b1_107_, lean_object* v_f_108_, lean_object* v_s_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lp_tree_Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0___redArg(v_f_108_, v_s_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2(lean_object* v_l_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_R_113_, lean_object* v_l_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_tree_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00Formalism_MainNotions_TTwVals_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_114_);
return v___x_115_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__0(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_to_int(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__1(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&lp_tree_Formalism_MainNotions_artNum___redArg___closed__0, &lp_tree_Formalism_MainNotions_artNum___redArg___closed__0_once, _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__0);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__2(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&lp_tree_Formalism_MainNotions_artNum___redArg___closed__1, &lp_tree_Formalism_MainNotions_artNum___redArg___closed__1_once, _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__1);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_obj_once(&lp_tree_Formalism_MainNotions_artNum___redArg___closed__2, &lp_tree_Formalism_MainNotions_artNum___redArg___closed__2_once, _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__2);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_artNum___redArg(lean_object* v_H_125_, lean_object* v_p_126_){
_start:
{
lean_object* v_q_127_; lean_object* v_d_128_; lean_object* v_QS_129_; lean_object* v_art_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_q_127_ = lean_ctor_get(v_H_125_, 0);
lean_inc(v_q_127_);
v_d_128_ = lean_ctor_get(v_H_125_, 1);
lean_inc(v_d_128_);
v_QS_129_ = lean_ctor_get(v_H_125_, 2);
lean_inc(v_QS_129_);
v_art_130_ = lean_ctor_get(v_H_125_, 8);
lean_inc_ref(v_art_130_);
lean_dec_ref(v_H_125_);
v___x_131_ = lean_nat_mul(v_QS_129_, v_q_127_);
lean_dec(v_q_127_);
lean_dec(v_QS_129_);
v___x_132_ = lean_nat_mul(v___x_131_, v_d_128_);
lean_dec(v_d_128_);
lean_dec(v___x_131_);
v___x_133_ = lean_nat_gcd(v_p_126_, v___x_132_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_dec_eq(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
lean_dec(v___x_132_);
lean_dec_ref(v_art_130_);
lean_dec(v_p_126_);
v___x_136_ = lean_obj_once(&lp_tree_Formalism_MainNotions_artNum___redArg___closed__3, &lp_tree_Formalism_MainNotions_artNum___redArg___closed__3_once, _init_lp_tree_Formalism_MainNotions_artNum___redArg___closed__3);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v___x_137_ = lp_mathlib_ZMod_unitOfCoprime___redArg(v___x_132_, v_p_126_);
v___x_138_ = lean_apply_1(v_art_130_, v___x_137_);
v_fst_139_ = lean_ctor_get(v___x_138_, 0);
v_snd_140_ = lean_ctor_get(v___x_138_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v___x_138_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_snd_140_);
lean_inc(v_fst_139_);
lean_dec(v___x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lp_tree_Formalism_HC_Frame_iotaInv___redArg(v_snd_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_144_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_139_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_artNum(lean_object* v_00_u03c6_149_, lean_object* v_H_150_, lean_object* v_p_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lp_tree_Formalism_MainNotions_artNum___redArg(v_H_150_, v_p_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_artNum___boxed(lean_object* v_00_u03c6_153_, lean_object* v_H_154_, lean_object* v_p_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = lp_tree_Formalism_MainNotions_artNum(v_00_u03c6_153_, v_H_154_, v_p_155_);
lean_dec_ref(v_00_u03c6_153_);
return v_res_156_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_DFam(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_FamCore(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_DFam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
