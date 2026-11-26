// Lean compiler output
// Module: Lib.DiscreteSeries.Theta.BlockRule
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Theta.FockDualPair
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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
static lean_once_cell_t lp_GRH_New_doubledBlock___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_doubledBlock___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_doubledBlock___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_doubledBlock___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_doubledBlock___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_doubledBlock(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_doubledBlock_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_centredBlock___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_centredBlock___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_centredBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_doubledBlock___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_doubledBlock___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_doubledBlock___lam__0(lean_object* v_d_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_7_ = lean_nat_to_int(v_d_5_);
v___x_8_ = lean_obj_once(&lp_GRH_New_doubledBlock___lam__0___closed__0, &lp_GRH_New_doubledBlock___lam__0___closed__0_once, _init_lp_GRH_New_doubledBlock___lam__0___closed__0);
v___x_9_ = lean_int_sub(v___x_7_, v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_obj_once(&lp_GRH_New_doubledBlock___lam__0___closed__1, &lp_GRH_New_doubledBlock___lam__0___closed__1_once, _init_lp_GRH_New_doubledBlock___lam__0___closed__1);
v___x_11_ = lean_nat_to_int(v_b_6_);
v___x_12_ = lean_int_mul(v___x_10_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_int_sub(v___x_9_, v___x_12_);
lean_dec(v___x_12_);
lean_dec(v___x_9_);
return v___x_13_;
}
}
LEAN_EXPORT uint8_t lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object* v___x_14_, uint8_t v___x_15_, lean_object* v___y_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_int_dec_eq(v___x_14_, v___y_16_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 1;
return v___x_18_;
}
else
{
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___x_19_, lean_object* v___x_20_, lean_object* v___y_21_){
_start:
{
uint8_t v___x_351__boxed_22_; uint8_t v_res_23_; lean_object* v_r_24_; 
v___x_351__boxed_22_ = lean_unbox(v___x_20_);
v_res_23_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(v___x_19_, v___x_351__boxed_22_, v___y_21_);
lean_dec(v___y_21_);
lean_dec(v___x_19_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_as_25_, size_t v_i_26_, size_t v_stop_27_, lean_object* v_b_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_usize_dec_eq(v_i_26_, v_stop_27_);
if (v___x_29_ == 0)
{
size_t v___x_30_; size_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___f_34_; uint8_t v___x_35_; 
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_sub(v_i_26_, v___x_30_);
v___x_32_ = lean_array_uget_borrowed(v_as_25_, v___x_31_);
v___x_33_ = lean_box(v___x_29_);
lean_inc(v___x_32_);
v___f_34_ = lean_alloc_closure((void*)(lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_34_, 0, v___x_32_);
lean_closure_set(v___f_34_, 1, v___x_33_);
lean_inc(v_b_28_);
v___x_35_ = l_List_decidableBAll___redArg(v___f_34_, v_b_28_);
if (v___x_35_ == 0)
{
v_i_26_ = v___x_31_;
goto _start;
}
else
{
lean_object* v___x_37_; 
lean_inc(v___x_32_);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_32_);
lean_ctor_set(v___x_37_, 1, v_b_28_);
v_i_26_ = v___x_31_;
v_b_28_ = v___x_37_;
goto _start;
}
}
else
{
return v_b_28_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_as_39_, lean_object* v_i_40_, lean_object* v_stop_41_, lean_object* v_b_42_){
_start:
{
size_t v_i_boxed_43_; size_t v_stop_boxed_44_; lean_object* v_res_45_; 
v_i_boxed_43_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_stop_boxed_44_ = lean_unbox_usize(v_stop_41_);
lean_dec(v_stop_41_);
v_res_45_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_as_39_, v_i_boxed_43_, v_stop_boxed_44_, v_b_42_);
lean_dec_ref(v_as_39_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_init_46_, lean_object* v_l_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_48_ = lean_array_mk(v_l_47_);
v___x_49_ = lean_array_get_size(v___x_48_);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_nat_dec_lt(v___x_50_, v___x_49_);
if (v___x_51_ == 0)
{
lean_dec_ref(v___x_48_);
return v_init_46_;
}
else
{
size_t v___x_52_; size_t v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_usize_of_nat(v___x_49_);
v___x_53_ = ((size_t)0ULL);
v___x_54_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v___x_48_, v___x_52_, v___x_53_, v_init_46_);
lean_dec_ref(v___x_48_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_l_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_box(0);
v___x_57_ = lp_GRH_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v___x_56_, v_l_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1(lean_object* v_s_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0(lean_object* v_s_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(lean_object* v_f_62_, lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lp_mathlib_Multiset_map___redArg(v_f_62_, v_s_63_);
v___x_65_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_doubledBlock(lean_object* v_d_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc(v_d_66_);
v___f_67_ = lean_alloc_closure((void*)(lp_GRH_New_doubledBlock___lam__0), 2, 1);
lean_closure_set(v___f_67_, 0, v_d_66_);
v___x_68_ = l_List_range(v_d_66_);
v___x_69_ = lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(v___f_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_doubledBlock_spec__0(lean_object* v_00_u03b1_70_, lean_object* v_f_71_, lean_object* v_s_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(v_f_71_, v_s_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2(lean_object* v_l_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_R_76_, lean_object* v_l_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_centredBlock___lam__0(lean_object* v_e_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&lp_GRH_New_doubledBlock___lam__0___closed__1, &lp_GRH_New_doubledBlock___lam__0___closed__1_once, _init_lp_GRH_New_doubledBlock___lam__0___closed__1);
v___x_82_ = lean_int_mul(v___x_81_, v_e_79_);
v___x_83_ = lean_int_add(v___x_82_, v_x_80_);
lean_dec(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_centredBlock___lam__0___boxed(lean_object* v_e_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_centredBlock___lam__0(v_e_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec(v_e_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_centredBlock(lean_object* v_e_87_, lean_object* v_d_88_){
_start:
{
lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___f_89_ = lean_alloc_closure((void*)(lp_GRH_New_centredBlock___lam__0___boxed), 2, 1);
lean_closure_set(v___f_89_, 0, v_e_87_);
v___x_90_ = lp_GRH_New_doubledBlock(v_d_88_);
v___x_91_ = lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(v___f_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry___redArg(lean_object* v_00_u03b3_92_, lean_object* v_m_93_, lean_object* v_l_94_, lean_object* v_i_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_96_ = lean_apply_1(v_l_94_, v_i_95_);
v___x_97_ = lean_obj_once(&lp_GRH_New_doubledBlock___lam__0___closed__1, &lp_GRH_New_doubledBlock___lam__0___closed__1_once, _init_lp_GRH_New_doubledBlock___lam__0___closed__1);
v___x_98_ = lean_int_mul(v___x_97_, v_00_u03b3_92_);
v___x_99_ = lean_int_sub(v___x_96_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_96_);
v___x_100_ = lean_nat_to_int(v_m_93_);
v___x_101_ = lean_int_add(v___x_99_, v___x_100_);
lean_dec(v___x_100_);
lean_dec(v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry___redArg___boxed(lean_object* v_00_u03b3_102_, lean_object* v_m_103_, lean_object* v_l_104_, lean_object* v_i_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_GRH_New_shiftedEntry___redArg(v_00_u03b3_102_, v_m_103_, v_l_104_, v_i_105_);
lean_dec(v_00_u03b3_102_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry(lean_object* v_00_u03b9_107_, lean_object* v_00_u03b3_108_, lean_object* v_m_109_, lean_object* v_l_110_, lean_object* v_i_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_GRH_New_shiftedEntry___redArg(v_00_u03b3_108_, v_m_109_, v_l_110_, v_i_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_shiftedEntry___boxed(lean_object* v_00_u03b9_113_, lean_object* v_00_u03b3_114_, lean_object* v_m_115_, lean_object* v_l_116_, lean_object* v_i_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_GRH_New_shiftedEntry(v_00_u03b9_113_, v_00_u03b3_114_, v_m_115_, v_l_116_, v_i_117_);
lean_dec(v_00_u03b3_114_);
return v_res_118_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_FockDualPair(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_BlockRule(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_Theta_FockDualPair(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
