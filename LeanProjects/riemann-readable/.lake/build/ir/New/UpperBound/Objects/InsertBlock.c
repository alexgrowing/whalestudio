// Lean compiler output
// Module: New.UpperBound.Objects.InsertBlock
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Theta.BlockRule
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
lean_object* lp_GRH_New_centredBlock(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Additive_ofMul___redArg();
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lp_mathlib_Additive_toMul___redArg();
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_bind___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_block___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_block(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_ndunion___at___00New_CentreSystem_entries_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_entries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_entries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_rank___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_rank___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_rank(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_CentreSystem_lowering___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_lowering___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_CentreSystem_lowering___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_lowering___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0;
LEAN_EXPORT uint8_t lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_CentreSystem_instDecidableCountsFor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_instDecidableCountsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_CentreSystem_sign___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_sign___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_CentreSystem_sign___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_sign___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_CentreSystem_sign___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_sign___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_CentreSystem_sign___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_sign___redArg___closed__2;
static lean_once_cell_t lp_GRH_New_CentreSystem_sign___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_CentreSystem_sign___redArg___closed__3;
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_sign___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_sign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_block___redArg(lean_object* v_X_1_, lean_object* v_c_2_){
_start:
{
lean_object* v_centre_3_; lean_object* v_length_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_centre_3_ = lean_ctor_get(v_X_1_, 1);
lean_inc_ref(v_centre_3_);
v_length_4_ = lean_ctor_get(v_X_1_, 2);
lean_inc_ref(v_length_4_);
lean_dec_ref(v_X_1_);
lean_inc(v_c_2_);
v___x_5_ = lean_apply_1(v_centre_3_, v_c_2_);
v___x_6_ = lean_apply_1(v_length_4_, v_c_2_);
v___x_7_ = lp_GRH_New_centredBlock(v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_block(lean_object* v_00_u03b9_8_, lean_object* v_X_9_, lean_object* v_c_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_GRH_New_CentreSystem_block___redArg(v_X_9_, v_c_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg___lam__0(lean_object* v_t_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_1(v_t_12_, v_a_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg(lean_object* v_s_15_, lean_object* v_t_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_17_ = lean_alloc_closure((void*)(lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_17_, 0, v_t_16_);
v___x_18_ = lp_mathlib_Multiset_bind___redArg(v_s_15_, v___f_17_);
v___x_19_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_doubledBlock_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__1(lean_object* v_a_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
else
{
lean_object* v_head_23_; lean_object* v_tail_24_; uint8_t v___x_25_; 
v_head_23_ = lean_ctor_get(v_x_21_, 0);
v_tail_24_ = lean_ctor_get(v_x_21_, 1);
v___x_25_ = lean_int_dec_eq(v_a_20_, v_head_23_);
if (v___x_25_ == 0)
{
v_x_21_ = v_tail_24_;
goto _start;
}
else
{
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__1___boxed(lean_object* v_a_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lp_GRH_List_elem___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__1(v_a_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec(v_a_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2_spec__3(lean_object* v_as_31_, size_t v_i_32_, size_t v_stop_33_, lean_object* v_b_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_usize_dec_eq(v_i_32_, v_stop_33_);
if (v___x_35_ == 0)
{
size_t v___x_36_; size_t v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_sub(v_i_32_, v___x_36_);
v___x_38_ = lean_array_uget_borrowed(v_as_31_, v___x_37_);
v___x_39_ = lp_GRH_List_elem___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__1(v___x_38_, v_b_34_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_inc(v___x_38_);
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v_b_34_);
v_i_32_ = v___x_37_;
v_b_34_ = v___x_40_;
goto _start;
}
else
{
v_i_32_ = v___x_37_;
goto _start;
}
}
else
{
return v_b_34_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2_spec__3___boxed(lean_object* v_as_43_, lean_object* v_i_44_, lean_object* v_stop_45_, lean_object* v_b_46_){
_start:
{
size_t v_i_boxed_47_; size_t v_stop_boxed_48_; lean_object* v_res_49_; 
v_i_boxed_47_ = lean_unbox_usize(v_i_44_);
lean_dec(v_i_44_);
v_stop_boxed_48_ = lean_unbox_usize(v_stop_45_);
lean_dec(v_stop_45_);
v_res_49_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2_spec__3(v_as_43_, v_i_boxed_47_, v_stop_boxed_48_, v_b_46_);
lean_dec_ref(v_as_43_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2(lean_object* v_init_50_, lean_object* v_l_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_52_ = lean_array_mk(v_l_51_);
v___x_53_ = lean_array_get_size(v___x_52_);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_nat_dec_lt(v___x_54_, v___x_53_);
if (v___x_55_ == 0)
{
lean_dec_ref(v___x_52_);
return v_init_50_;
}
else
{
size_t v___x_56_; size_t v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_usize_of_nat(v___x_53_);
v___x_57_ = ((size_t)0ULL);
v___x_58_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2_spec__3(v___x_52_, v___x_56_, v___x_57_, v_init_50_);
lean_dec_ref(v___x_52_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_ndunion___at___00New_CentreSystem_entries_spec__1(lean_object* v_s_59_, lean_object* v_t_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2(v_t_60_, v_s_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_entries___redArg(lean_object* v_X_62_, lean_object* v_B_63_){
_start:
{
lean_object* v_stem_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_stem_64_ = lean_ctor_get(v_X_62_, 4);
lean_inc(v_stem_64_);
v___x_65_ = lean_alloc_closure((void*)(lp_GRH_New_CentreSystem_block), 3, 2);
lean_closure_set(v___x_65_, 0, lean_box(0));
lean_closure_set(v___x_65_, 1, v_X_62_);
v___x_66_ = lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg(v_B_63_, v___x_65_);
v___x_67_ = lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_CentreSystem_entries_spec__1_spec__2(v___x_66_, v_stem_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_entries(lean_object* v_00_u03b9_68_, lean_object* v_X_69_, lean_object* v_B_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_GRH_New_CentreSystem_entries___redArg(v_X_69_, v_B_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0(lean_object* v_00_u03b1_72_, lean_object* v_s_73_, lean_object* v_t_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_GRH_Finset_biUnion___at___00New_CentreSystem_entries_spec__0___redArg(v_s_73_, v_t_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_rank___redArg___lam__0(lean_object* v_length_76_, lean_object* v_c_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_apply_1(v_length_76_, v_c_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_rank___redArg(lean_object* v_X_79_, lean_object* v_B_80_){
_start:
{
lean_object* v_length_81_; lean_object* v_stem_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_length_81_ = lean_ctor_get(v_X_79_, 2);
lean_inc_ref(v_length_81_);
v_stem_82_ = lean_ctor_get(v_X_79_, 4);
lean_inc(v_stem_82_);
lean_dec_ref(v_X_79_);
v___f_83_ = lean_alloc_closure((void*)(lp_GRH_New_CentreSystem_rank___redArg___lam__0), 2, 1);
lean_closure_set(v___f_83_, 0, v_length_81_);
v___x_84_ = l_List_lengthTR___redArg(v_stem_82_);
lean_dec(v_stem_82_);
v___x_85_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v_B_80_, v___f_83_);
v___x_86_ = lean_nat_add(v___x_84_, v___x_85_);
lean_dec(v___x_85_);
lean_dec(v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_rank(lean_object* v_00_u03b9_87_, lean_object* v_X_88_, lean_object* v_B_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lp_GRH_New_CentreSystem_rank___redArg(v_X_88_, v_B_89_);
return v___x_90_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_lowering___redArg___closed__0(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_lowering___redArg___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering___redArg(lean_object* v_X_95_, lean_object* v_B_96_){
_start:
{
lean_object* v_stem_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_stem_99_ = lean_ctor_get(v_X_95_, 4);
v___x_100_ = l_List_lengthTR___redArg(v_stem_99_);
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_mod(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_dec_eq(v___x_102_, v___x_103_);
lean_dec(v___x_102_);
if (v___x_104_ == 0)
{
goto v___jp_97_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = l_List_lengthTR___redArg(v_B_96_);
v___x_106_ = lean_nat_mod(v___x_105_, v___x_101_);
lean_dec(v___x_105_);
v___x_107_ = lean_nat_dec_eq(v___x_106_, v___x_103_);
lean_dec(v___x_106_);
if (v___x_107_ == 0)
{
goto v___jp_97_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&lp_GRH_New_CentreSystem_lowering___redArg___closed__1, &lp_GRH_New_CentreSystem_lowering___redArg___closed__1_once, _init_lp_GRH_New_CentreSystem_lowering___redArg___closed__1);
return v___x_108_;
}
}
v___jp_97_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&lp_GRH_New_CentreSystem_lowering___redArg___closed__0, &lp_GRH_New_CentreSystem_lowering___redArg___closed__0_once, _init_lp_GRH_New_CentreSystem_lowering___redArg___closed__0);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering___redArg___boxed(lean_object* v_X_109_, lean_object* v_B_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_GRH_New_CentreSystem_lowering___redArg(v_X_109_, v_B_110_);
lean_dec(v_B_110_);
lean_dec_ref(v_X_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering(lean_object* v_00_u03b9_112_, lean_object* v_X_113_, lean_object* v_B_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_GRH_New_CentreSystem_lowering___redArg(v_X_113_, v_B_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_lowering___boxed(lean_object* v_00_u03b9_116_, lean_object* v_X_117_, lean_object* v_B_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_GRH_New_CentreSystem_lowering(v_00_u03b9_116_, v_X_117_, v_B_118_);
lean_dec(v_B_118_);
lean_dec_ref(v_X_117_);
return v_res_119_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg(lean_object* v_X_122_, lean_object* v_c_123_, lean_object* v_y_124_){
_start:
{
lean_object* v_centre_125_; lean_object* v_isUp_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_centre_125_ = lean_ctor_get(v_X_122_, 1);
lean_inc_ref(v_centre_125_);
v_isUp_126_ = lean_ctor_get(v_X_122_, 3);
lean_inc_ref(v_isUp_126_);
lean_dec_ref(v_X_122_);
lean_inc(v_c_123_);
v___x_127_ = lean_apply_1(v_isUp_126_, v_c_123_);
v___x_128_ = lean_unbox(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_129_ = lean_obj_once(&lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0, &lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0_once, _init_lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0);
v___x_130_ = lean_apply_1(v_centre_125_, v_c_123_);
v___x_131_ = lean_int_mul(v___x_129_, v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_int_dec_lt(v_y_124_, v___x_131_);
lean_dec(v___x_131_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = lean_obj_once(&lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0, &lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0_once, _init_lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___closed__0);
v___x_134_ = lean_apply_1(v_centre_125_, v_c_123_);
v___x_135_ = lean_int_mul(v___x_133_, v___x_134_);
lean_dec(v___x_134_);
v___x_136_ = lean_int_dec_lt(v___x_135_, v_y_124_);
lean_dec(v___x_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg___boxed(lean_object* v_X_137_, lean_object* v_c_138_, lean_object* v_y_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg(v_X_137_, v_c_138_, v_y_139_);
lean_dec(v_y_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_CentreSystem_instDecidableCountsFor(lean_object* v_00_u03b9_142_, lean_object* v_X_143_, lean_object* v_c_144_, lean_object* v_y_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg(v_X_143_, v_c_144_, v_y_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_instDecidableCountsFor___boxed(lean_object* v_00_u03b9_147_, lean_object* v_X_148_, lean_object* v_c_149_, lean_object* v_y_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = lp_GRH_New_CentreSystem_instDecidableCountsFor(v_00_u03b9_147_, v_X_148_, v_c_149_, v_y_150_);
lean_dec(v_y_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_CentreSystem_sign___redArg___lam__0(lean_object* v_X_153_, lean_object* v_y_154_, lean_object* v_a_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lp_GRH_New_CentreSystem_instDecidableCountsFor___redArg(v_X_153_, v_a_155_, v_y_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_sign___redArg___lam__0___boxed(lean_object* v_X_157_, lean_object* v_y_158_, lean_object* v_a_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = lp_GRH_New_CentreSystem_sign___redArg___lam__0(v_X_157_, v_y_158_, v_a_159_);
lean_dec(v_y_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_sign___redArg___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&lp_GRH_New_CentreSystem_lowering___redArg___closed__1, &lp_GRH_New_CentreSystem_lowering___redArg___closed__1_once, _init_lp_GRH_New_CentreSystem_lowering___redArg___closed__1);
v___x_163_ = lean_int_neg(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_sign___redArg___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_obj_once(&lp_GRH_New_CentreSystem_sign___redArg___closed__0, &lp_GRH_New_CentreSystem_sign___redArg___closed__0_once, _init_lp_GRH_New_CentreSystem_sign___redArg___closed__0);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_sign___redArg___closed__2(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lp_mathlib_Additive_ofMul___redArg();
return v___x_166_;
}
}
static lean_object* _init_lp_GRH_New_CentreSystem_sign___redArg___closed__3(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lp_mathlib_Additive_toMul___redArg();
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_sign___redArg(lean_object* v_inst_168_, lean_object* v_X_169_, lean_object* v_B_170_, lean_object* v_y_171_){
_start:
{
lean_object* v___x_172_; lean_object* v_centres_173_; lean_object* v___x_174_; lean_object* v_toFun_175_; lean_object* v___x_176_; lean_object* v_toFun_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_val_180_; lean_object* v_inv_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_196_; 
v___x_172_ = lean_obj_once(&lp_GRH_New_CentreSystem_sign___redArg___closed__1, &lp_GRH_New_CentreSystem_sign___redArg___closed__1_once, _init_lp_GRH_New_CentreSystem_sign___redArg___closed__1);
v_centres_173_ = lean_ctor_get(v_X_169_, 0);
lean_inc(v_centres_173_);
v___x_174_ = lean_obj_once(&lp_GRH_New_CentreSystem_sign___redArg___closed__2, &lp_GRH_New_CentreSystem_sign___redArg___closed__2_once, _init_lp_GRH_New_CentreSystem_sign___redArg___closed__2);
v_toFun_175_ = lean_ctor_get(v___x_174_, 0);
v___x_176_ = lean_obj_once(&lp_GRH_New_CentreSystem_sign___redArg___closed__3, &lp_GRH_New_CentreSystem_sign___redArg___closed__3_once, _init_lp_GRH_New_CentreSystem_sign___redArg___closed__3);
v_toFun_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_toFun_175_);
v___x_178_ = lean_apply_1(v_toFun_175_, v___x_172_);
lean_inc(v_toFun_177_);
v___x_179_ = lean_apply_1(v_toFun_177_, v___x_178_);
v_val_180_ = lean_ctor_get(v___x_179_, 0);
v_inv_181_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_196_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_196_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_inv_181_);
lean_inc(v_val_180_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_196_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___f_185_ = lean_alloc_closure((void*)(lp_GRH_New_CentreSystem_sign___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_185_, 0, v_X_169_);
lean_closure_set(v___f_185_, 1, v_y_171_);
v___x_186_ = lp_mathlib_Multiset_sub___redArg(v_inst_168_, v_centres_173_, v_B_170_);
v___x_187_ = lp_mathlib_Multiset_filter___redArg(v___f_185_, v___x_186_);
v___x_188_ = l_List_lengthTR___redArg(v___x_187_);
lean_dec(v___x_187_);
v___x_189_ = l_Int_pow(v_val_180_, v___x_188_);
lean_dec(v_val_180_);
v___x_190_ = l_Int_pow(v_inv_181_, v___x_188_);
lean_dec(v___x_188_);
lean_dec(v_inv_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_190_);
lean_ctor_set(v___x_183_, 0, v___x_189_);
v___x_192_ = v___x_183_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_195_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_inc(v_toFun_175_);
v___x_193_ = lean_apply_1(v_toFun_175_, v___x_192_);
lean_inc(v_toFun_177_);
v___x_194_ = lean_apply_1(v_toFun_177_, v___x_193_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CentreSystem_sign(lean_object* v_00_u03b9_197_, lean_object* v_inst_198_, lean_object* v_X_199_, lean_object* v_B_200_, lean_object* v_y_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lp_GRH_New_CentreSystem_sign___redArg(v_inst_198_, v_X_199_, v_B_200_, v_y_201_);
return v___x_202_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Theta_BlockRule(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_InsertBlock(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Theta_BlockRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
