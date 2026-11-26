// Lean compiler output
// Module: New.Determinant.AuxiliaryForms.GridPaths
// Imports: public import Init public meta import Init public import Lib.Base
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
lean_object* lp_mathlib_Nat_decreasingInduction___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_List_foldrTR___at___00Multiset_ndunion___at___00YoungDiagram_cellsOfRowLens_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Prod_swap(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_nil_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_down_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_down_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_down_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_right_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_right_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_right_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_GridPath_column___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_GridPath_column___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_GridPath_column___redArg___closed__0 = (const lean_object*)&lp_GRH_New_GridPath_column___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_row(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_row___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_squares___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_squares(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_squares___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_first___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_first___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_first(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_last___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_last___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_last(lean_object*);
LEAN_EXPORT uint8_t lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_TwoGridPath_squares_spec__0___redArg(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_TwoGridPath_squares___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Prod_swap, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_TwoGridPath_squares___redArg___closed__0 = (const lean_object*)&lp_GRH_New_TwoGridPath_squares___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_squares___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_squares(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_squares___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_TwoGridPath_squares_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GRH_New_GridPath_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx(lean_object* v_a_u2080_7_, lean_object* v_b_u2080_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_GRH_New_GridPath_ctorIdx___redArg(v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorIdx___boxed(lean_object* v_a_u2080_13_, lean_object* v_b_u2080_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_GridPath_ctorIdx(v_a_u2080_13_, v_b_u2080_14_, v_a_15_, v_a_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec(v_a_16_);
lean_dec(v_a_15_);
lean_dec(v_b_u2080_14_);
lean_dec(v_a_u2080_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorElim___redArg(lean_object* v_t_19_, lean_object* v_k_20_){
_start:
{
if (lean_obj_tag(v_t_19_) == 0)
{
return v_k_20_;
}
else
{
lean_object* v_a_21_; lean_object* v_b_22_; lean_object* v_p_23_; lean_object* v___x_24_; 
v_a_21_ = lean_ctor_get(v_t_19_, 0);
lean_inc(v_a_21_);
v_b_22_ = lean_ctor_get(v_t_19_, 1);
lean_inc(v_b_22_);
v_p_23_ = lean_ctor_get(v_t_19_, 2);
lean_inc(v_p_23_);
lean_dec(v_t_19_);
v___x_24_ = lean_apply_3(v_k_20_, v_a_21_, v_b_22_, v_p_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorElim(lean_object* v_a_u2080_25_, lean_object* v_b_u2080_26_, lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_31_, v_k_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_ctorElim___boxed(lean_object* v_a_u2080_35_, lean_object* v_b_u2080_36_, lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_k_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_GridPath_ctorElim(v_a_u2080_35_, v_b_u2080_36_, v_motive_37_, v_ctorIdx_38_, v_a_39_, v_a_40_, v_t_41_, v_h_42_, v_k_43_);
lean_dec(v_a_40_);
lean_dec(v_a_39_);
lean_dec(v_ctorIdx_38_);
lean_dec(v_b_u2080_36_);
lean_dec(v_a_u2080_35_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_nil_elim___redArg(lean_object* v_t_45_, lean_object* v_nil_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_45_, v_nil_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_nil_elim(lean_object* v_a_u2080_48_, lean_object* v_b_u2080_49_, lean_object* v_motive_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_nil_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_53_, v_nil_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_nil_elim___boxed(lean_object* v_a_u2080_57_, lean_object* v_b_u2080_58_, lean_object* v_motive_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_nil_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_GRH_New_GridPath_nil_elim(v_a_u2080_57_, v_b_u2080_58_, v_motive_59_, v_a_60_, v_a_61_, v_t_62_, v_h_63_, v_nil_64_);
lean_dec(v_a_61_);
lean_dec(v_a_60_);
lean_dec(v_b_u2080_58_);
lean_dec(v_a_u2080_57_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_down_elim___redArg(lean_object* v_t_66_, lean_object* v_down_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_66_, v_down_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_down_elim(lean_object* v_a_u2080_69_, lean_object* v_b_u2080_70_, lean_object* v_motive_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_down_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_74_, v_down_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_down_elim___boxed(lean_object* v_a_u2080_78_, lean_object* v_b_u2080_79_, lean_object* v_motive_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_down_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_GridPath_down_elim(v_a_u2080_78_, v_b_u2080_79_, v_motive_80_, v_a_81_, v_a_82_, v_t_83_, v_h_84_, v_down_85_);
lean_dec(v_a_82_);
lean_dec(v_a_81_);
lean_dec(v_b_u2080_79_);
lean_dec(v_a_u2080_78_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_right_elim___redArg(lean_object* v_t_87_, lean_object* v_right_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_87_, v_right_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_right_elim(lean_object* v_a_u2080_90_, lean_object* v_b_u2080_91_, lean_object* v_motive_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_right_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lp_GRH_New_GridPath_ctorElim___redArg(v_t_95_, v_right_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_right_elim___boxed(lean_object* v_a_u2080_99_, lean_object* v_b_u2080_100_, lean_object* v_motive_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_right_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_GRH_New_GridPath_right_elim(v_a_u2080_99_, v_b_u2080_100_, v_motive_101_, v_a_102_, v_a_103_, v_t_104_, v_h_105_, v_right_106_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec(v_b_u2080_100_);
lean_dec(v_a_u2080_99_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append___redArg(lean_object* v_p_108_, lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
lean_dec(v_x_110_);
lean_dec(v_x_109_);
lean_inc(v_p_108_);
return v_p_108_;
}
case 1:
{
lean_object* v_p_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_122_; 
v_p_112_ = lean_ctor_get(v_x_111_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_111_);
if (v_isSharedCheck_122_ == 0)
{
lean_object* v_unused_123_; lean_object* v_unused_124_; 
v_unused_123_ = lean_ctor_get(v_x_111_, 1);
lean_dec(v_unused_123_);
v_unused_124_ = lean_ctor_get(v_x_111_, 0);
lean_dec(v_unused_124_);
v___x_114_ = v_x_111_;
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_p_112_);
lean_dec(v_x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_x_110_, v___x_116_);
lean_inc(v_x_109_);
v___x_118_ = lp_GRH_New_GridPath_append___redArg(v_p_108_, v_x_109_, v___x_117_, v_p_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 2, v___x_118_);
lean_ctor_set(v___x_114_, 1, v_x_110_);
lean_ctor_set(v___x_114_, 0, v_x_109_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_109_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_110_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
default: 
{
lean_object* v_a_125_; lean_object* v_p_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_x_109_);
v_a_125_ = lean_ctor_get(v_x_111_, 0);
v_p_126_ = lean_ctor_get(v_x_111_, 2);
v_isSharedCheck_134_ = !lean_is_exclusive(v_x_111_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_x_111_, 1);
lean_dec(v_unused_135_);
v___x_128_ = v_x_111_;
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_p_126_);
lean_inc(v_a_125_);
lean_dec(v_x_111_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_inc(v_x_110_);
lean_inc(v_a_125_);
v___x_130_ = lp_GRH_New_GridPath_append___redArg(v_p_108_, v_a_125_, v_x_110_, v_p_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 2, v___x_130_);
lean_ctor_set(v___x_128_, 1, v_x_110_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_125_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_x_110_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append___redArg___boxed(lean_object* v_p_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_GRH_New_GridPath_append___redArg(v_p_136_, v_x_137_, v_x_138_, v_x_139_);
lean_dec(v_p_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append(lean_object* v_a_u2080_141_, lean_object* v_b_u2080_142_, lean_object* v_a_143_, lean_object* v_b_144_, lean_object* v_p_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lp_GRH_New_GridPath_append___redArg(v_p_145_, v_x_146_, v_x_147_, v_x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_append___boxed(lean_object* v_a_u2080_150_, lean_object* v_b_u2080_151_, lean_object* v_a_152_, lean_object* v_b_153_, lean_object* v_p_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = lp_GRH_New_GridPath_append(v_a_u2080_150_, v_b_u2080_151_, v_a_152_, v_b_153_, v_p_154_, v_x_155_, v_x_156_, v_x_157_);
lean_dec(v_p_154_);
lean_dec(v_b_153_);
lean_dec(v_a_152_);
lean_dec(v_b_u2080_151_);
lean_dec(v_a_u2080_150_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___redArg___lam__0(lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_p_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_x_159_);
lean_ctor_set(v___x_163_, 2, v_p_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___redArg(lean_object* v_b_165_, lean_object* v_m_166_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___f_167_ = ((lean_object*)(lp_GRH_New_GridPath_column___redArg___closed__0));
v___x_168_ = lean_box(0);
v___x_169_ = lp_mathlib_Nat_decreasingInduction___redArg(v_m_166_, v___f_167_, v___x_168_, v_b_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___redArg___boxed(lean_object* v_b_170_, lean_object* v_m_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = lp_GRH_New_GridPath_column___redArg(v_b_170_, v_m_171_);
lean_dec(v_m_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column(lean_object* v_b_173_, lean_object* v_m_174_, lean_object* v_hb_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lp_GRH_New_GridPath_column___redArg(v_b_173_, v_m_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_column___boxed(lean_object* v_b_177_, lean_object* v_m_178_, lean_object* v_hb_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_GRH_New_GridPath_column(v_b_177_, v_m_178_, v_hb_179_);
lean_dec(v_m_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_row(lean_object* v_m_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_zero_183_; uint8_t v_isZero_184_; 
v_zero_183_ = lean_unsigned_to_nat(0u);
v_isZero_184_ = lean_nat_dec_eq(v_x_182_, v_zero_183_);
if (v_isZero_184_ == 1)
{
lean_object* v___x_185_; 
lean_dec(v_m_181_);
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v_one_186_; lean_object* v_n_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_one_186_ = lean_unsigned_to_nat(1u);
v_n_187_ = lean_nat_sub(v_x_182_, v_one_186_);
lean_inc(v_m_181_);
v___x_188_ = lp_GRH_New_GridPath_row(v_m_181_, v_n_187_);
v___x_189_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_189_, 0, v_n_187_);
lean_ctor_set(v___x_189_, 1, v_m_181_);
lean_ctor_set(v___x_189_, 2, v___x_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_row___boxed(lean_object* v_m_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lp_GRH_New_GridPath_row(v_m_190_, v_x_191_);
lean_dec(v_x_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_squares___redArg(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
switch(lean_obj_tag(v_x_195_))
{
case 0:
{
lean_object* v___x_196_; 
lean_dec(v_x_194_);
lean_dec(v_x_193_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
case 1:
{
lean_object* v_p_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_p_197_ = lean_ctor_get(v_x_195_, 2);
lean_inc(v_p_197_);
lean_dec_ref_known(v_x_195_, 3);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_x_194_, v___x_198_);
lean_inc(v_x_193_);
v___x_200_ = lp_GRH_New_GridPath_squares___redArg(v_x_193_, v___x_199_, v_p_197_);
v___x_201_ = l_List_range(v_x_193_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v_x_194_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lp_mathlib_Multiset_product___redArg(v___x_201_, v___x_203_);
v___x_205_ = lp_mathlib_List_foldrTR___at___00Multiset_ndunion___at___00YoungDiagram_cellsOfRowLens_spec__0_spec__1(v___x_204_, v___x_200_);
return v___x_205_;
}
default: 
{
lean_object* v_a_206_; lean_object* v_p_207_; 
lean_dec(v_x_193_);
v_a_206_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_a_206_);
v_p_207_ = lean_ctor_get(v_x_195_, 2);
lean_inc(v_p_207_);
lean_dec_ref_known(v_x_195_, 3);
v_x_193_ = v_a_206_;
v_x_195_ = v_p_207_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_squares(lean_object* v_a_u2080_209_, lean_object* v_b_u2080_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lp_GRH_New_GridPath_squares___redArg(v_x_211_, v_x_212_, v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_squares___boxed(lean_object* v_a_u2080_215_, lean_object* v_b_u2080_216_, lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = lp_GRH_New_GridPath_squares(v_a_u2080_215_, v_b_u2080_216_, v_x_217_, v_x_218_, v_x_219_);
lean_dec(v_b_u2080_216_);
lean_dec(v_a_u2080_215_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___redArg(lean_object* v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_){
_start:
{
lean_object* v_zero_224_; uint8_t v_isZero_225_; 
v_zero_224_ = lean_unsigned_to_nat(0u);
v_isZero_225_ = lean_nat_dec_eq(v_x_221_, v_zero_224_);
if (v_isZero_225_ == 1)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v_h__2_223_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_apply_1(v_h__1_222_, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v_one_228_; lean_object* v_n_229_; lean_object* v___x_230_; 
lean_dec(v_h__1_222_);
v_one_228_ = lean_unsigned_to_nat(1u);
v_n_229_ = lean_nat_sub(v_x_221_, v_one_228_);
v___x_230_ = lean_apply_1(v_h__2_223_, v_n_229_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___redArg___boxed(lean_object* v_x_231_, lean_object* v_h__1_232_, lean_object* v_h__2_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___redArg(v_x_231_, v_h__1_232_, v_h__2_233_);
lean_dec(v_x_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter(lean_object* v_motive_235_, lean_object* v_x_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
lean_object* v_zero_239_; uint8_t v_isZero_240_; 
v_zero_239_ = lean_unsigned_to_nat(0u);
v_isZero_240_ = lean_nat_dec_eq(v_x_236_, v_zero_239_);
if (v_isZero_240_ == 1)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_h__2_238_);
v___x_241_ = lean_box(0);
v___x_242_ = lean_apply_1(v_h__1_237_, v___x_241_);
return v___x_242_;
}
else
{
lean_object* v_one_243_; lean_object* v_n_244_; lean_object* v___x_245_; 
lean_dec(v_h__1_237_);
v_one_243_ = lean_unsigned_to_nat(1u);
v_n_244_ = lean_nat_sub(v_x_236_, v_one_243_);
v___x_245_ = lean_apply_1(v_h__2_238_, v_n_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter___boxed(lean_object* v_motive_246_, lean_object* v_x_247_, lean_object* v_h__1_248_, lean_object* v_h__2_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_row_match__1_splitter(v_motive_246_, v_x_247_, v_h__1_248_, v_h__2_249_);
lean_dec(v_x_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter___redArg(lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_, lean_object* v_h__3_256_){
_start:
{
switch(lean_obj_tag(v_x_253_))
{
case 0:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_h__3_256_);
lean_dec(v_h__2_255_);
lean_dec(v_x_252_);
lean_dec(v_x_251_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_apply_1(v_h__1_254_, v___x_257_);
return v___x_258_;
}
case 1:
{
lean_object* v_p_259_; lean_object* v___x_260_; 
lean_dec(v_h__3_256_);
lean_dec(v_h__1_254_);
v_p_259_ = lean_ctor_get(v_x_253_, 2);
lean_inc(v_p_259_);
lean_dec_ref_known(v_x_253_, 3);
v___x_260_ = lean_apply_3(v_h__2_255_, v_x_251_, v_x_252_, v_p_259_);
return v___x_260_;
}
default: 
{
lean_object* v_a_261_; lean_object* v_p_262_; lean_object* v___x_263_; 
lean_dec(v_h__2_255_);
lean_dec(v_h__1_254_);
lean_dec(v_x_251_);
v_a_261_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_a_261_);
v_p_262_ = lean_ctor_get(v_x_253_, 2);
lean_inc(v_p_262_);
lean_dec_ref_known(v_x_253_, 3);
v___x_263_ = lean_apply_3(v_h__3_256_, v_x_252_, v_a_261_, v_p_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter(lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v_motive_266_, lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_, lean_object* v_h__3_272_){
_start:
{
switch(lean_obj_tag(v_x_269_))
{
case 0:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_h__3_272_);
lean_dec(v_h__2_271_);
lean_dec(v_x_268_);
lean_dec(v_x_267_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_apply_1(v_h__1_270_, v___x_273_);
return v___x_274_;
}
case 1:
{
lean_object* v_p_275_; lean_object* v___x_276_; 
lean_dec(v_h__3_272_);
lean_dec(v_h__1_270_);
v_p_275_ = lean_ctor_get(v_x_269_, 2);
lean_inc(v_p_275_);
lean_dec_ref_known(v_x_269_, 3);
v___x_276_ = lean_apply_3(v_h__2_271_, v_x_267_, v_x_268_, v_p_275_);
return v___x_276_;
}
default: 
{
lean_object* v_a_277_; lean_object* v_p_278_; lean_object* v___x_279_; 
lean_dec(v_h__2_271_);
lean_dec(v_h__1_270_);
lean_dec(v_x_267_);
v_a_277_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_a_277_);
v_p_278_ = lean_ctor_get(v_x_269_, 2);
lean_inc(v_p_278_);
lean_dec_ref_known(v_x_269_, 3);
v___x_279_ = lean_apply_3(v_h__3_272_, v_x_268_, v_a_277_, v_p_278_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter___boxed(lean_object* v_a_280_, lean_object* v_b_281_, lean_object* v_motive_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_h__1_286_, lean_object* v_h__2_287_, lean_object* v_h__3_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_GRH___private_New_Determinant_AuxiliaryForms_GridPaths_0__New_GridPath_append_match__1_splitter(v_a_280_, v_b_281_, v_motive_282_, v_x_283_, v_x_284_, v_x_285_, v_h__1_286_, v_h__2_287_, v_h__3_288_);
lean_dec(v_b_281_);
lean_dec(v_a_280_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_first___lam__0(lean_object* v___x_290_, lean_object* v_m_291_, uint8_t v_x_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lp_GRH_New_GridPath_column___redArg(v___x_290_, v_m_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_first___lam__0___boxed(lean_object* v___x_294_, lean_object* v_m_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_x_15__boxed_297_; lean_object* v_res_298_; 
v_x_15__boxed_297_ = lean_unbox(v_x_296_);
v_res_298_ = lp_GRH_New_TwoGridPath_first___lam__0(v___x_294_, v_m_295_, v_x_15__boxed_297_);
lean_dec(v_m_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_first(lean_object* v_m_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___f_301_; lean_object* v___x_302_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___f_301_ = lean_alloc_closure((void*)(lp_GRH_New_TwoGridPath_first___lam__0___boxed), 3, 2);
lean_closure_set(v___f_301_, 0, v___x_300_);
lean_closure_set(v___f_301_, 1, v_m_299_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___f_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_last___lam__0(lean_object* v_m_303_, uint8_t v_x_304_){
_start:
{
lean_object* v___x_305_; 
lean_inc(v_m_303_);
v___x_305_ = lp_GRH_New_GridPath_row(v_m_303_, v_m_303_);
lean_dec(v_m_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_last___lam__0___boxed(lean_object* v_m_306_, lean_object* v_x_307_){
_start:
{
uint8_t v_x_8__boxed_308_; lean_object* v_res_309_; 
v_x_8__boxed_308_ = lean_unbox(v_x_307_);
v_res_309_ = lp_GRH_New_TwoGridPath_last___lam__0(v_m_306_, v_x_8__boxed_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_last(lean_object* v_m_310_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; 
lean_inc(v_m_310_);
v___f_311_ = lean_alloc_closure((void*)(lp_GRH_New_TwoGridPath_last___lam__0___boxed), 2, 1);
lean_closure_set(v___f_311_, 0, v_m_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_m_310_);
lean_ctor_set(v___x_312_, 1, v___f_311_);
return v___x_312_;
}
}
LEAN_EXPORT uint8_t lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(lean_object* v___x_313_, uint8_t v___x_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v___x_316_);
v___x_317_ = l_instDecidableEqProd___redArg(v___x_316_, v___x_316_, v___x_313_, v___y_315_);
if (v___x_317_ == 0)
{
uint8_t v___x_318_; 
v___x_318_ = 1;
return v___x_318_;
}
else
{
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___x_319_, lean_object* v___x_320_, lean_object* v___y_321_){
_start:
{
uint8_t v___x_332__boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v___x_332__boxed_322_ = lean_unbox(v___x_320_);
v_res_323_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0(v___x_319_, v___x_332__boxed_322_, v___y_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_as_325_, size_t v_i_326_, size_t v_stop_327_, lean_object* v_b_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_326_, v_stop_327_);
if (v___x_329_ == 0)
{
size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___f_334_; uint8_t v___x_335_; 
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_sub(v_i_326_, v___x_330_);
v___x_332_ = lean_array_uget_borrowed(v_as_325_, v___x_331_);
v___x_333_ = lean_box(v___x_329_);
lean_inc(v___x_332_);
v___f_334_ = lean_alloc_closure((void*)(lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_334_, 0, v___x_332_);
lean_closure_set(v___f_334_, 1, v___x_333_);
lean_inc(v_b_328_);
v___x_335_ = l_List_decidableBAll___redArg(v___f_334_, v_b_328_);
if (v___x_335_ == 0)
{
v_i_326_ = v___x_331_;
goto _start;
}
else
{
lean_object* v___x_337_; 
lean_inc(v___x_332_);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_332_);
lean_ctor_set(v___x_337_, 1, v_b_328_);
v_i_326_ = v___x_331_;
v_b_328_ = v___x_337_;
goto _start;
}
}
else
{
return v_b_328_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_345_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_as_339_, v_i_boxed_343_, v_stop_boxed_344_, v_b_342_);
lean_dec_ref(v_as_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_init_346_, lean_object* v_l_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_348_ = lean_array_mk(v_l_347_);
v___x_349_ = lean_array_get_size(v___x_348_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_nat_dec_lt(v___x_350_, v___x_349_);
if (v___x_351_ == 0)
{
lean_dec_ref(v___x_348_);
return v_init_346_;
}
else
{
size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_usize_of_nat(v___x_349_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v___x_348_, v___x_352_, v___x_353_, v_init_346_);
lean_dec_ref(v___x_348_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_l_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_box(0);
v___x_357_ = lp_GRH_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v___x_356_, v_l_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1(lean_object* v_s_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0(lean_object* v_s_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_s_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_TwoGridPath_squares_spec__0___redArg(lean_object* v_f_362_, lean_object* v_s_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lp_mathlib_Multiset_map___redArg(v_f_362_, v_s_363_);
v___x_365_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_squares___redArg(lean_object* v_00_u0393_367_){
_start:
{
lean_object* v_diagonalIndex_368_; lean_object* v_half_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_diagonalIndex_368_ = lean_ctor_get(v_00_u0393_367_, 0);
lean_inc_n(v_diagonalIndex_368_, 5);
v_half_369_ = lean_ctor_get(v_00_u0393_367_, 1);
lean_inc_ref_n(v_half_369_, 2);
lean_dec_ref(v_00_u0393_367_);
v___x_370_ = l_List_range(v_diagonalIndex_368_);
lean_inc(v___x_370_);
v___x_371_ = lp_mathlib_Multiset_product___redArg(v___x_370_, v___x_370_);
v___x_372_ = 0;
v___x_373_ = lean_box(v___x_372_);
v___x_374_ = lean_apply_1(v_half_369_, v___x_373_);
v___x_375_ = lp_GRH_New_GridPath_squares___redArg(v_diagonalIndex_368_, v_diagonalIndex_368_, v___x_374_);
v___x_376_ = lp_mathlib_List_foldrTR___at___00Multiset_ndunion___at___00YoungDiagram_cellsOfRowLens_spec__0_spec__1(v___x_375_, v___x_371_);
v___x_377_ = ((lean_object*)(lp_GRH_New_TwoGridPath_squares___redArg___closed__0));
v___x_378_ = 1;
v___x_379_ = lean_box(v___x_378_);
v___x_380_ = lean_apply_1(v_half_369_, v___x_379_);
v___x_381_ = lp_GRH_New_GridPath_squares___redArg(v_diagonalIndex_368_, v_diagonalIndex_368_, v___x_380_);
v___x_382_ = lp_GRH_Finset_image___at___00New_TwoGridPath_squares_spec__0___redArg(v___x_377_, v___x_381_);
v___x_383_ = lp_mathlib_List_foldrTR___at___00Multiset_ndunion___at___00YoungDiagram_cellsOfRowLens_spec__0_spec__1(v___x_382_, v___x_376_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_squares(lean_object* v_m_384_, lean_object* v_00_u0393_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lp_GRH_New_TwoGridPath_squares___redArg(v_00_u0393_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_squares___boxed(lean_object* v_m_387_, lean_object* v_00_u0393_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = lp_GRH_New_TwoGridPath_squares(v_m_387_, v_00_u0393_388_);
lean_dec(v_m_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_image___at___00New_TwoGridPath_squares_spec__0(lean_object* v_00_u03b1_390_, lean_object* v_f_391_, lean_object* v_s_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lp_GRH_Finset_image___at___00New_TwoGridPath_squares_spec__0___redArg(v_f_391_, v_s_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2(lean_object* v_l_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_R_396_, lean_object* v_l_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lp_GRH_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00New_TwoGridPath_squares_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_l_397_);
return v___x_398_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Base(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_GridPaths(uint8_t builtin) {
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
res = initialize_GRH_Lib_Base(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
