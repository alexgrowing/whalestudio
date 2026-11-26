// Lean compiler output
// Module: New.Determinant.AuxiliaryForms.PathData
// Imports: public import Init public meta import Init public import Lib.Weil.DualPair.Flip public import New.Determinant.AuxiliaryForms.GridPaths public import New.Determinant.Chain.SquareLaw public import New.Determinant.Twist.FitTwists public import New.OneLift.ComparisonOperator.ExchangeData
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_columnEdge(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_columnEdge___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowEdge(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowEdge___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__0 = (const lean_object*)&lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__0_value;
static const lean_closure_object lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__1 = (const lean_object*)&lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__1_value;
static const lean_closure_object lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__2___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__1_value),((lean_object*)&lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__0_value)} };
static const lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__2 = (const lean_object*)&lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__2_value;
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_ndinsert___at___00New_GridPath_edges_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_edges___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_edges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_edges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent___redArg(lean_object* v_D_1_, uint8_t v_x_2_){
_start:
{
if (v_x_2_ == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
else
{
lean_object* v_natB_4_; 
v_natB_4_ = lean_ctor_get(v_D_1_, 2);
lean_inc(v_natB_4_);
return v_natB_4_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent___redArg___boxed(lean_object* v_D_5_, lean_object* v_x_6_){
_start:
{
uint8_t v_x_24__boxed_7_; lean_object* v_res_8_; 
v_x_24__boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = lp_GRH_New_Data_triangleExponent___redArg(v_D_5_, v_x_24__boxed_7_);
lean_dec_ref(v_D_5_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent(lean_object* v_P_9_, lean_object* v_D_10_, uint8_t v_x_11_){
_start:
{
if (v_x_11_ == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(1u);
return v___x_12_;
}
else
{
lean_object* v_natB_13_; 
v_natB_13_ = lean_ctor_get(v_D_10_, 2);
lean_inc(v_natB_13_);
return v_natB_13_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_triangleExponent___boxed(lean_object* v_P_14_, lean_object* v_D_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_x_29__boxed_17_; lean_object* v_res_18_; 
v_x_29__boxed_17_ = lean_unbox(v_x_16_);
v_res_18_ = lp_GRH_New_Data_triangleExponent(v_P_14_, v_D_15_, v_x_29__boxed_17_);
lean_dec_ref(v_D_15_);
lean_dec_ref(v_P_14_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_columnEdge(uint8_t v_z_19_, lean_object* v_a_20_, lean_object* v_b_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
lean_inc(v_b_21_);
lean_inc(v_a_20_);
v___x_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_22_, 0, v_a_20_);
lean_ctor_set(v___x_22_, 1, v_b_21_);
v___x_23_ = lean_box(v_z_19_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_b_21_, v___x_25_);
lean_dec(v_b_21_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v_a_20_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = lean_box(v_z_19_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_24_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_columnEdge___boxed(lean_object* v_z_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_z_boxed_34_; lean_object* v_res_35_; 
v_z_boxed_34_ = lean_unbox(v_z_31_);
v_res_35_ = lp_GRH_New_Data_columnEdge(v_z_boxed_34_, v_a_32_, v_b_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowEdge(uint8_t v_z_36_, lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_inc(v_b_38_);
lean_inc(v_a_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_a_37_);
lean_ctor_set(v___x_39_, 1, v_b_38_);
v___x_40_ = lean_box(v_z_36_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v___x_39_);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_a_37_, v___x_42_);
lean_dec(v_a_37_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v_b_38_);
v___x_45_ = lean_box(v_z_36_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_41_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_rowEdge___boxed(lean_object* v_z_48_, lean_object* v_a_49_, lean_object* v_b_50_){
_start:
{
uint8_t v_z_boxed_51_; lean_object* v_res_52_; 
v_z_boxed_51_ = lean_unbox(v_z_48_);
v_res_52_ = lp_GRH_New_Data_rowEdge(v_z_boxed_51_, v_a_49_, v_b_50_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__2(lean_object* v___f_53_, lean_object* v___f_54_, lean_object* v_a_55_, lean_object* v_b_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = l_instDecidableEqProd___redArg(v___f_53_, v___f_54_, v_a_55_, v_b_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__2___boxed(lean_object* v___f_58_, lean_object* v___f_59_, lean_object* v_a_60_, lean_object* v_b_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__2(v___f_58_, v___f_59_, v_a_60_, v_b_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__1(uint8_t v___y_64_, uint8_t v___y_65_){
_start:
{
if (v___y_65_ == 0)
{
if (v___y_64_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 1;
return v___x_66_;
}
else
{
return v___y_65_;
}
}
else
{
return v___y_64_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__1___boxed(lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
uint8_t v___y_359__boxed_69_; uint8_t v___y_360__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v___y_359__boxed_69_ = lean_unbox(v___y_67_);
v___y_360__boxed_70_ = lean_unbox(v___y_68_);
v_res_71_ = lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__1(v___y_359__boxed_69_, v___y_360__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__0(lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v___x_75_);
v___x_76_ = l_instDecidableEqProd___redArg(v___x_75_, v___x_75_, v_a_73_, v_b_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__0___boxed(lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___lam__0(v_a_77_, v_b_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0(lean_object* v_a_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
uint8_t v___x_88_; 
lean_dec_ref(v_a_86_);
v___x_88_ = 0;
return v___x_88_;
}
else
{
lean_object* v_head_89_; lean_object* v_tail_90_; lean_object* v___f_91_; uint8_t v___x_92_; 
v_head_89_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_head_89_);
v_tail_90_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_tail_90_);
lean_dec_ref_known(v_x_87_, 2);
v___f_91_ = ((lean_object*)(lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___closed__2));
lean_inc_ref(v_a_86_);
v___x_92_ = l_instDecidableEqProd___redArg(v___f_91_, v___f_91_, v_a_86_, v_head_89_);
if (v___x_92_ == 0)
{
v_x_87_ = v_tail_90_;
goto _start;
}
else
{
lean_dec(v_tail_90_);
lean_dec_ref(v_a_86_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0___boxed(lean_object* v_a_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0(v_a_94_, v_x_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_ndinsert___at___00New_GridPath_edges_spec__0(lean_object* v_a_98_, lean_object* v_s_99_){
_start:
{
uint8_t v___x_100_; 
lean_inc(v_s_99_);
lean_inc_ref(v_a_98_);
v___x_100_ = lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0(v_a_98_, v_s_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v_a_98_);
lean_ctor_set(v___x_101_, 1, v_s_99_);
return v___x_101_;
}
else
{
lean_dec_ref(v_a_98_);
return v_s_99_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges___redArg(uint8_t v_z_102_, lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
switch(lean_obj_tag(v_x_105_))
{
case 0:
{
lean_object* v___x_106_; 
lean_dec(v_x_104_);
lean_dec(v_x_103_);
v___x_106_ = lean_box(0);
return v___x_106_;
}
case 1:
{
lean_object* v_p_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_p_107_ = lean_ctor_get(v_x_105_, 2);
lean_inc(v_p_107_);
lean_dec_ref_known(v_x_105_, 3);
lean_inc(v_x_104_);
lean_inc_n(v_x_103_, 2);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_x_103_);
lean_ctor_set(v___x_108_, 1, v_x_104_);
v___x_109_ = lean_box(v_z_102_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_x_104_, v___x_111_);
lean_dec(v_x_104_);
lean_inc(v___x_112_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_x_103_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_box(v_z_102_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_110_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lp_GRH_New_GridPath_edges___redArg(v_z_102_, v_x_103_, v___x_112_, v_p_107_);
v___x_118_ = lp_GRH_Multiset_ndinsert___at___00New_GridPath_edges_spec__0(v___x_116_, v___x_117_);
return v___x_118_;
}
default: 
{
lean_object* v_a_119_; lean_object* v_p_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_x_103_);
v_a_119_ = lean_ctor_get(v_x_105_, 0);
lean_inc_n(v_a_119_, 2);
v_p_120_ = lean_ctor_get(v_x_105_, 2);
lean_inc(v_p_120_);
lean_dec_ref_known(v_x_105_, 3);
lean_inc_n(v_x_104_, 2);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_a_119_);
lean_ctor_set(v___x_121_, 1, v_x_104_);
v___x_122_ = lean_box(v_z_102_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_a_119_, v___x_124_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_x_104_);
v___x_127_ = lean_box(v_z_102_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_123_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lp_GRH_New_GridPath_edges___redArg(v_z_102_, v_a_119_, v_x_104_, v_p_120_);
v___x_131_ = lp_GRH_Multiset_ndinsert___at___00New_GridPath_edges_spec__0(v___x_129_, v___x_130_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges___redArg___boxed(lean_object* v_z_132_, lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_z_boxed_136_; lean_object* v_res_137_; 
v_z_boxed_136_ = lean_unbox(v_z_132_);
v_res_137_ = lp_GRH_New_GridPath_edges___redArg(v_z_boxed_136_, v_x_133_, v_x_134_, v_x_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges(lean_object* v_a_u2080_138_, lean_object* v_b_u2080_139_, uint8_t v_z_140_, lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lp_GRH_New_GridPath_edges___redArg(v_z_140_, v_x_141_, v_x_142_, v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GridPath_edges___boxed(lean_object* v_a_u2080_145_, lean_object* v_b_u2080_146_, lean_object* v_z_147_, lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_z_boxed_151_; lean_object* v_res_152_; 
v_z_boxed_151_ = lean_unbox(v_z_147_);
v_res_152_ = lp_GRH_New_GridPath_edges(v_a_u2080_145_, v_b_u2080_146_, v_z_boxed_151_, v_x_148_, v_x_149_, v_x_150_);
lean_dec(v_b_u2080_146_);
lean_dec(v_a_u2080_145_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter___redArg(lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_, lean_object* v_h__3_158_){
_start:
{
switch(lean_obj_tag(v_x_155_))
{
case 0:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_h__3_158_);
lean_dec(v_h__2_157_);
lean_dec(v_x_154_);
lean_dec(v_x_153_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_1(v_h__1_156_, v___x_159_);
return v___x_160_;
}
case 1:
{
lean_object* v_p_161_; lean_object* v___x_162_; 
lean_dec(v_h__3_158_);
lean_dec(v_h__1_156_);
v_p_161_ = lean_ctor_get(v_x_155_, 2);
lean_inc(v_p_161_);
lean_dec_ref_known(v_x_155_, 3);
v___x_162_ = lean_apply_3(v_h__2_157_, v_x_153_, v_x_154_, v_p_161_);
return v___x_162_;
}
default: 
{
lean_object* v_a_163_; lean_object* v_p_164_; lean_object* v___x_165_; 
lean_dec(v_h__2_157_);
lean_dec(v_h__1_156_);
lean_dec(v_x_153_);
v_a_163_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_163_);
v_p_164_ = lean_ctor_get(v_x_155_, 2);
lean_inc(v_p_164_);
lean_dec_ref_known(v_x_155_, 3);
v___x_165_ = lean_apply_3(v_h__3_158_, v_x_154_, v_a_163_, v_p_164_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter(lean_object* v_a_u2080_166_, lean_object* v_b_u2080_167_, lean_object* v_motive_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_h__1_172_, lean_object* v_h__2_173_, lean_object* v_h__3_174_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_h__3_174_);
lean_dec(v_h__2_173_);
lean_dec(v_x_170_);
lean_dec(v_x_169_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v_h__1_172_, v___x_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_p_177_; lean_object* v___x_178_; 
lean_dec(v_h__3_174_);
lean_dec(v_h__1_172_);
v_p_177_ = lean_ctor_get(v_x_171_, 2);
lean_inc(v_p_177_);
lean_dec_ref_known(v_x_171_, 3);
v___x_178_ = lean_apply_3(v_h__2_173_, v_x_169_, v_x_170_, v_p_177_);
return v___x_178_;
}
default: 
{
lean_object* v_a_179_; lean_object* v_p_180_; lean_object* v___x_181_; 
lean_dec(v_h__2_173_);
lean_dec(v_h__1_172_);
lean_dec(v_x_169_);
v_a_179_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_a_179_);
v_p_180_ = lean_ctor_get(v_x_171_, 2);
lean_inc(v_p_180_);
lean_dec_ref_known(v_x_171_, 3);
v___x_181_ = lean_apply_3(v_h__3_174_, v_x_170_, v_a_179_, v_p_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter___boxed(lean_object* v_a_u2080_182_, lean_object* v_b_u2080_183_, lean_object* v_motive_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_, lean_object* v_h__3_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_GRH___private_New_Determinant_AuxiliaryForms_PathData_0__New_GridPath_edges_match__1_splitter(v_a_u2080_182_, v_b_u2080_183_, v_motive_184_, v_x_185_, v_x_186_, v_x_187_, v_h__1_188_, v_h__2_189_, v_h__3_190_);
lean_dec(v_b_u2080_183_);
lean_dec(v_a_u2080_182_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0_spec__1(lean_object* v_as_192_, size_t v_i_193_, size_t v_stop_194_, lean_object* v_b_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lean_usize_dec_eq(v_i_193_, v_stop_194_);
if (v___x_196_ == 0)
{
size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_197_ = ((size_t)1ULL);
v___x_198_ = lean_usize_sub(v_i_193_, v___x_197_);
v___x_199_ = lean_array_uget_borrowed(v_as_192_, v___x_198_);
lean_inc(v_b_195_);
lean_inc(v___x_199_);
v___x_200_ = lp_GRH_List_elem___at___00Multiset_ndinsert___at___00New_GridPath_edges_spec__0_spec__0(v___x_199_, v_b_195_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_inc(v___x_199_);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v_b_195_);
v_i_193_ = v___x_198_;
v_b_195_ = v___x_201_;
goto _start;
}
else
{
v_i_193_ = v___x_198_;
goto _start;
}
}
else
{
return v_b_195_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0_spec__1___boxed(lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_, lean_object* v_b_207_){
_start:
{
size_t v_i_boxed_208_; size_t v_stop_boxed_209_; lean_object* v_res_210_; 
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_210_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0_spec__1(v_as_204_, v_i_boxed_208_, v_stop_boxed_209_, v_b_207_);
lean_dec_ref(v_as_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0(lean_object* v_init_211_, lean_object* v_l_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_213_ = lean_array_mk(v_l_212_);
v___x_214_ = lean_array_get_size(v___x_213_);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_nat_dec_lt(v___x_215_, v___x_214_);
if (v___x_216_ == 0)
{
lean_dec_ref(v___x_213_);
return v_init_211_;
}
else
{
size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_usize_of_nat(v___x_214_);
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lp_GRH___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0_spec__1(v___x_213_, v___x_217_, v___x_218_, v_init_211_);
lean_dec_ref(v___x_213_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0(lean_object* v_s_220_, lean_object* v_t_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0(v_t_221_, v_s_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_edges___redArg(lean_object* v_00_u0393_223_){
_start:
{
lean_object* v_diagonalIndex_224_; lean_object* v_half_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_diagonalIndex_224_ = lean_ctor_get(v_00_u0393_223_, 0);
lean_inc_n(v_diagonalIndex_224_, 4);
v_half_225_ = lean_ctor_get(v_00_u0393_223_, 1);
lean_inc_ref_n(v_half_225_, 2);
lean_dec_ref(v_00_u0393_223_);
v___x_226_ = 0;
v___x_227_ = lean_box(v___x_226_);
v___x_228_ = lean_apply_1(v_half_225_, v___x_227_);
v___x_229_ = lp_GRH_New_GridPath_edges___redArg(v___x_226_, v_diagonalIndex_224_, v_diagonalIndex_224_, v___x_228_);
v___x_230_ = 1;
v___x_231_ = lean_box(v___x_230_);
v___x_232_ = lean_apply_1(v_half_225_, v___x_231_);
v___x_233_ = lp_GRH_New_GridPath_edges___redArg(v___x_230_, v_diagonalIndex_224_, v_diagonalIndex_224_, v___x_232_);
v___x_234_ = lp_GRH_List_foldrTR___at___00Multiset_ndunion___at___00New_TwoGridPath_edges_spec__0_spec__0(v___x_233_, v___x_229_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_edges(lean_object* v_m_235_, lean_object* v_00_u0393_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lp_GRH_New_TwoGridPath_edges___redArg(v_00_u0393_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwoGridPath_edges___boxed(lean_object* v_m_238_, lean_object* v_00_u0393_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = lp_GRH_New_TwoGridPath_edges(v_m_238_, v_00_u0393_239_);
lean_dec(v_m_238_);
return v_res_240_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_Flip(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_GridPaths(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Chain_SquareLaw(uint8_t builtin);
lean_object* initialize_GRH_New_Determinant_Twist_FitTwists(uint8_t builtin);
lean_object* initialize_GRH_New_OneLift_ComparisonOperator_ExchangeData(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Determinant_AuxiliaryForms_PathData(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_DualPair_Flip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_AuxiliaryForms_GridPaths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Chain_SquareLaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Determinant_Twist_FitTwists(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_OneLift_ComparisonOperator_ExchangeData(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
