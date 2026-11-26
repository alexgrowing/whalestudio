// Lean compiler output
// Module: New.UpperBound.Objects.Parameters
// Imports: public import Init public meta import Init public import Lib.Weil.Lift public import New.UpperBound.Objects.InsertBlock public import New.UpperBound.Objects.LabelsAndIndexTypes
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
lean_object* lp_GRH_New_Data_t___redArg(lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_GRH_New_Data_targetParameter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_GRH_New_Data_liftWeight___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_isLeft___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Data_gridCentres___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Data_gridCentres___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_isLeft___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* lp_GRH_New_Data_gridCentres___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Data_gridCentres___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridBlocks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridBlocks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight___redArg(lean_object* v_D_1_, uint8_t v_c_2_, lean_object* v_l_3_, lean_object* v_inst_4_, lean_object* v_00_u03c4_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___y_8_; 
v___x_6_ = l_List_lengthTR___redArg(v_inst_4_);
if (v_c_2_ == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 1;
v___y_8_ = v___x_18_;
goto v___jp_7_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = 0;
v___y_8_ = v___x_19_;
goto v___jp_7_;
}
v___jp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_9_ = l_Bool_toNat(v___y_8_);
v___x_10_ = lean_nat_add(v___x_6_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_6_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_shiftr(v___x_10_, v___x_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_nat_to_int(v___x_12_);
v___x_14_ = lean_nat_add(v_l_3_, v___x_11_);
v___x_15_ = lp_GRH_New_Data_liftWeight___redArg(v_D_1_, v___x_14_, v_00_u03c4_5_);
lean_dec(v___x_14_);
v___x_16_ = lean_nat_to_int(v___x_15_);
v___x_17_ = lean_int_sub(v___x_13_, v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_13_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight___redArg___boxed(lean_object* v_D_20_, lean_object* v_c_21_, lean_object* v_l_22_, lean_object* v_inst_23_, lean_object* v_00_u03c4_24_){
_start:
{
uint8_t v_c_boxed_25_; lean_object* v_res_26_; 
v_c_boxed_25_ = lean_unbox(v_c_21_);
v_res_26_ = lp_GRH_New_Data_gridWeight___redArg(v_D_20_, v_c_boxed_25_, v_l_22_, v_inst_23_, v_00_u03c4_24_);
lean_dec(v_inst_23_);
lean_dec(v_l_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight(lean_object* v_P_27_, lean_object* v_D_28_, uint8_t v_c_29_, lean_object* v_l_30_, lean_object* v_n_31_, lean_object* v_inst_32_, lean_object* v_00_u03c4_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_GRH_New_Data_gridWeight___redArg(v_D_28_, v_c_29_, v_l_30_, v_inst_32_, v_00_u03c4_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridWeight___boxed(lean_object* v_P_35_, lean_object* v_D_36_, lean_object* v_c_37_, lean_object* v_l_38_, lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_00_u03c4_41_){
_start:
{
uint8_t v_c_boxed_42_; lean_object* v_res_43_; 
v_c_boxed_42_ = lean_unbox(v_c_37_);
v_res_43_ = lp_GRH_New_Data_gridWeight(v_P_35_, v_D_36_, v_c_boxed_42_, v_l_38_, v_n_39_, v_inst_40_, v_00_u03c4_41_);
lean_dec(v_inst_40_);
lean_dec(v_l_38_);
lean_dec_ref(v_P_35_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___redArg(lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
lean_object* v_zero_47_; uint8_t v_isZero_48_; 
v_zero_47_ = lean_unsigned_to_nat(0u);
v_isZero_48_ = lean_nat_dec_eq(v_x_44_, v_zero_47_);
if (v_isZero_48_ == 1)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_45_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_one_51_; lean_object* v_n_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_45_);
v_one_51_ = lean_unsigned_to_nat(1u);
v_n_52_ = lean_nat_sub(v_x_44_, v_one_51_);
v___x_53_ = lean_apply_1(v_h__2_46_, v_n_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___redArg___boxed(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___redArg(v_x_54_, v_h__1_55_, v_h__2_56_);
lean_dec(v_x_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter(lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
lean_object* v_zero_62_; uint8_t v_isZero_63_; 
v_zero_62_ = lean_unsigned_to_nat(0u);
v_isZero_63_ = lean_nat_dec_eq(v_x_59_, v_zero_62_);
if (v_isZero_63_ == 1)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_61_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__1_60_, v___x_64_);
return v___x_65_;
}
else
{
lean_object* v_one_66_; lean_object* v_n_67_; lean_object* v___x_68_; 
lean_dec(v_h__1_60_);
v_one_66_ = lean_unsigned_to_nat(1u);
v_n_67_ = lean_nat_sub(v_x_59_, v_one_66_);
v___x_68_ = lean_apply_1(v_h__2_61_, v_n_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter___boxed(lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_GRH___private_New_UpperBound_Objects_Parameters_0__New_Data_gridDiagEquiv_match__1_splitter(v_motive_69_, v_x_70_, v_h__1_71_, v_h__2_72_);
lean_dec(v_x_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__0(lean_object* v_D_74_, uint8_t v_z_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lp_GRH_New_Data_t___redArg(v_D_74_);
v___x_78_ = l_Bool_toNat(v_z_75_);
v___x_79_ = lean_nat_sub(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__0___boxed(lean_object* v_D_80_, lean_object* v_z_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_z_boxed_83_; lean_object* v_res_84_; 
v_z_boxed_83_ = lean_unbox(v_z_81_);
v_res_84_ = lp_GRH_New_Data_gridCentres___redArg___lam__0(v_D_80_, v_z_boxed_83_, v_x_82_);
lean_dec(v_x_82_);
lean_dec_ref(v_D_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__1(lean_object* v_D_85_, uint8_t v_z_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lp_GRH_New_Data_t___redArg(v_D_85_);
v___x_89_ = l_Bool_toNat(v_z_86_);
v___x_90_ = lean_nat_add(v___x_88_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__1___boxed(lean_object* v_D_91_, lean_object* v_z_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_z_boxed_94_; lean_object* v_res_95_; 
v_z_boxed_94_ = lean_unbox(v_z_92_);
v_res_95_ = lp_GRH_New_Data_gridCentres___redArg___lam__1(v_D_91_, v_z_boxed_94_, v_x_93_);
lean_dec(v_x_93_);
lean_dec_ref(v_D_91_);
return v_res_95_;
}
}
static lean_object* _init_lp_GRH_New_Data_gridCentres___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(2u);
v___x_97_ = lean_nat_to_int(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__2(lean_object* v_D_98_, lean_object* v_00_u03c4_99_, uint8_t v_z_100_, lean_object* v_n_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_102_ = lean_obj_once(&lp_GRH_New_Data_gridCentres___redArg___lam__2___closed__0, &lp_GRH_New_Data_gridCentres___redArg___lam__2___closed__0_once, _init_lp_GRH_New_Data_gridCentres___redArg___lam__2___closed__0);
v___x_103_ = lp_GRH_New_Data_targetParameter___redArg(v_D_98_, v_00_u03c4_99_, v_n_101_);
v___x_104_ = lean_int_mul(v___x_102_, v___x_103_);
lean_dec(v___x_103_);
v___x_105_ = l_Bool_toNat(v_z_100_);
v___x_106_ = lean_nat_to_int(v___x_105_);
v___x_107_ = lean_int_add(v___x_104_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__2___boxed(lean_object* v_D_108_, lean_object* v_00_u03c4_109_, lean_object* v_z_110_, lean_object* v_n_111_){
_start:
{
uint8_t v_z_boxed_112_; lean_object* v_res_113_; 
v_z_boxed_112_ = lean_unbox(v_z_110_);
v_res_113_ = lp_GRH_New_Data_gridCentres___redArg___lam__2(v_D_108_, v_00_u03c4_109_, v_z_boxed_112_, v_n_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__3(lean_object* v_D_114_, lean_object* v_00_u03c4_115_, lean_object* v_l_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_l_116_, v___x_117_);
v___x_119_ = lp_GRH_New_Data_liftWeight___redArg(v_D_114_, v___x_118_, v_00_u03c4_115_);
lean_dec(v___x_118_);
v___x_120_ = lean_nat_to_int(v___x_119_);
v___x_121_ = lean_int_neg(v___x_120_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__3___boxed(lean_object* v_D_122_, lean_object* v_00_u03c4_123_, lean_object* v_l_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_GRH_New_Data_gridCentres___redArg___lam__3(v_D_122_, v_00_u03c4_123_, v_l_124_);
lean_dec(v_l_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__4(lean_object* v_D_126_, lean_object* v_00_u03c4_127_, lean_object* v_l_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_l_128_, v___x_129_);
v___x_131_ = lp_GRH_New_Data_liftWeight___redArg(v_D_126_, v___x_130_, v_00_u03c4_127_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___lam__4___boxed(lean_object* v_D_133_, lean_object* v_00_u03c4_134_, lean_object* v_l_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = lp_GRH_New_Data_gridCentres___redArg___lam__4(v_D_133_, v_00_u03c4_134_, v_l_135_);
lean_dec(v_l_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg(lean_object* v_D_138_, lean_object* v_00_u03c4_139_, uint8_t v_z_140_){
_start:
{
lean_object* v_m_141_; lean_object* v_r_142_; lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_m_141_ = lean_ctor_get(v_D_138_, 6);
lean_inc(v_m_141_);
v_r_142_ = lean_ctor_get(v_D_138_, 7);
lean_inc(v_r_142_);
v___x_143_ = lean_box(v_z_140_);
lean_inc_ref_n(v_D_138_, 4);
v___f_144_ = lean_alloc_closure((void*)(lp_GRH_New_Data_gridCentres___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_144_, 0, v_D_138_);
lean_closure_set(v___f_144_, 1, v___x_143_);
v___x_145_ = lean_box(v_z_140_);
v___f_146_ = lean_alloc_closure((void*)(lp_GRH_New_Data_gridCentres___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_146_, 0, v_D_138_);
lean_closure_set(v___f_146_, 1, v___x_145_);
v___x_147_ = lean_box(v_z_140_);
lean_inc_n(v_00_u03c4_139_, 2);
v___f_148_ = lean_alloc_closure((void*)(lp_GRH_New_Data_gridCentres___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_148_, 0, v_D_138_);
lean_closure_set(v___f_148_, 1, v_00_u03c4_139_);
lean_closure_set(v___f_148_, 2, v___x_147_);
v___f_149_ = lean_alloc_closure((void*)(lp_GRH_New_Data_gridCentres___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_149_, 0, v_D_138_);
lean_closure_set(v___f_149_, 1, v_00_u03c4_139_);
v___f_150_ = lean_alloc_closure((void*)(lp_GRH_New_Data_gridCentres___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_150_, 0, v_D_138_);
lean_closure_set(v___f_150_, 1, v_00_u03c4_139_);
v___x_151_ = l_List_range(v_m_141_);
lean_inc(v___x_151_);
v___x_152_ = lp_mathlib_Multiset_disjSum___redArg(v___x_151_, v___x_151_);
v___x_153_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, lean_box(0));
lean_closure_set(v___x_153_, 3, v___f_150_);
lean_closure_set(v___x_153_, 4, v___f_149_);
v___x_154_ = lean_alloc_closure((void*)(l_Sum_elim), 6, 5);
lean_closure_set(v___x_154_, 0, lean_box(0));
lean_closure_set(v___x_154_, 1, lean_box(0));
lean_closure_set(v___x_154_, 2, lean_box(0));
lean_closure_set(v___x_154_, 3, v___f_146_);
lean_closure_set(v___x_154_, 4, v___f_144_);
v___x_155_ = ((lean_object*)(lp_GRH_New_Data_gridCentres___redArg___closed__0));
v___x_156_ = l_Bool_toNat(v_z_140_);
v___x_157_ = lean_nat_add(v_r_142_, v___x_156_);
lean_dec(v___x_156_);
lean_dec(v_r_142_);
v___x_158_ = l_List_range(v___x_157_);
v___x_159_ = lp_GRH_Finset_image___at___00New_doubledBlock_spec__0___redArg(v___f_148_, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_160_, 0, v___x_152_);
lean_ctor_set(v___x_160_, 1, v___x_153_);
lean_ctor_set(v___x_160_, 2, v___x_154_);
lean_ctor_set(v___x_160_, 3, v___x_155_);
lean_ctor_set(v___x_160_, 4, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___redArg___boxed(lean_object* v_D_161_, lean_object* v_00_u03c4_162_, lean_object* v_z_163_){
_start:
{
uint8_t v_z_boxed_164_; lean_object* v_res_165_; 
v_z_boxed_164_ = lean_unbox(v_z_163_);
v_res_165_ = lp_GRH_New_Data_gridCentres___redArg(v_D_161_, v_00_u03c4_162_, v_z_boxed_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres(lean_object* v_P_166_, lean_object* v_D_167_, lean_object* v_00_u03c4_168_, uint8_t v_z_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lp_GRH_New_Data_gridCentres___redArg(v_D_167_, v_00_u03c4_168_, v_z_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridCentres___boxed(lean_object* v_P_171_, lean_object* v_D_172_, lean_object* v_00_u03c4_173_, lean_object* v_z_174_){
_start:
{
uint8_t v_z_boxed_175_; lean_object* v_res_176_; 
v_z_boxed_175_ = lean_unbox(v_z_174_);
v_res_176_ = lp_GRH_New_Data_gridCentres(v_P_171_, v_D_172_, v_00_u03c4_173_, v_z_boxed_175_);
lean_dec_ref(v_P_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridBlocks(lean_object* v_o_177_, lean_object* v_i_178_, lean_object* v_j_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = l_List_range(v_i_178_);
v___x_181_ = lean_nat_add(v_o_177_, v_j_179_);
v___x_182_ = lp_mathlib_Finset_Ico___at___00FormalMultilinearSeries_compPartialSumSource_spec__0(v_o_177_, v___x_181_);
lean_dec(v___x_181_);
v___x_183_ = lp_mathlib_Multiset_disjSum___redArg(v___x_180_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Data_gridBlocks___boxed(lean_object* v_o_184_, lean_object* v_i_185_, lean_object* v_j_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = lp_GRH_New_Data_gridBlocks(v_o_184_, v_i_185_, v_j_186_);
lean_dec(v_j_186_);
lean_dec(v_o_184_);
return v_res_187_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Lift(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_InsertBlock(uint8_t builtin);
lean_object* initialize_GRH_New_UpperBound_Objects_LabelsAndIndexTypes(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_Parameters(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Lift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_InsertBlock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_UpperBound_Objects_LabelsAndIndexTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
