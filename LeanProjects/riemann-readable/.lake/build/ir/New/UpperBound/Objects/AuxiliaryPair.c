// Lean compiler output
// Module: New.UpperBound.Objects.AuxiliaryPair
// Imports: public import Init public meta import Init public import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic public import Lib.ClassField.HeckeCharacter.TameModulus public import Lib.GLn.Dual public import Lib.General.Algebra.LevelModulus public import Lib.Weil.Unramified.HeckeTransfer
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Nat_instAddCancelCommMonoid;
extern lean_object* lp_mathlib_Nat_instLocallyFiniteOrder;
lean_object* lp_mathlib_Finset_Ico___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_val_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_val_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter(lean_object* v_E_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_S_12_, lean_object* v_motive_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v_val_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_16_);
v_val_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_x_14_, 1);
v___x_18_ = lean_apply_1(v_h__1_15_, v_val_17_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v_val_19_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_19_);
lean_dec_ref_known(v_x_14_, 1);
v___x_20_ = lean_apply_1(v_h__2_16_, v_val_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter___boxed(lean_object* v_E_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_S_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_GRH___private_New_UpperBound_Objects_AuxiliaryPair_0__New_firstBlockHom_match__1_splitter(v_E_21_, v_inst_22_, v_inst_23_, v_inst_24_, v_S_25_, v_motive_26_, v_x_27_, v_h__1_28_, v_h__2_29_);
lean_dec_ref(v_S_25_);
lean_dec_ref(v_inst_22_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount___redArg(lean_object* v_inst_31_, lean_object* v_O_32_, lean_object* v_00_u03c4_33_, lean_object* v_i_34_){
_start:
{
lean_object* v_colsPlus_35_; lean_object* v_colsMinus_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_colsPlus_35_ = lean_ctor_get(v_O_32_, 5);
lean_inc_ref(v_colsPlus_35_);
v_colsMinus_36_ = lean_ctor_get(v_O_32_, 6);
lean_inc_ref(v_colsMinus_36_);
lean_dec_ref(v_O_32_);
lean_inc(v_i_34_);
lean_inc(v_00_u03c4_33_);
v___x_37_ = lean_apply_2(v_colsPlus_35_, v_00_u03c4_33_, v_i_34_);
v___x_38_ = l_List_lengthTR___redArg(v_inst_31_);
v___x_39_ = lean_nat_sub(v___x_38_, v_i_34_);
lean_dec(v_i_34_);
lean_dec(v___x_38_);
v___x_40_ = lean_apply_2(v_colsMinus_36_, v_00_u03c4_33_, v___x_39_);
v___x_41_ = lean_nat_add(v___x_37_, v___x_40_);
lean_dec(v___x_40_);
lean_dec(v___x_37_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount___redArg___boxed(lean_object* v_inst_42_, lean_object* v_O_43_, lean_object* v_00_u03c4_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_GRH_New_DescentPair_columnCount___redArg(v_inst_42_, v_O_43_, v_00_u03c4_44_, v_i_45_);
lean_dec(v_inst_42_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount(lean_object* v_E_47_, lean_object* v_r_48_, lean_object* v_n_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_O_55_, lean_object* v_00_u03c4_56_, lean_object* v_i_57_){
_start:
{
lean_object* v_colsPlus_58_; lean_object* v_colsMinus_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_colsPlus_58_ = lean_ctor_get(v_O_55_, 5);
lean_inc_ref(v_colsPlus_58_);
v_colsMinus_59_ = lean_ctor_get(v_O_55_, 6);
lean_inc_ref(v_colsMinus_59_);
lean_dec_ref(v_O_55_);
lean_inc(v_i_57_);
lean_inc(v_00_u03c4_56_);
v___x_60_ = lean_apply_2(v_colsPlus_58_, v_00_u03c4_56_, v_i_57_);
v___x_61_ = l_List_lengthTR___redArg(v_inst_54_);
v___x_62_ = lean_nat_sub(v___x_61_, v_i_57_);
lean_dec(v_i_57_);
lean_dec(v___x_61_);
v___x_63_ = lean_apply_2(v_colsMinus_59_, v_00_u03c4_56_, v___x_62_);
v___x_64_ = lean_nat_add(v___x_60_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_60_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_columnCount___boxed(lean_object* v_E_65_, lean_object* v_r_66_, lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_O_73_, lean_object* v_00_u03c4_74_, lean_object* v_i_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_GRH_New_DescentPair_columnCount(v_E_65_, v_r_66_, v_n_67_, v_inst_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_O_73_, v_00_u03c4_74_, v_i_75_);
lean_dec(v_inst_72_);
lean_dec_ref(v_inst_71_);
lean_dec(v_inst_70_);
lean_dec_ref(v_inst_69_);
lean_dec_ref(v_inst_68_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___redArg___lam__0(lean_object* v_O_77_, lean_object* v_00_u03c4_78_, lean_object* v_i_79_){
_start:
{
lean_object* v_colsMinus_80_; lean_object* v___x_81_; 
v_colsMinus_80_ = lean_ctor_get(v_O_77_, 6);
lean_inc_ref(v_colsMinus_80_);
lean_dec_ref(v_O_77_);
v___x_81_ = lean_apply_2(v_colsMinus_80_, v_00_u03c4_78_, v_i_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___redArg(lean_object* v_inst_82_, lean_object* v_O_83_, lean_object* v_00_u03c4_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___f_85_ = lean_alloc_closure((void*)(lp_GRH_New_DescentPair_detExp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_85_, 0, v_O_83_);
lean_closure_set(v___f_85_, 1, v_00_u03c4_84_);
v___x_86_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_87_ = lp_mathlib_Nat_instLocallyFiniteOrder;
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = l_List_lengthTR___redArg(v_inst_82_);
v___x_90_ = lp_mathlib_Finset_Ico___redArg(v___x_87_, v___x_88_, v___x_89_);
v___x_91_ = lp_mathlib_Finset_sum___redArg(v___x_86_, v___x_90_, v___f_85_);
v___x_92_ = lean_nat_to_int(v___x_91_);
v___x_93_ = lean_int_neg(v___x_92_);
lean_dec(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___redArg___boxed(lean_object* v_inst_94_, lean_object* v_O_95_, lean_object* v_00_u03c4_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_GRH_New_DescentPair_detExp___redArg(v_inst_94_, v_O_95_, v_00_u03c4_96_);
lean_dec(v_inst_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp(lean_object* v_E_98_, lean_object* v_r_99_, lean_object* v_n_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_O_106_, lean_object* v_00_u03c4_107_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___f_108_ = lean_alloc_closure((void*)(lp_GRH_New_DescentPair_detExp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_108_, 0, v_O_106_);
lean_closure_set(v___f_108_, 1, v_00_u03c4_107_);
v___x_109_ = lp_mathlib_Nat_instAddCancelCommMonoid;
v___x_110_ = lp_mathlib_Nat_instLocallyFiniteOrder;
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = l_List_lengthTR___redArg(v_inst_105_);
v___x_113_ = lp_mathlib_Finset_Ico___redArg(v___x_110_, v___x_111_, v___x_112_);
v___x_114_ = lp_mathlib_Finset_sum___redArg(v___x_109_, v___x_113_, v___f_108_);
v___x_115_ = lean_nat_to_int(v___x_114_);
v___x_116_ = lean_int_neg(v___x_115_);
lean_dec(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_detExp___boxed(lean_object* v_E_117_, lean_object* v_r_118_, lean_object* v_n_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_O_125_, lean_object* v_00_u03c4_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_GRH_New_DescentPair_detExp(v_E_117_, v_r_118_, v_n_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_inst_123_, v_inst_124_, v_O_125_, v_00_u03c4_126_);
lean_dec(v_inst_124_);
lean_dec_ref(v_inst_123_);
lean_dec(v_inst_122_);
lean_dec_ref(v_inst_121_);
lean_dec_ref(v_inst_120_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff___redArg(lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = l_List_lengthTR___redArg(v_inst_129_);
v___x_131_ = l_List_lengthTR___redArg(v_inst_128_);
v___x_132_ = lean_nat_sub(v___x_130_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff___redArg___boxed(lean_object* v_inst_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_GRH_New_DescentPair_rankDiff___redArg(v_inst_133_, v_inst_134_);
lean_dec(v_inst_134_);
lean_dec(v_inst_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff(lean_object* v_E_136_, lean_object* v_r_137_, lean_object* v_n_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = l_List_lengthTR___redArg(v_inst_143_);
v___x_146_ = l_List_lengthTR___redArg(v_inst_141_);
v___x_147_ = lean_nat_sub(v___x_145_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v___x_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DescentPair_rankDiff___boxed(lean_object* v_E_148_, lean_object* v_r_149_, lean_object* v_n_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = lp_GRH_New_DescentPair_rankDiff(v_E_148_, v_r_149_, v_n_150_, v_inst_151_, v_inst_152_, v_inst_153_, v_inst_154_, v_inst_155_, v_x_156_);
lean_dec_ref(v_x_156_);
lean_dec(v_inst_155_);
lean_dec_ref(v_inst_154_);
lean_dec(v_inst_153_);
lean_dec_ref(v_inst_152_);
lean_dec_ref(v_inst_151_);
return v_res_157_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_AutomorphicForms_AutomorphicAsAlgebraic(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_HeckeCharacter_TameModulus(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_Dual(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_LevelModulus(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_HeckeTransfer(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_UpperBound_Objects_AuxiliaryPair(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_AutomorphicForms_AutomorphicAsAlgebraic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_HeckeCharacter_TameModulus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_Dual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_LevelModulus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Unramified_HeckeTransfer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
