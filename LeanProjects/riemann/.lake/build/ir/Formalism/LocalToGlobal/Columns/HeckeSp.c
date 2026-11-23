// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.HeckeSp
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq public import Formalism.LocalToGlobal.Columns.StdLatUnimodular public import Formalism.LocalToGlobal.Columns.DecoFin
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_completeLattice___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_baseChange___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lp_mathlib_AddSubgroupClass_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_submoduleMap___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_Quotient_equiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_NCov_pt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hAlg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hAlg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hGen___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sysOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sysOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sysOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSumOver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSumOver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_gaussBin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_gaussBin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSumOver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSumOver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_exSys___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_exSys___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Col_exSys___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_exSys___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exSys(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exSys___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_L2_Col_exOp_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_L2_Col_exOp_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_L2_Col_exOp_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_L2_Col_exOp_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exOp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exOp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exOp(lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_quotMapEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_quotMapEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigAt(lean_object* v_K_1_, lean_object* v_V_2_, lean_object* v_I_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_op_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigAt___boxed(lean_object* v_K_10_, lean_object* v_V_11_, lean_object* v_I_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_op_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_tree_Formalism_L2_Col_eigAt(v_K_10_, v_V_11_, v_I_12_, v_inst_13_, v_inst_14_, v_inst_15_, v_op_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec(v_op_16_);
lean_dec(v_inst_15_);
lean_dec_ref(v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_toSemiring_24_; lean_object* v_toAddMonoid_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_toSupSet_28_; lean_object* v___x_29_; 
v___x_22_ = lp_mathlib_Field_toSemifield___redArg(v_inst_19_);
v___x_23_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_22_);
v_toSemiring_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_toSemiring_24_);
lean_dec_ref(v___x_23_);
v_toAddMonoid_25_ = lean_ctor_get(v_inst_20_, 0);
v___x_26_ = lp_mathlib_Submodule_completeLattice___redArg(v_toSemiring_24_, v_toAddMonoid_25_, v_inst_21_);
lean_dec_ref(v_toSemiring_24_);
v___x_27_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_26_);
v_toSupSet_28_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_toSupSet_28_);
lean_dec_ref(v___x_27_);
v___x_29_ = lean_apply_1(v_toSupSet_28_, lean_box(0));
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum___redArg___boxed(lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_tree_Formalism_L2_Col_eigSum___redArg(v_inst_30_, v_inst_31_, v_inst_32_);
lean_dec(v_inst_32_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum(lean_object* v_K_34_, lean_object* v_V_35_, lean_object* v_I_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_op_40_, lean_object* v_C_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_tree_Formalism_L2_Col_eigSum___redArg(v_inst_37_, v_inst_38_, v_inst_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSum___boxed(lean_object* v_K_43_, lean_object* v_V_44_, lean_object* v_I_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_op_49_, lean_object* v_C_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_tree_Formalism_L2_Col_eigSum(v_K_43_, v_V_44_, v_I_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_op_49_, v_C_50_);
lean_dec(v_op_49_);
lean_dec(v_inst_48_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hAlg(lean_object* v_O_52_, lean_object* v_K_53_, lean_object* v_V_54_, lean_object* v_I_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_op_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hAlg___boxed(lean_object* v_O_65_, lean_object* v_K_66_, lean_object* v_V_67_, lean_object* v_I_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_op_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_L2_Col_hAlg(v_O_65_, v_K_66_, v_V_67_, v_I_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_inst_75_, v_op_76_);
lean_dec(v_op_76_);
lean_dec(v_inst_74_);
lean_dec(v_inst_73_);
lean_dec_ref(v_inst_72_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_69_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hGen___redArg(lean_object* v_op_78_, lean_object* v_i_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_apply_1(v_op_78_, v_i_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hGen(lean_object* v_O_81_, lean_object* v_K_82_, lean_object* v_V_83_, lean_object* v_I_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_op_92_, lean_object* v_i_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_apply_1(v_op_92_, v_i_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_hGen___boxed(lean_object* v_O_95_, lean_object* v_K_96_, lean_object* v_V_97_, lean_object* v_I_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_op_106_, lean_object* v_i_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_L2_Col_hGen(v_O_95_, v_K_96_, v_V_97_, v_I_98_, v_inst_99_, v_inst_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_op_106_, v_i_107_);
lean_dec(v_inst_104_);
lean_dec(v_inst_103_);
lean_dec_ref(v_inst_102_);
lean_dec_ref(v_inst_101_);
lean_dec_ref(v_inst_100_);
lean_dec_ref(v_inst_99_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sysOf___redArg(lean_object* v_inst_109_, lean_object* v_op_110_, lean_object* v_00_u03c8_111_, lean_object* v_i_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_apply_1(v_op_110_, v_i_112_);
v___x_114_ = lp_tree_Formalism_L2_NCov_pt___redArg(v_inst_109_, v_00_u03c8_111_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sysOf(lean_object* v_O_115_, lean_object* v_K_116_, lean_object* v_V_117_, lean_object* v_I_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_op_126_, lean_object* v_00_u03c8_127_, lean_object* v_i_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_tree_Formalism_L2_Col_sysOf___redArg(v_inst_121_, v_op_126_, v_00_u03c8_127_, v_i_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_sysOf___boxed(lean_object* v_O_130_, lean_object* v_K_131_, lean_object* v_V_132_, lean_object* v_I_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_op_141_, lean_object* v_00_u03c8_142_, lean_object* v_i_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_tree_Formalism_L2_Col_sysOf(v_O_130_, v_K_131_, v_V_132_, v_I_133_, v_inst_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_op_141_, v_00_u03c8_142_, v_i_143_);
lean_dec(v_inst_139_);
lean_dec(v_inst_138_);
lean_dec_ref(v_inst_137_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_134_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL___redArg(lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_op_150_, lean_object* v_i_151_){
_start:
{
lean_object* v___x_152_; lean_object* v_toCommSemiring_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_toSemiring_156_; lean_object* v_toAddMonoid_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_152_ = lp_mathlib_Field_toSemifield___redArg(v_inst_145_);
v_toCommSemiring_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref(v_toCommSemiring_153_);
lean_dec_ref(v___x_152_);
v___x_154_ = lp_mathlib_Field_toSemifield___redArg(v_inst_148_);
v___x_155_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_154_);
v_toSemiring_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_toSemiring_156_);
lean_dec_ref(v___x_155_);
v_toAddMonoid_157_ = lean_ctor_get(v_inst_146_, 0);
lean_inc_ref_n(v_toAddMonoid_157_, 2);
lean_dec_ref(v_inst_146_);
v___x_158_ = lean_apply_1(v_op_150_, v_i_151_);
lean_inc(v_inst_147_);
v___x_159_ = lp_mathlib_LinearMap_baseChange___redArg(v_toCommSemiring_153_, v_toSemiring_156_, v_inst_149_, v_toAddMonoid_157_, v_toAddMonoid_157_, v_inst_147_, v_inst_147_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL___redArg___boxed(lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_op_165_, lean_object* v_i_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lp_tree_Formalism_L2_Col_opL___redArg(v_inst_160_, v_inst_161_, v_inst_162_, v_inst_163_, v_inst_164_, v_op_165_, v_i_166_);
lean_dec_ref(v_inst_163_);
lean_dec_ref(v_inst_160_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL(lean_object* v_K_168_, lean_object* v_V_169_, lean_object* v_I_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_L_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_op_177_, lean_object* v_i_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lp_tree_Formalism_L2_Col_opL___redArg(v_inst_171_, v_inst_172_, v_inst_173_, v_inst_175_, v_inst_176_, v_op_177_, v_i_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_opL___boxed(lean_object* v_K_180_, lean_object* v_V_181_, lean_object* v_I_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_L_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_op_189_, lean_object* v_i_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_tree_Formalism_L2_Col_opL(v_K_180_, v_V_181_, v_I_182_, v_inst_183_, v_inst_184_, v_inst_185_, v_L_186_, v_inst_187_, v_inst_188_, v_op_189_, v_i_190_);
lean_dec_ref(v_inst_187_);
lean_dec_ref(v_inst_183_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSumOver(lean_object* v_K_192_, lean_object* v_V_193_, lean_object* v_I_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_L_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_op_201_, lean_object* v_C_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_eigSumOver___boxed(lean_object* v_K_204_, lean_object* v_V_205_, lean_object* v_I_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_L_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_op_213_, lean_object* v_C_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = lp_tree_Formalism_L2_Col_eigSumOver(v_K_204_, v_V_205_, v_I_206_, v_inst_207_, v_inst_208_, v_inst_209_, v_L_210_, v_inst_211_, v_inst_212_, v_op_213_, v_C_214_);
lean_dec(v_op_213_);
lean_dec_ref(v_inst_212_);
lean_dec_ref(v_inst_211_);
lean_dec(v_inst_209_);
lean_dec_ref(v_inst_208_);
lean_dec_ref(v_inst_207_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_gaussBin(lean_object* v_q_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_zero_219_; uint8_t v_isZero_220_; 
v_zero_219_ = lean_unsigned_to_nat(0u);
v_isZero_220_ = lean_nat_dec_eq(v_x_218_, v_zero_219_);
if (v_isZero_220_ == 1)
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(1u);
return v___x_221_;
}
else
{
uint8_t v_isZero_222_; 
v_isZero_222_ = lean_nat_dec_eq(v_x_217_, v_zero_219_);
if (v_isZero_222_ == 1)
{
return v_zero_219_;
}
else
{
lean_object* v_one_223_; lean_object* v_n_224_; lean_object* v_n_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_one_223_ = lean_unsigned_to_nat(1u);
v_n_224_ = lean_nat_sub(v_x_218_, v_one_223_);
v_n_225_ = lean_nat_sub(v_x_217_, v_one_223_);
v___x_226_ = lp_tree_Formalism_L2_Col_gaussBin(v_q_216_, v_n_225_, v_n_224_);
v___x_227_ = lean_nat_add(v_n_224_, v_one_223_);
lean_dec(v_n_224_);
v___x_228_ = lean_nat_pow(v_q_216_, v___x_227_);
v___x_229_ = lp_tree_Formalism_L2_Col_gaussBin(v_q_216_, v_n_225_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v_n_225_);
v___x_230_ = lean_nat_mul(v___x_228_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_nat_add(v___x_226_, v___x_230_);
lean_dec(v___x_230_);
lean_dec(v___x_226_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_gaussBin___boxed(lean_object* v_q_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = lp_tree_Formalism_L2_Col_gaussBin(v_q_232_, v_x_233_, v_x_234_);
lean_dec(v_x_234_);
lean_dec(v_x_233_);
lean_dec(v_q_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___redArg(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_h__1_238_, lean_object* v_h__2_239_, lean_object* v_h__3_240_){
_start:
{
lean_object* v_zero_241_; uint8_t v_isZero_242_; 
v_zero_241_ = lean_unsigned_to_nat(0u);
v_isZero_242_ = lean_nat_dec_eq(v_x_237_, v_zero_241_);
if (v_isZero_242_ == 1)
{
lean_object* v___x_243_; 
lean_dec(v_h__3_240_);
lean_dec(v_h__2_239_);
v___x_243_ = lean_apply_1(v_h__1_238_, v_x_236_);
return v___x_243_;
}
else
{
lean_object* v_one_244_; lean_object* v_n_245_; uint8_t v_isZero_246_; 
lean_dec(v_h__1_238_);
v_one_244_ = lean_unsigned_to_nat(1u);
v_n_245_ = lean_nat_sub(v_x_237_, v_one_244_);
v_isZero_246_ = lean_nat_dec_eq(v_x_236_, v_zero_241_);
if (v_isZero_246_ == 1)
{
lean_object* v___x_247_; 
lean_dec(v_h__3_240_);
lean_dec(v_x_236_);
v___x_247_ = lean_apply_1(v_h__2_239_, v_n_245_);
return v___x_247_;
}
else
{
lean_object* v_n_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_239_);
v_n_248_ = lean_nat_sub(v_x_236_, v_one_244_);
lean_dec(v_x_236_);
v___x_249_ = lean_apply_2(v_h__3_240_, v_n_248_, v_n_245_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___redArg___boxed(lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_h__1_252_, lean_object* v_h__2_253_, lean_object* v_h__3_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___redArg(v_x_250_, v_x_251_, v_h__1_252_, v_h__2_253_, v_h__3_254_);
lean_dec(v_x_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter(lean_object* v_motive_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_h__1_259_, lean_object* v_h__2_260_, lean_object* v_h__3_261_){
_start:
{
lean_object* v_zero_262_; uint8_t v_isZero_263_; 
v_zero_262_ = lean_unsigned_to_nat(0u);
v_isZero_263_ = lean_nat_dec_eq(v_x_258_, v_zero_262_);
if (v_isZero_263_ == 1)
{
lean_object* v___x_264_; 
lean_dec(v_h__3_261_);
lean_dec(v_h__2_260_);
v___x_264_ = lean_apply_1(v_h__1_259_, v_x_257_);
return v___x_264_;
}
else
{
lean_object* v_one_265_; lean_object* v_n_266_; uint8_t v_isZero_267_; 
lean_dec(v_h__1_259_);
v_one_265_ = lean_unsigned_to_nat(1u);
v_n_266_ = lean_nat_sub(v_x_258_, v_one_265_);
v_isZero_267_ = lean_nat_dec_eq(v_x_257_, v_zero_262_);
if (v_isZero_267_ == 1)
{
lean_object* v___x_268_; 
lean_dec(v_h__3_261_);
lean_dec(v_x_257_);
v___x_268_ = lean_apply_1(v_h__2_260_, v_n_266_);
return v___x_268_;
}
else
{
lean_object* v_n_269_; lean_object* v___x_270_; 
lean_dec(v_h__2_260_);
v_n_269_ = lean_nat_sub(v_x_257_, v_one_265_);
lean_dec(v_x_257_);
v___x_270_ = lean_apply_2(v_h__3_261_, v_n_269_, v_n_266_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter___boxed(lean_object* v_motive_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_, lean_object* v_h__3_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_gaussBin_match__1_splitter(v_motive_271_, v_x_272_, v_x_273_, v_h__1_274_, v_h__2_275_, v_h__3_276_);
lean_dec(v_x_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA___redArg(lean_object* v_inst_278_, lean_object* v_muV_279_, lean_object* v_etaV_280_, lean_object* v_q_281_, lean_object* v_r_282_, lean_object* v_P_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_toSemiring_286_; lean_object* v___x_287_; lean_object* v_toMul_288_; lean_object* v_toMonoid_289_; lean_object* v___x_290_; lean_object* v_inv_291_; lean_object* v___x_292_; lean_object* v_val_293_; lean_object* v_toNPow_294_; lean_object* v___x_295_; lean_object* v_toRing_296_; lean_object* v___x_297_; lean_object* v_toAddMonoidWithOne_298_; lean_object* v_toNatCast_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_284_ = lp_mathlib_Field_toSemifield___redArg(v_inst_278_);
v___x_285_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_284_);
v_toSemiring_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref_n(v_toSemiring_286_, 2);
lean_dec_ref(v___x_285_);
v___x_287_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_286_);
v_toMul_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_n(v_toMul_288_, 2);
lean_dec_ref(v___x_287_);
v_toMonoid_289_ = lean_ctor_get(v_toSemiring_286_, 1);
lean_inc_ref(v_toMonoid_289_);
lean_dec_ref(v_toSemiring_286_);
lean_inc_n(v_P_283_, 2);
v___x_290_ = lean_apply_1(v_muV_279_, v_P_283_);
v_inv_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_inv_291_);
lean_dec_ref(v___x_290_);
v___x_292_ = lean_apply_1(v_etaV_280_, v_P_283_);
v_val_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_293_);
lean_dec_ref(v___x_292_);
v_toNPow_294_ = lean_ctor_get(v_toMonoid_289_, 2);
lean_inc(v_toNPow_294_);
lean_dec_ref(v_toMonoid_289_);
v___x_295_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_278_);
v_toRing_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_ref(v_toRing_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_296_);
v_toAddMonoidWithOne_298_ = lean_ctor_get(v___x_297_, 1);
lean_inc_ref(v_toAddMonoidWithOne_298_);
lean_dec_ref(v___x_297_);
v_toNatCast_299_ = lean_ctor_get(v_toAddMonoidWithOne_298_, 0);
lean_inc(v_toNatCast_299_);
lean_dec_ref(v_toAddMonoidWithOne_298_);
v___x_300_ = lean_apply_2(v_toMul_288_, v_inv_291_, v_val_293_);
v___x_301_ = lean_apply_1(v_q_281_, v_P_283_);
v___x_302_ = lean_apply_1(v_toNatCast_299_, v___x_301_);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_r_282_, v___x_303_);
v___x_305_ = lean_nat_shiftr(v___x_304_, v___x_303_);
lean_dec(v___x_304_);
v___x_306_ = lean_apply_2(v_toNPow_294_, v___x_305_, v___x_302_);
v___x_307_ = lean_apply_2(v_toMul_288_, v___x_300_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA___redArg___boxed(lean_object* v_inst_308_, lean_object* v_muV_309_, lean_object* v_etaV_310_, lean_object* v_q_311_, lean_object* v_r_312_, lean_object* v_P_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = lp_tree_Formalism_L2_Col_firstValA___redArg(v_inst_308_, v_muV_309_, v_etaV_310_, v_q_311_, v_r_312_, v_P_313_);
lean_dec(v_r_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA(lean_object* v_K_315_, lean_object* v_Pl_316_, lean_object* v_inst_317_, lean_object* v_muV_318_, lean_object* v_etaV_319_, lean_object* v_q_320_, lean_object* v_r_321_, lean_object* v_P_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lp_tree_Formalism_L2_Col_firstValA___redArg(v_inst_317_, v_muV_318_, v_etaV_319_, v_q_320_, v_r_321_, v_P_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValA___boxed(lean_object* v_K_324_, lean_object* v_Pl_325_, lean_object* v_inst_326_, lean_object* v_muV_327_, lean_object* v_etaV_328_, lean_object* v_q_329_, lean_object* v_r_330_, lean_object* v_P_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = lp_tree_Formalism_L2_Col_firstValA(v_K_324_, v_Pl_325_, v_inst_326_, v_muV_327_, v_etaV_328_, v_q_329_, v_r_330_, v_P_331_);
lean_dec(v_r_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB___redArg(lean_object* v_inst_333_, lean_object* v_muV_334_, lean_object* v_q_335_, lean_object* v_r_336_, lean_object* v_m_337_, lean_object* v_t_338_, lean_object* v_P_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_toSemiring_342_; lean_object* v___x_343_; lean_object* v_toMul_344_; lean_object* v___x_345_; lean_object* v_toMonoid_346_; lean_object* v_val_347_; lean_object* v_toNPow_348_; lean_object* v___x_349_; lean_object* v_toRing_350_; lean_object* v___x_351_; lean_object* v_toAddMonoidWithOne_352_; lean_object* v_toNatCast_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_340_ = lp_mathlib_Field_toSemifield___redArg(v_inst_333_);
v___x_341_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_340_);
v_toSemiring_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref_n(v_toSemiring_342_, 2);
lean_dec_ref(v___x_341_);
v___x_343_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_342_);
v_toMul_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_toMul_344_);
lean_dec_ref(v___x_343_);
lean_inc(v_P_339_);
v___x_345_ = lean_apply_1(v_muV_334_, v_P_339_);
v_toMonoid_346_ = lean_ctor_get(v_toSemiring_342_, 1);
lean_inc_ref(v_toMonoid_346_);
lean_dec_ref(v_toSemiring_342_);
v_val_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_347_);
lean_dec_ref(v___x_345_);
v_toNPow_348_ = lean_ctor_get(v_toMonoid_346_, 2);
lean_inc(v_toNPow_348_);
lean_dec_ref(v_toMonoid_346_);
v___x_349_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_333_);
v_toRing_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc_ref(v_toRing_350_);
lean_dec_ref(v___x_349_);
v___x_351_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_350_);
v_toAddMonoidWithOne_352_ = lean_ctor_get(v___x_351_, 1);
lean_inc_ref(v_toAddMonoidWithOne_352_);
lean_dec_ref(v___x_351_);
v_toNatCast_353_ = lean_ctor_get(v_toAddMonoidWithOne_352_, 0);
lean_inc(v_toNatCast_353_);
lean_dec_ref(v_toAddMonoidWithOne_352_);
v___x_354_ = lean_apply_1(v_q_335_, v_P_339_);
v___x_355_ = lean_apply_1(v_toNatCast_353_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_sub(v_m_337_, v___x_356_);
v___x_358_ = lean_nat_mul(v___x_357_, v_t_338_);
lean_dec(v___x_357_);
v___x_359_ = lean_nat_add(v_r_336_, v___x_358_);
lean_dec(v___x_358_);
v___x_360_ = lean_nat_shiftr(v___x_359_, v___x_356_);
lean_dec(v___x_359_);
v___x_361_ = lean_apply_2(v_toNPow_348_, v___x_360_, v___x_355_);
v___x_362_ = lean_apply_2(v_toMul_344_, v_val_347_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB___redArg___boxed(lean_object* v_inst_363_, lean_object* v_muV_364_, lean_object* v_q_365_, lean_object* v_r_366_, lean_object* v_m_367_, lean_object* v_t_368_, lean_object* v_P_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = lp_tree_Formalism_L2_Col_firstValB___redArg(v_inst_363_, v_muV_364_, v_q_365_, v_r_366_, v_m_367_, v_t_368_, v_P_369_);
lean_dec(v_t_368_);
lean_dec(v_m_367_);
lean_dec(v_r_366_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB(lean_object* v_K_371_, lean_object* v_Pl_372_, lean_object* v_inst_373_, lean_object* v_muV_374_, lean_object* v_q_375_, lean_object* v_r_376_, lean_object* v_m_377_, lean_object* v_t_378_, lean_object* v_P_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lp_tree_Formalism_L2_Col_firstValB___redArg(v_inst_373_, v_muV_374_, v_q_375_, v_r_376_, v_m_377_, v_t_378_, v_P_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_firstValB___boxed(lean_object* v_K_381_, lean_object* v_Pl_382_, lean_object* v_inst_383_, lean_object* v_muV_384_, lean_object* v_q_385_, lean_object* v_r_386_, lean_object* v_m_387_, lean_object* v_t_388_, lean_object* v_P_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = lp_tree_Formalism_L2_Col_firstValB(v_K_381_, v_Pl_382_, v_inst_383_, v_muV_384_, v_q_385_, v_r_386_, v_m_387_, v_t_388_, v_P_389_);
lean_dec(v_t_388_);
lean_dec(v_m_387_);
lean_dec(v_r_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum___redArg(lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lp_tree_Formalism_L2_Col_eigSum___redArg(v_inst_391_, v_inst_392_, v_inst_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum___redArg___boxed(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = lp_tree_Formalism_L2_Col_blockSum___redArg(v_inst_395_, v_inst_396_, v_inst_397_);
lean_dec(v_inst_397_);
lean_dec_ref(v_inst_396_);
lean_dec_ref(v_inst_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum(lean_object* v_K_399_, lean_object* v_V_400_, lean_object* v_Pl_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_n_405_, lean_object* v_q_406_, lean_object* v_t_407_, lean_object* v_bl_408_, lean_object* v_op_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lp_tree_Formalism_L2_Col_eigSum___redArg(v_inst_402_, v_inst_403_, v_inst_404_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSum___boxed(lean_object* v_K_411_, lean_object* v_V_412_, lean_object* v_Pl_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_n_417_, lean_object* v_q_418_, lean_object* v_t_419_, lean_object* v_bl_420_, lean_object* v_op_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = lp_tree_Formalism_L2_Col_blockSum(v_K_411_, v_V_412_, v_Pl_413_, v_inst_414_, v_inst_415_, v_inst_416_, v_n_417_, v_q_418_, v_t_419_, v_bl_420_, v_op_421_);
lean_dec(v_op_421_);
lean_dec(v_bl_420_);
lean_dec(v_t_419_);
lean_dec_ref(v_q_418_);
lean_dec(v_n_417_);
lean_dec(v_inst_416_);
lean_dec_ref(v_inst_415_);
lean_dec_ref(v_inst_414_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSumOver(lean_object* v_K_423_, lean_object* v_V_424_, lean_object* v_Pl_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_L_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_n_432_, lean_object* v_q_433_, lean_object* v_t_434_, lean_object* v_bl_435_, lean_object* v_op_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_box(0);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blockSumOver___boxed(lean_object* v_K_438_, lean_object* v_V_439_, lean_object* v_Pl_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_L_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_n_447_, lean_object* v_q_448_, lean_object* v_t_449_, lean_object* v_bl_450_, lean_object* v_op_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = lp_tree_Formalism_L2_Col_blockSumOver(v_K_438_, v_V_439_, v_Pl_440_, v_inst_441_, v_inst_442_, v_inst_443_, v_L_444_, v_inst_445_, v_inst_446_, v_n_447_, v_q_448_, v_t_449_, v_bl_450_, v_op_451_);
lean_dec(v_op_451_);
lean_dec(v_bl_450_);
lean_dec(v_t_449_);
lean_dec_ref(v_q_448_);
lean_dec(v_n_447_);
lean_dec_ref(v_inst_446_);
lean_dec_ref(v_inst_445_);
lean_dec(v_inst_443_);
lean_dec_ref(v_inst_442_);
lean_dec_ref(v_inst_441_);
return v_res_452_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_exSys___closed__0(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_exSys___closed__1(void){
_start:
{
lean_object* v_zero_455_; lean_object* v___x_456_; 
v_zero_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_zero_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exSys(lean_object* v_x_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_zero_461_; uint8_t v_isZero_462_; 
v_zero_461_ = lean_unsigned_to_nat(0u);
v_isZero_462_ = lean_nat_dec_eq(v_x_457_, v_zero_461_);
if (v_isZero_462_ == 1)
{
lean_object* v_snd_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_snd_463_ = lean_ctor_get(v_a_458_, 1);
v___x_464_ = lean_unsigned_to_nat(2u);
v___x_465_ = lp_tree_Formalism_L2_Col_gaussBin(v___x_464_, v___x_464_, v_snd_463_);
v___x_466_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_465_);
return v___x_466_;
}
else
{
lean_object* v_one_467_; lean_object* v_n_468_; uint8_t v_isZero_469_; lean_object* v_snd_470_; uint8_t v___x_471_; 
v_one_467_ = lean_unsigned_to_nat(1u);
v_n_468_ = lean_nat_sub(v_x_457_, v_one_467_);
v_isZero_469_ = lean_nat_dec_eq(v_n_468_, v_zero_461_);
lean_dec(v_n_468_);
v_snd_470_ = lean_ctor_get(v_a_458_, 1);
v___x_471_ = lean_nat_dec_eq(v_snd_470_, v_zero_461_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = lean_nat_dec_eq(v_snd_470_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_obj_once(&lp_tree_Formalism_L2_Col_exSys___closed__1, &lp_tree_Formalism_L2_Col_exSys___closed__1_once, _init_lp_tree_Formalism_L2_Col_exSys___closed__1);
return v___x_474_;
}
else
{
goto v___jp_459_;
}
}
else
{
goto v___jp_459_;
}
}
v___jp_459_:
{
lean_object* v___x_460_; 
v___x_460_ = lean_obj_once(&lp_tree_Formalism_L2_Col_exSys___closed__0, &lp_tree_Formalism_L2_Col_exSys___closed__0_once, _init_lp_tree_Formalism_L2_Col_exSys___closed__0);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exSys___boxed(lean_object* v_x_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = lp_tree_Formalism_L2_Col_exSys(v_x_475_, v_a_476_);
lean_dec_ref(v_a_476_);
lean_dec(v_x_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_L2_Col_exOp_spec__0___lam__0(lean_object* v_i_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_apply_1(v___y_479_, v_i_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_proj___at___00Formalism_L2_Col_exOp_spec__0(lean_object* v_i_481_){
_start:
{
lean_object* v___f_482_; 
v___f_482_ = lean_alloc_closure((void*)(lp_tree_LinearMap_proj___at___00Formalism_L2_Col_exOp_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_482_, 0, v_i_481_);
return v___f_482_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_L2_Col_exOp_spec__1___lam__0(lean_object* v_f_483_, lean_object* v_c_484_, lean_object* v_i_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_apply_2(v_f_483_, v_i_485_, v_c_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_pi___at___00Formalism_L2_Col_exOp_spec__1(lean_object* v_f_487_){
_start:
{
lean_object* v___f_488_; 
v___f_488_ = lean_alloc_closure((void*)(lp_tree_LinearMap_pi___at___00Formalism_L2_Col_exOp_spec__1___lam__0), 3, 1);
lean_closure_set(v___f_488_, 0, v_f_487_);
return v___f_488_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exOp___lam__0(lean_object* v_x_489_, lean_object* v_j_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lp_tree_Formalism_L2_Col_exSys(v_j_490_, v_x_489_);
v___x_493_ = lean_apply_1(v___y_491_, v_j_490_);
v___x_494_ = l_Rat_mul(v___x_492_, v___x_493_);
lean_dec_ref(v___x_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exOp___lam__0___boxed(lean_object* v_x_495_, lean_object* v_j_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = lp_tree_Formalism_L2_Col_exOp___lam__0(v_x_495_, v_j_496_, v___y_497_);
lean_dec_ref(v_x_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_exOp(lean_object* v_x_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___f_501_; 
v___f_500_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_exOp___lam__0___boxed), 3, 1);
lean_closure_set(v___f_500_, 0, v_x_499_);
v___f_501_ = lean_alloc_closure((void*)(lp_tree_LinearMap_pi___at___00Formalism_L2_Col_exOp_spec__1___lam__0), 3, 1);
lean_closure_set(v___f_501_, 0, v___f_500_);
return v___f_501_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___redArg(lean_object* v_x_502_, lean_object* v_h__1_503_, lean_object* v_h__2_504_){
_start:
{
lean_object* v_zero_505_; uint8_t v_isZero_506_; 
v_zero_505_ = lean_unsigned_to_nat(0u);
v_isZero_506_ = lean_nat_dec_eq(v_x_502_, v_zero_505_);
if (v_isZero_506_ == 1)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_h__2_504_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_1(v_h__1_503_, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v_one_509_; lean_object* v_n_510_; uint8_t v_isZero_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_h__1_503_);
v_one_509_ = lean_unsigned_to_nat(1u);
v_n_510_ = lean_nat_sub(v_x_502_, v_one_509_);
v_isZero_511_ = lean_nat_dec_eq(v_n_510_, v_zero_505_);
lean_dec(v_n_510_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_1(v_h__2_504_, v___x_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___redArg___boxed(lean_object* v_x_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___redArg(v_x_514_, v_h__1_515_, v_h__2_516_);
lean_dec(v_x_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter(lean_object* v_motive_518_, lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
lean_object* v_zero_522_; uint8_t v_isZero_523_; 
v_zero_522_ = lean_unsigned_to_nat(0u);
v_isZero_523_ = lean_nat_dec_eq(v_x_519_, v_zero_522_);
if (v_isZero_523_ == 1)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_521_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_apply_1(v_h__1_520_, v___x_524_);
return v___x_525_;
}
else
{
lean_object* v_one_526_; lean_object* v_n_527_; uint8_t v_isZero_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_h__1_520_);
v_one_526_ = lean_unsigned_to_nat(1u);
v_n_527_ = lean_nat_sub(v_x_519_, v_one_526_);
v_isZero_528_ = lean_nat_dec_eq(v_n_527_, v_zero_522_);
lean_dec(v_n_527_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_apply_1(v_h__2_521_, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter___boxed(lean_object* v_motive_531_, lean_object* v_x_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = lp_tree___private_Formalism_LocalToGlobal_Columns_HeckeSp_0__Formalism_L2_Col_exSys_match__1_splitter(v_motive_531_, v_x_532_, v_h__1_533_, v_h__2_534_);
lean_dec(v_x_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_quotMapEquiv___redArg(lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_g_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_540_ = lp_mathlib_AddSubgroupClass_toAddGroup___redArg(v_inst_537_);
v___f_541_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_smul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_541_, 0, v_inst_538_);
v___x_542_ = lean_box(0);
v___x_543_ = lp_mathlib_LinearEquiv_submoduleMap___redArg(v_g_539_);
lean_inc_ref(v___f_541_);
lean_inc_ref(v___x_540_);
lean_inc_ref(v_inst_536_);
v___x_544_ = lp_mathlib_Submodule_Quotient_equiv___redArg(v_inst_536_, v_inst_536_, v___x_540_, v___f_541_, v___x_540_, v___f_541_, v___x_542_, v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_quotMapEquiv(lean_object* v_R_545_, lean_object* v_W_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_g_550_, lean_object* v_A_551_, lean_object* v_B_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lp_tree_Formalism_L2_Col_quotMapEquiv___redArg(v_inst_547_, v_inst_548_, v_inst_549_, v_g_550_);
return v___x_553_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_DecoFin(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_DecoFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
