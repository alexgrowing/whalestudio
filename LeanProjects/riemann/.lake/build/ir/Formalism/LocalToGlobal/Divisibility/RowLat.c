// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.RowLat
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec public import Formalism.LocalToGlobal.Divisibility.Frames public import Formalism.LocalToGlobal.Columns.HeckeSp public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_Pi_addCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* lp_mathlib_AddSubgroupClass_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Submodule_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_eigSum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* lp_mathlib_AddSubmonoidClass_toAddMonoid___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_addMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_perpOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_perpOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ccOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ccOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_perpOf(lean_object* v_K_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_n_4_, lean_object* v_H_5_, lean_object* v_Z_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_perpOf___boxed(lean_object* v_K_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_n_11_, lean_object* v_H_12_, lean_object* v_Z_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_tree_Formalism_L2_DIV_perpOf(v_K_8_, v_inst_9_, v_inst_10_, v_n_11_, v_H_12_, v_Z_13_);
lean_dec(v_H_12_);
lean_dec(v_n_11_);
lean_dec(v_inst_10_);
lean_dec_ref(v_inst_9_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg___lam__0(lean_object* v_toMonoid_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; lean_object* v_toOne_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
v___x_17_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_15_);
v_toOne_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
lean_object* v_unused_26_; 
v_unused_26_ = lean_ctor_get(v___x_17_, 1);
lean_dec(v_unused_26_);
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_toOne_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
lean_inc(v_toOne_18_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v_toOne_18_);
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_toOne_18_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_toOne_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg___lam__0___boxed(lean_object* v_toMonoid_27_, lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_L2_DIV_Lvl_full___redArg___lam__0(v_toMonoid_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec_ref(v_toMonoid_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg(lean_object* v_inst_30_, lean_object* v_X_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_toSemiring_34_; lean_object* v_toMonoid_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_44_; 
v___x_32_ = lp_mathlib_Field_toSemifield___redArg(v_inst_30_);
v___x_33_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_32_);
v_toSemiring_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc_ref(v_toSemiring_34_);
lean_dec_ref(v___x_33_);
v_toMonoid_35_ = lean_ctor_get(v_toSemiring_34_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v_toSemiring_34_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; lean_object* v_unused_46_; 
v_unused_45_ = lean_ctor_get(v_toSemiring_34_, 2);
lean_dec(v_unused_45_);
v_unused_46_ = lean_ctor_get(v_toSemiring_34_, 0);
lean_dec(v_unused_46_);
v___x_37_ = v_toSemiring_34_;
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_toMonoid_35_);
lean_dec(v_toSemiring_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___f_40_; lean_object* v___x_42_; 
v___x_39_ = lean_box(0);
v___f_40_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_Lvl_full___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_40_, 0, v_toMonoid_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 2, v___f_40_);
lean_ctor_set(v___x_37_, 1, v___x_39_);
lean_ctor_set(v___x_37_, 0, v_X_31_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_X_31_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v___f_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___redArg___boxed(lean_object* v_inst_47_, lean_object* v_X_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_tree_Formalism_L2_DIV_Lvl_full___redArg(v_inst_47_, v_X_48_);
lean_dec_ref(v_inst_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full(lean_object* v_K_50_, lean_object* v_G_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_X_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_tree_Formalism_L2_DIV_Lvl_full___redArg(v_inst_52_, v_X_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_Lvl_full___boxed(lean_object* v_K_56_, lean_object* v_G_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_X_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_DIV_Lvl_full(v_K_56_, v_G_57_, v_inst_58_, v_inst_59_, v_X_60_);
lean_dec_ref(v_inst_59_);
lean_dec_ref(v_inst_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__0(lean_object* v_a_62_, lean_object* v_r_63_, lean_object* v_modV_64_, lean_object* v_t_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_toFun_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_toFun_68_ = lean_ctor_get(v_a_62_, 1);
lean_inc(v_toFun_68_);
lean_dec_ref(v_a_62_);
lean_inc(v_t_65_);
v___x_69_ = lean_apply_1(v_toFun_68_, v_t_65_);
v___x_70_ = lean_apply_3(v_r_63_, v_t_65_, v___y_66_, v___y_67_);
v___x_71_ = lean_apply_2(v_modV_64_, v___x_69_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__1(lean_object* v_toAddMonoid_72_, lean_object* v_i_73_){
_start:
{
lean_inc_ref(v_toAddMonoid_72_);
return v_toAddMonoid_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__1___boxed(lean_object* v_toAddMonoid_74_, lean_object* v_i_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__1(v_toAddMonoid_74_, v_i_75_);
lean_dec(v_i_75_);
lean_dec_ref(v_toAddMonoid_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg(lean_object* v_S_77_, lean_object* v_inst_78_, lean_object* v_r_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_addV_81_; lean_object* v_modV_82_; lean_object* v_toAddMonoid_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_addV_81_ = lean_ctor_get(v_S_77_, 1);
lean_inc_ref(v_addV_81_);
v_modV_82_ = lean_ctor_get(v_S_77_, 2);
lean_inc(v_modV_82_);
lean_dec_ref(v_S_77_);
v_toAddMonoid_83_ = lean_ctor_get(v_addV_81_, 0);
lean_inc_ref(v_toAddMonoid_83_);
lean_dec_ref(v_addV_81_);
v___f_84_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__0), 6, 3);
lean_closure_set(v___f_84_, 0, v_a_80_);
lean_closure_set(v___f_84_, 1, v_r_79_);
lean_closure_set(v___f_84_, 2, v_modV_82_);
v___f_85_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_85_, 0, v_toAddMonoid_83_);
v___x_86_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_85_);
v___x_87_ = lp_mathlib_AddSubmonoidClass_toAddMonoid___redArg(v___x_86_);
v___x_88_ = lp_mathlib_LinearMap_addMonoid___redArg(v___x_87_);
v___x_89_ = lp_mathlib_Finset_sum___redArg(v___x_88_, v_inst_78_, v___f_84_);
lean_dec_ref(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp(lean_object* v_K_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_S_94_, lean_object* v_G_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_r_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_tree_Formalism_L2_DIV_CSD_gaOp___redArg(v_S_94_, v_inst_97_, v_r_98_, v_a_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_CSD_gaOp___boxed(lean_object* v_K_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_S_105_, lean_object* v_G_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_r_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_tree_Formalism_L2_DIV_CSD_gaOp(v_K_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_S_105_, v_G_106_, v_inst_107_, v_inst_108_, v_r_109_, v_a_110_);
lean_dec_ref(v_inst_107_);
lean_dec(v_inst_104_);
lean_dec_ref(v_inst_102_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0(lean_object* v_B_112_, lean_object* v_i_113_){
_start:
{
lean_object* v_S_114_; lean_object* v_addV_115_; 
v_S_114_ = lean_ctor_get(v_B_112_, 0);
v_addV_115_ = lean_ctor_get(v_S_114_, 1);
lean_inc_ref(v_addV_115_);
return v_addV_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0___boxed(lean_object* v_B_116_, lean_object* v_i_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0(v_B_116_, v_i_117_);
lean_dec(v_i_117_);
lean_dec_ref(v_B_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg(lean_object* v_inst_119_, lean_object* v_B_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v_S_123_; lean_object* v_modV_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___f_127_; lean_object* v___x_128_; 
lean_inc_ref(v_B_120_);
v___f_121_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_121_, 0, v_B_120_);
v___x_122_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_121_);
v_S_123_ = lean_ctor_get(v_B_120_, 0);
lean_inc_ref(v_S_123_);
lean_dec_ref(v_B_120_);
v_modV_124_ = lean_ctor_get(v_S_123_, 2);
lean_inc(v_modV_124_);
lean_dec_ref(v_S_123_);
v___x_125_ = lp_mathlib_Pi_Function_module___redArg(v_modV_124_);
v___x_126_ = lp_mathlib_AddSubgroupClass_toAddGroup___redArg(v___x_122_);
v___f_127_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_smul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_127_, 0, v___x_125_);
v___x_128_ = lp_tree_Formalism_L2_Col_eigSum___redArg(v_inst_119_, v___x_126_, v___f_127_);
lean_dec_ref(v___f_127_);
lean_dec_ref(v___x_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___boxed(lean_object* v_inst_129_, lean_object* v_B_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg(v_inst_129_, v_B_130_);
lean_dec_ref(v_inst_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH(lean_object* v_K_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_G_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_Pl0_139_, lean_object* v_B_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg(v_inst_133_, v_B_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_ZH___boxed(lean_object* v_K_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_G_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_Pl0_149_, lean_object* v_B_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = lp_tree_Formalism_L2_DIV_BlockDat_ZH(v_K_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_G_146_, v_inst_147_, v_inst_148_, v_Pl0_149_, v_B_150_);
lean_dec(v_inst_148_);
lean_dec_ref(v_inst_147_);
lean_dec(v_inst_145_);
lean_dec_ref(v_inst_143_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF___redArg(lean_object* v_inst_152_, lean_object* v_B_153_){
_start:
{
lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v_S_156_; lean_object* v_modV_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___x_161_; 
lean_inc_ref(v_B_153_);
v___f_154_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_BlockDat_ZH___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_154_, 0, v_B_153_);
v___x_155_ = lp_mathlib_Pi_addCommGroup___redArg(v___f_154_);
v_S_156_ = lean_ctor_get(v_B_153_, 0);
lean_inc_ref(v_S_156_);
lean_dec_ref(v_B_153_);
v_modV_157_ = lean_ctor_get(v_S_156_, 2);
lean_inc(v_modV_157_);
lean_dec_ref(v_S_156_);
v___x_158_ = lp_mathlib_Pi_Function_module___redArg(v_modV_157_);
v___x_159_ = lp_mathlib_AddSubgroupClass_toAddGroup___redArg(v___x_155_);
v___f_160_ = lean_alloc_closure((void*)(lp_mathlib_Submodule_smul___redArg___lam__0), 3, 1);
lean_closure_set(v___f_160_, 0, v___x_158_);
v___x_161_ = lp_tree_Formalism_L2_Col_eigSum___redArg(v_inst_152_, v___x_159_, v___f_160_);
lean_dec_ref(v___f_160_);
lean_dec_ref(v___x_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF___redArg___boxed(lean_object* v_inst_162_, lean_object* v_B_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = lp_tree_Formalism_L2_DIV_BlockDat_partF___redArg(v_inst_162_, v_B_163_);
lean_dec_ref(v_inst_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF(lean_object* v_K_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_G_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_Pl0_172_, lean_object* v_B_173_, lean_object* v_Sg_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lp_tree_Formalism_L2_DIV_BlockDat_partF___redArg(v_inst_166_, v_B_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_BlockDat_partF___boxed(lean_object* v_K_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_G_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_Pl0_183_, lean_object* v_B_184_, lean_object* v_Sg_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = lp_tree_Formalism_L2_DIV_BlockDat_partF(v_K_176_, v_inst_177_, v_inst_178_, v_inst_179_, v_G_180_, v_inst_181_, v_inst_182_, v_Pl0_183_, v_B_184_, v_Sg_185_);
lean_dec_ref(v_Sg_185_);
lean_dec(v_inst_182_);
lean_dec_ref(v_inst_181_);
lean_dec(v_inst_179_);
lean_dec_ref(v_inst_177_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl___redArg(lean_object* v_F_187_, lean_object* v_P_188_, lean_object* v_00_u03c8_189_){
_start:
{
lean_object* v_X_190_; lean_object* v___x_191_; 
v_X_190_ = lean_ctor_get(v_F_187_, 2);
lean_inc(v_X_190_);
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v_X_190_);
lean_ctor_set(v___x_191_, 1, v_P_188_);
lean_ctor_set(v___x_191_, 2, v_00_u03c8_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl___redArg___boxed(lean_object* v_F_192_, lean_object* v_P_193_, lean_object* v_00_u03c8_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = lp_tree_Formalism_L2_DIV_DefFam_lvl___redArg(v_F_192_, v_P_193_, v_00_u03c8_194_);
lean_dec_ref(v_F_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl(lean_object* v_K_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_G_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_Pl0_203_, lean_object* v_T_204_, lean_object* v_J_205_, lean_object* v_F_206_, lean_object* v_P_207_, lean_object* v_00_u03c8_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lp_tree_Formalism_L2_DIV_DefFam_lvl___redArg(v_F_206_, v_P_207_, v_00_u03c8_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvl___boxed(lean_object* v_K_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_G_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_Pl0_217_, lean_object* v_T_218_, lean_object* v_J_219_, lean_object* v_F_220_, lean_object* v_P_221_, lean_object* v_00_u03c8_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_tree_Formalism_L2_DIV_DefFam_lvl(v_K_210_, v_inst_211_, v_inst_212_, v_inst_213_, v_G_214_, v_inst_215_, v_inst_216_, v_Pl0_217_, v_T_218_, v_J_219_, v_F_220_, v_P_221_, v_00_u03c8_222_);
lean_dec_ref(v_F_220_);
lean_dec(v_inst_216_);
lean_dec_ref(v_inst_215_);
lean_dec(v_inst_213_);
lean_dec_ref(v_inst_211_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg___lam__0(lean_object* v_00_u03c8_224_, lean_object* v_g_225_){
_start:
{
lean_object* v___x_226_; lean_object* v_val_227_; lean_object* v_inv_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v___x_226_ = lean_apply_1(v_00_u03c8_224_, v_g_225_);
v_val_227_ = lean_ctor_get(v___x_226_, 0);
v_inv_228_ = lean_ctor_get(v___x_226_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_inv_228_);
lean_inc(v_val_227_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_val_227_);
lean_ctor_set(v___x_230_, 0, v_inv_228_);
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_inv_228_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_val_227_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg(lean_object* v_F_236_, lean_object* v_P_237_, lean_object* v_00_u03c8_238_){
_start:
{
lean_object* v_X_239_; lean_object* v___f_240_; lean_object* v___x_241_; 
v_X_239_ = lean_ctor_get(v_F_236_, 2);
v___f_240_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg___lam__0), 2, 1);
lean_closure_set(v___f_240_, 0, v_00_u03c8_238_);
lean_inc(v_X_239_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_X_239_);
lean_ctor_set(v___x_241_, 1, v_P_237_);
lean_ctor_set(v___x_241_, 2, v___f_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg___boxed(lean_object* v_F_242_, lean_object* v_P_243_, lean_object* v_00_u03c8_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg(v_F_242_, v_P_243_, v_00_u03c8_244_);
lean_dec_ref(v_F_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA(lean_object* v_K_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_G_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_Pl0_253_, lean_object* v_T_254_, lean_object* v_J_255_, lean_object* v_F_256_, lean_object* v_P_257_, lean_object* v_00_u03c8_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lp_tree_Formalism_L2_DIV_DefFam_lvlA___redArg(v_F_256_, v_P_257_, v_00_u03c8_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_DefFam_lvlA___boxed(lean_object* v_K_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_G_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_Pl0_267_, lean_object* v_T_268_, lean_object* v_J_269_, lean_object* v_F_270_, lean_object* v_P_271_, lean_object* v_00_u03c8_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = lp_tree_Formalism_L2_DIV_DefFam_lvlA(v_K_260_, v_inst_261_, v_inst_262_, v_inst_263_, v_G_264_, v_inst_265_, v_inst_266_, v_Pl0_267_, v_T_268_, v_J_269_, v_F_270_, v_P_271_, v_00_u03c8_272_);
lean_dec_ref(v_F_270_);
lean_dec(v_inst_266_);
lean_dec_ref(v_inst_265_);
lean_dec(v_inst_263_);
lean_dec_ref(v_inst_261_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ccOf(lean_object* v_K_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_Bs_278_, lean_object* v_Df_279_, lean_object* v_S_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_ccOf___boxed(lean_object* v_K_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_Bs_286_, lean_object* v_Df_287_, lean_object* v_S_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_tree_Formalism_L2_DIV_ccOf(v_K_282_, v_inst_283_, v_inst_284_, v_inst_285_, v_Bs_286_, v_Df_287_, v_S_288_);
lean_dec_ref(v_S_288_);
lean_dec_ref(v_Df_287_);
lean_dec_ref(v_Bs_286_);
lean_dec(v_inst_285_);
lean_dec_ref(v_inst_283_);
return v_res_289_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_Frames(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefSide(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLat(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_Frames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_IndefiniteForms_IndefSide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
