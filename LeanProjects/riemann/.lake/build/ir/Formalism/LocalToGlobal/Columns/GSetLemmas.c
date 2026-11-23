// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.GSetLemmas
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq public import Formalism.ThetaLiftIndependence.Statement public import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_LinearEquiv_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_SubMulAction_instSMulSubtypeMem___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_onCl___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_subtypeEquiv___redArg(lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_symm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_symm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_trans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_trans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fibre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fibre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twSgn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twSgn___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twSgn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv___redArg(lean_object* v_e_1_){
_start:
{
lean_object* v_eG_2_; lean_object* v___x_3_; 
v_eG_2_ = lean_ctor_get(v_e_1_, 0);
lean_inc_ref(v_eG_2_);
lean_dec_ref(v_e_1_);
v___x_3_ = lp_mathlib_Equiv_subtypeEquiv___redArg(v_eG_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv(lean_object* v_K_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_S_8_, lean_object* v_S_x27_9_, lean_object* v_e_10_, lean_object* v_d_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv___redArg(v_e_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv___boxed(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_S_17_, lean_object* v_S_x27_18_, lean_object* v_e_19_, lean_object* v_d_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_Col_GSD_Iso_stabEquiv(v_K_13_, v_inst_14_, v_inst_15_, v_inst_16_, v_S_17_, v_S_x27_18_, v_e_19_, v_d_20_);
lean_dec(v_d_20_);
lean_dec_ref(v_S_x27_18_);
lean_dec_ref(v_S_17_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_14_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___redArg___lam__0(lean_object* v_e_22_, lean_object* v_s_23_, lean_object* v_c_x27_24_){
_start:
{
lean_object* v_eD_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_toFun_28_; lean_object* v_toFun_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_eD_25_ = lean_ctor_get(v_e_22_, 1);
lean_inc_ref(v_eD_25_);
v___x_26_ = lp_tree_Formalism_L2_Col_GSD_Iso_onCl___redArg(v_e_22_);
v___x_27_ = lp_mathlib_Equiv_symm___redArg(v___x_26_);
v_toFun_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_toFun_28_);
lean_dec_ref(v___x_27_);
v_toFun_29_ = lean_ctor_get(v_eD_25_, 0);
lean_inc(v_toFun_29_);
lean_dec_ref(v_eD_25_);
v___x_30_ = lean_apply_1(v_toFun_28_, v_c_x27_24_);
v___x_31_ = lean_apply_1(v_s_23_, v___x_30_);
v___x_32_ = lean_apply_1(v_toFun_29_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___redArg(lean_object* v_e_33_, lean_object* v_s_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___redArg___lam__0), 3, 2);
lean_closure_set(v___f_35_, 0, v_e_33_);
lean_closure_set(v___f_35_, 1, v_s_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec(lean_object* v_K_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_S_40_, lean_object* v_S_x27_41_, lean_object* v_e_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___f_44_; 
v___f_44_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___redArg___lam__0), 3, 2);
lean_closure_set(v___f_44_, 0, v_e_42_);
lean_closure_set(v___f_44_, 1, v_s_43_);
return v___f_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_mapSec___boxed(lean_object* v_K_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_S_49_, lean_object* v_S_x27_50_, lean_object* v_e_51_, lean_object* v_s_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_tree_Formalism_L2_Col_GSD_Iso_mapSec(v_K_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_S_49_, v_S_x27_50_, v_e_51_, v_s_52_);
lean_dec_ref(v_S_x27_50_);
lean_dec_ref(v_S_49_);
lean_dec(v_inst_48_);
lean_dec_ref(v_inst_46_);
return v_res_53_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___closed__0(void){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg(lean_object* v_inst_55_, lean_object* v_S_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_addV_59_; lean_object* v_toSemiring_60_; lean_object* v_modV_61_; lean_object* v_toAddMonoid_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_57_ = lp_mathlib_Field_toSemifield___redArg(v_inst_55_);
v___x_58_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_57_);
v_addV_59_ = lean_ctor_get(v_S_56_, 2);
v_toSemiring_60_ = lean_ctor_get(v___x_58_, 0);
lean_inc_ref(v_toSemiring_60_);
lean_dec_ref(v___x_58_);
v_modV_61_ = lean_ctor_get(v_S_56_, 3);
v_toAddMonoid_62_ = lean_ctor_get(v_addV_59_, 0);
v___x_63_ = lean_obj_once(&lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___closed__0, &lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___closed__0);
v___x_64_ = lp_mathlib_LinearEquiv_refl(lean_box(0), lean_box(0), v_toSemiring_60_, v_toAddMonoid_62_, v_modV_61_);
lean_dec_ref(v_toSemiring_60_);
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg___boxed(lean_object* v_inst_66_, lean_object* v_S_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg(v_inst_66_, v_S_67_);
lean_dec_ref(v_S_67_);
lean_dec_ref(v_inst_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl(lean_object* v_K_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_S_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_L2_Col_GSD_Iso_refl___redArg(v_inst_70_, v_S_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_refl___boxed(lean_object* v_K_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_S_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_tree_Formalism_L2_Col_GSD_Iso_refl(v_K_75_, v_inst_76_, v_inst_77_, v_inst_78_, v_S_79_);
lean_dec_ref(v_S_79_);
lean_dec(v_inst_78_);
lean_dec_ref(v_inst_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_symm___redArg(lean_object* v_e_81_){
_start:
{
lean_object* v_eG_82_; lean_object* v_eD_83_; lean_object* v_eV_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_94_; 
v_eG_82_ = lean_ctor_get(v_e_81_, 0);
v_eD_83_ = lean_ctor_get(v_e_81_, 1);
v_eV_84_ = lean_ctor_get(v_e_81_, 2);
v_isSharedCheck_94_ = !lean_is_exclusive(v_e_81_);
if (v_isSharedCheck_94_ == 0)
{
v___x_86_ = v_e_81_;
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_eV_84_);
lean_inc(v_eD_83_);
lean_inc(v_eG_82_);
lean_dec(v_e_81_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_88_ = lp_mathlib_Equiv_symm___redArg(v_eG_82_);
v___x_89_ = lp_mathlib_Equiv_symm___redArg(v_eD_83_);
v___x_90_ = lp_mathlib_LinearEquiv_symm___redArg(v_eV_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 2, v___x_90_);
lean_ctor_set(v___x_86_, 1, v___x_89_);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_92_ = v___x_86_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_symm(lean_object* v_K_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_S_99_, lean_object* v_S_x27_100_, lean_object* v_e_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_tree_Formalism_L2_Col_GSD_Iso_symm___redArg(v_e_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_symm___boxed(lean_object* v_K_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_S_107_, lean_object* v_S_x27_108_, lean_object* v_e_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_tree_Formalism_L2_Col_GSD_Iso_symm(v_K_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_S_107_, v_S_x27_108_, v_e_109_);
lean_dec_ref(v_S_x27_108_);
lean_dec_ref(v_S_107_);
lean_dec(v_inst_106_);
lean_dec_ref(v_inst_104_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_trans___redArg(lean_object* v_e_111_, lean_object* v_e_x27_112_){
_start:
{
lean_object* v_eG_113_; lean_object* v_eD_114_; lean_object* v_eV_115_; lean_object* v_eG_116_; lean_object* v_eD_117_; lean_object* v_eV_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_eG_113_ = lean_ctor_get(v_e_111_, 0);
lean_inc_ref(v_eG_113_);
v_eD_114_ = lean_ctor_get(v_e_111_, 1);
lean_inc_ref(v_eD_114_);
v_eV_115_ = lean_ctor_get(v_e_111_, 2);
lean_inc_ref(v_eV_115_);
lean_dec_ref(v_e_111_);
v_eG_116_ = lean_ctor_get(v_e_x27_112_, 0);
v_eD_117_ = lean_ctor_get(v_e_x27_112_, 1);
v_eV_118_ = lean_ctor_get(v_e_x27_112_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_e_x27_112_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_e_x27_112_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_eV_118_);
lean_inc(v_eD_117_);
lean_inc(v_eG_116_);
lean_dec(v_e_x27_112_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_122_ = lp_mathlib_Equiv_trans___redArg(v_eG_113_, v_eG_116_);
v___x_123_ = lp_mathlib_Equiv_trans___redArg(v_eD_114_, v_eD_117_);
v___x_124_ = lp_mathlib_LinearEquiv_trans___redArg(v_eV_115_, v_eV_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 2, v___x_124_);
lean_ctor_set(v___x_120_, 1, v___x_123_);
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_trans(lean_object* v_K_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_S_133_, lean_object* v_S_x27_134_, lean_object* v_e_135_, lean_object* v_S_x27_x27_136_, lean_object* v_e_x27_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_tree_Formalism_L2_Col_GSD_Iso_trans___redArg(v_e_135_, v_e_x27_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_Iso_trans___boxed(lean_object* v_K_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_S_143_, lean_object* v_S_x27_144_, lean_object* v_e_145_, lean_object* v_S_x27_x27_146_, lean_object* v_e_x27_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_tree_Formalism_L2_Col_GSD_Iso_trans(v_K_139_, v_inst_140_, v_inst_141_, v_inst_142_, v_S_143_, v_S_x27_144_, v_e_145_, v_S_x27_x27_146_, v_e_x27_147_);
lean_dec_ref(v_S_x27_x27_146_);
lean_dec_ref(v_S_x27_144_);
lean_dec_ref(v_S_143_);
lean_dec(v_inst_142_);
lean_dec_ref(v_inst_140_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___redArg___lam__0(lean_object* v_Nab_149_, lean_object* v_t_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_1(v_Nab_149_, v_t_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___redArg___lam__1(lean_object* v_Del_152_, lean_object* v_t_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_apply_1(v_Del_152_, v_t_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___redArg(lean_object* v_S_155_){
_start:
{
lean_object* v_grpG_156_; lean_object* v_actD_157_; lean_object* v_addV_158_; lean_object* v_modV_159_; lean_object* v_modOV_160_; lean_object* v_fin_u03b9V_161_; lean_object* v_dec_u03b9V_162_; lean_object* v_bV_163_; lean_object* v_pair_164_; lean_object* v_00_u03c1_165_; lean_object* v_Nab_166_; lean_object* v_Del_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_177_; 
v_grpG_156_ = lean_ctor_get(v_S_155_, 0);
v_actD_157_ = lean_ctor_get(v_S_155_, 1);
v_addV_158_ = lean_ctor_get(v_S_155_, 2);
v_modV_159_ = lean_ctor_get(v_S_155_, 3);
v_modOV_160_ = lean_ctor_get(v_S_155_, 4);
v_fin_u03b9V_161_ = lean_ctor_get(v_S_155_, 5);
v_dec_u03b9V_162_ = lean_ctor_get(v_S_155_, 6);
v_bV_163_ = lean_ctor_get(v_S_155_, 7);
v_pair_164_ = lean_ctor_get(v_S_155_, 8);
v_00_u03c1_165_ = lean_ctor_get(v_S_155_, 9);
v_Nab_166_ = lean_ctor_get(v_S_155_, 10);
v_Del_167_ = lean_ctor_get(v_S_155_, 11);
v_isSharedCheck_177_ = !lean_is_exclusive(v_S_155_);
if (v_isSharedCheck_177_ == 0)
{
v___x_169_ = v_S_155_;
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_Del_167_);
lean_inc(v_Nab_166_);
lean_inc(v_00_u03c1_165_);
lean_inc(v_pair_164_);
lean_inc(v_bV_163_);
lean_inc(v_dec_u03b9V_162_);
lean_inc(v_fin_u03b9V_161_);
lean_inc(v_modOV_160_);
lean_inc(v_modV_159_);
lean_inc(v_addV_158_);
lean_inc(v_actD_157_);
lean_inc(v_grpG_156_);
lean_dec(v_S_155_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_175_; 
v___f_171_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_GSD_restr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_171_, 0, v_Nab_166_);
v___f_172_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_GSD_restr___redArg___lam__1), 2, 1);
lean_closure_set(v___f_172_, 0, v_Del_167_);
v___f_173_ = lean_alloc_closure((void*)(lp_mathlib_SubMulAction_instSMulSubtypeMem___redArg___lam__0), 3, 1);
lean_closure_set(v___f_173_, 0, v_actD_157_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 11, v___f_172_);
lean_ctor_set(v___x_169_, 10, v___f_171_);
lean_ctor_set(v___x_169_, 1, v___f_173_);
v___x_175_ = v___x_169_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_grpG_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___f_173_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_addV_158_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_modV_159_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_modOV_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v_fin_u03b9V_161_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_dec_u03b9V_162_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_bV_163_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_pair_164_);
lean_ctor_set(v_reuseFailAlloc_176_, 9, v_00_u03c1_165_);
lean_ctor_set(v_reuseFailAlloc_176_, 10, v___f_171_);
lean_ctor_set(v_reuseFailAlloc_176_, 11, v___f_172_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr(lean_object* v_K_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_S_182_, lean_object* v_T_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lp_tree_Formalism_L2_Col_GSD_restr___redArg(v_S_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_restr___boxed(lean_object* v_K_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_S_189_, lean_object* v_T_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_tree_Formalism_L2_Col_GSD_restr(v_K_185_, v_inst_186_, v_inst_187_, v_inst_188_, v_S_189_, v_T_190_);
lean_dec(v_inst_188_);
lean_dec_ref(v_inst_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fibre(lean_object* v_G_192_, lean_object* v_D_193_, lean_object* v_D_u2080_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_pr_198_, lean_object* v_hpr_199_, lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_fibre___boxed(lean_object* v_G_202_, lean_object* v_D_203_, lean_object* v_D_u2080_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_pr_208_, lean_object* v_hpr_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_tree_Formalism_L2_Col_fibre(v_G_202_, v_D_203_, v_D_u2080_204_, v_inst_205_, v_inst_206_, v_inst_207_, v_pr_208_, v_hpr_209_, v_x_210_);
lean_dec(v_x_210_);
lean_dec(v_pr_208_);
lean_dec(v_inst_207_);
lean_dec(v_inst_206_);
lean_dec_ref(v_inst_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twSgn___redArg___lam__0(lean_object* v___x_212_, lean_object* v_toIntCast_213_, lean_object* v_g_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_val_216_; lean_object* v___x_217_; lean_object* v_toMul_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_val_216_ = lean_ctor_get(v_g_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v_g_214_);
v___x_217_ = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(v___x_212_);
v_toMul_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_toMul_218_);
lean_dec_ref(v___x_217_);
v___x_219_ = lean_apply_1(v_toIntCast_213_, v_val_216_);
v___x_220_ = lean_apply_2(v_toMul_218_, v___x_219_, v___y_215_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twSgn___redArg(lean_object* v_inst_221_){
_start:
{
lean_object* v_toCommRing_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_toRing_226_; lean_object* v___x_227_; lean_object* v_toIntCast_228_; lean_object* v___f_229_; 
v_toCommRing_222_ = lean_ctor_get(v_inst_221_, 0);
v___x_223_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_222_);
v___x_224_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_223_);
v___x_225_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_221_);
v_toRing_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_toRing_226_);
lean_dec_ref(v___x_225_);
v___x_227_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_226_);
v_toIntCast_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_toIntCast_228_);
lean_dec_ref(v___x_227_);
v___f_229_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_GSD_twSgn___redArg___lam__0), 4, 2);
lean_closure_set(v___f_229_, 0, v___x_224_);
lean_closure_set(v___f_229_, 1, v_toIntCast_228_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twSgn(lean_object* v_K_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lp_tree_Formalism_L2_Col_GSD_twSgn___redArg(v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___redArg___lam__0(lean_object* v_toZero_233_, lean_object* v_toIntCast_234_, lean_object* v_d_235_){
_start:
{
if (lean_obj_tag(v_d_235_) == 0)
{
lean_dec(v_toIntCast_234_);
lean_inc(v_toZero_233_);
return v_toZero_233_;
}
else
{
lean_object* v_val_236_; lean_object* v_val_237_; lean_object* v___x_238_; 
v_val_236_ = lean_ctor_get(v_d_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v_d_235_, 1);
v_val_237_ = lean_ctor_get(v_val_236_, 0);
lean_inc(v_val_237_);
lean_dec(v_val_236_);
v___x_238_ = lean_apply_1(v_toIntCast_234_, v_val_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___redArg___lam__0___boxed(lean_object* v_toZero_239_, lean_object* v_toIntCast_240_, lean_object* v_d_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_tree_Formalism_L2_Col_GSD_twForm___redArg___lam__0(v_toZero_239_, v_toIntCast_240_, v_d_241_);
lean_dec(v_toZero_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___redArg(lean_object* v_inst_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_toSemiring_246_; lean_object* v___x_247_; lean_object* v_toZero_248_; lean_object* v___x_249_; lean_object* v_toRing_250_; lean_object* v___x_251_; lean_object* v_toIntCast_252_; lean_object* v___f_253_; 
v___x_244_ = lp_mathlib_Field_toSemifield___redArg(v_inst_243_);
v___x_245_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_244_);
v_toSemiring_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_toSemiring_246_);
lean_dec_ref(v___x_245_);
v___x_247_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_246_);
v_toZero_248_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_toZero_248_);
lean_dec_ref(v___x_247_);
v___x_249_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_243_);
v_toRing_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_toRing_250_);
lean_dec_ref(v___x_249_);
v___x_251_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_250_);
v_toIntCast_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_toIntCast_252_);
lean_dec_ref(v___x_251_);
v___f_253_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_GSD_twForm___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_253_, 0, v_toZero_248_);
lean_closure_set(v___f_253_, 1, v_toIntCast_252_);
return v___f_253_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm(lean_object* v_K_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lp_tree_Formalism_L2_Col_GSD_twForm___redArg(v_inst_255_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_GSD_twForm___boxed(lean_object* v_K_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = lp_tree_Formalism_L2_Col_GSD_twForm(v_K_259_, v_inst_260_, v_inst_261_, v_inst_262_);
lean_dec(v_inst_262_);
return v_res_263_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(uint8_t builtin);
lean_object* initialize_tree_Formalism_ThetaLiftIndependence_Statement(uint8_t builtin);
lean_object* initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_ThetaLiftIndependence_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
