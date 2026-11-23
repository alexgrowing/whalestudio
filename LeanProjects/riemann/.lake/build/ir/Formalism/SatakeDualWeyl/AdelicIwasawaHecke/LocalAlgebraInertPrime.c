// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LocalAlgebraInertPrime
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementG public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
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
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_UG_bc___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_RingEquiv_instEquivLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__0(lean_object* v_val_1_, lean_object* v___y_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_val_1_, v_j_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__1(lean_object* v_inv_5_, lean_object* v_j_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_2(v_inv_5_, v_j_6_, v_j_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__2(lean_object* v_inv_9_, lean_object* v___x_10_, lean_object* v_toMul_11_, lean_object* v_toAddCommMonoid_12_, lean_object* v___f_13_, lean_object* v_j_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; 
v___f_15_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__1), 3, 2);
lean_closure_set(v___f_15_, 0, v_inv_9_);
lean_closure_set(v___f_15_, 1, v_j_14_);
v___x_16_ = lp_mathlib_dotProduct___redArg(v___x_10_, v_toMul_11_, v_toAddCommMonoid_12_, v___f_15_, v___f_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__2___boxed(lean_object* v_inv_17_, lean_object* v___x_18_, lean_object* v_toMul_19_, lean_object* v_toAddCommMonoid_20_, lean_object* v___f_21_, lean_object* v_j_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__2(v_inv_17_, v___x_18_, v_toMul_19_, v_toAddCommMonoid_20_, v___f_21_, v_j_22_);
lean_dec_ref(v_toAddCommMonoid_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__3(lean_object* v_inv_24_, lean_object* v___y_25_, lean_object* v_j_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_2(v_inv_24_, v___y_25_, v_j_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__4(lean_object* v_val_28_, lean_object* v_inv_29_, lean_object* v___x_30_, lean_object* v_toMul_31_, lean_object* v_toAddCommMonoid_32_, lean_object* v_inv_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v___f_36_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__0), 3, 2);
lean_closure_set(v___f_36_, 0, v_val_28_);
lean_closure_set(v___f_36_, 1, v___y_35_);
lean_inc_ref(v_toAddCommMonoid_32_);
lean_inc(v_toMul_31_);
lean_inc(v___x_30_);
v___f_37_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_37_, 0, v_inv_29_);
lean_closure_set(v___f_37_, 1, v___x_30_);
lean_closure_set(v___f_37_, 2, v_toMul_31_);
lean_closure_set(v___f_37_, 3, v_toAddCommMonoid_32_);
lean_closure_set(v___f_37_, 4, v___f_36_);
v___f_38_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__3), 3, 2);
lean_closure_set(v___f_38_, 0, v_inv_33_);
lean_closure_set(v___f_38_, 1, v___y_34_);
v___x_39_ = lp_mathlib_dotProduct___redArg(v___x_30_, v_toMul_31_, v_toAddCommMonoid_32_, v___f_38_, v___f_37_);
lean_dec_ref(v_toAddCommMonoid_32_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__7(lean_object* v_val_40_, lean_object* v_j_41_, lean_object* v_j_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_apply_2(v_val_40_, v_j_42_, v_j_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__5(lean_object* v_val_44_, lean_object* v___x_45_, lean_object* v_toMul_46_, lean_object* v_toAddCommMonoid_47_, lean_object* v___f_48_, lean_object* v_j_49_){
_start:
{
lean_object* v___f_50_; lean_object* v___x_51_; 
v___f_50_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__7), 3, 2);
lean_closure_set(v___f_50_, 0, v_val_44_);
lean_closure_set(v___f_50_, 1, v_j_49_);
v___x_51_ = lp_mathlib_dotProduct___redArg(v___x_45_, v_toMul_46_, v_toAddCommMonoid_47_, v___f_48_, v___f_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__5___boxed(lean_object* v_val_52_, lean_object* v___x_53_, lean_object* v_toMul_54_, lean_object* v_toAddCommMonoid_55_, lean_object* v___f_56_, lean_object* v_j_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__5(v_val_52_, v___x_53_, v_toMul_54_, v_toAddCommMonoid_55_, v___f_56_, v_j_57_);
lean_dec_ref(v_toAddCommMonoid_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__6(lean_object* v_val_59_, lean_object* v_inv_60_, lean_object* v_val_61_, lean_object* v___x_62_, lean_object* v_toMul_63_, lean_object* v_toAddCommMonoid_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
v___f_67_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__0), 3, 2);
lean_closure_set(v___f_67_, 0, v_val_59_);
lean_closure_set(v___f_67_, 1, v___y_66_);
v___f_68_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__3), 3, 2);
lean_closure_set(v___f_68_, 0, v_inv_60_);
lean_closure_set(v___f_68_, 1, v___y_65_);
lean_inc_ref(v_toAddCommMonoid_64_);
lean_inc(v_toMul_63_);
lean_inc(v___x_62_);
v___f_69_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_69_, 0, v_val_61_);
lean_closure_set(v___f_69_, 1, v___x_62_);
lean_closure_set(v___f_69_, 2, v_toMul_63_);
lean_closure_set(v___f_69_, 3, v_toAddCommMonoid_64_);
lean_closure_set(v___f_69_, 4, v___f_68_);
v___x_70_ = lp_mathlib_dotProduct___redArg(v___x_62_, v_toMul_63_, v_toAddCommMonoid_64_, v___f_69_, v___f_67_);
lean_dec_ref(v_toAddCommMonoid_64_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__8(lean_object* v_P_71_, lean_object* v_coe_72_, lean_object* v_e_73_, lean_object* v_toSemiring_74_, lean_object* v___x_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_val_77_; lean_object* v_inv_78_; lean_object* v___x_79_; lean_object* v___x_339__overap_80_; lean_object* v___x_81_; lean_object* v_val_82_; lean_object* v_inv_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_val_77_ = lean_ctor_get(v_P_71_, 0);
lean_inc(v_val_77_);
v_inv_78_ = lean_ctor_get(v_P_71_, 1);
lean_inc(v_inv_78_);
lean_dec_ref(v_P_71_);
v___x_79_ = lean_apply_1(v_coe_72_, v_e_73_);
v___x_339__overap_80_ = lp_tree_Formalism_UG_bc___redArg(v___x_79_);
v___x_81_ = lean_apply_1(v___x_339__overap_80_, v_x_76_);
v_val_82_ = lean_ctor_get(v___x_81_, 0);
v_inv_83_ = lean_ctor_get(v___x_81_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_96_ == 0)
{
v___x_85_ = v___x_81_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_inv_83_);
lean_inc(v_val_82_);
lean_dec(v___x_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v_toAddCommMonoid_88_; lean_object* v___x_89_; lean_object* v_toMul_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_94_; 
v___x_87_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_74_);
v_toAddCommMonoid_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref_n(v_toAddCommMonoid_88_, 2);
v___x_89_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_87_);
v_toMul_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_n(v_toMul_90_, 2);
lean_dec_ref(v___x_89_);
lean_inc(v_inv_78_);
lean_inc(v___x_75_);
lean_inc(v_val_77_);
v___f_91_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__4), 8, 6);
lean_closure_set(v___f_91_, 0, v_val_77_);
lean_closure_set(v___f_91_, 1, v_inv_83_);
lean_closure_set(v___f_91_, 2, v___x_75_);
lean_closure_set(v___f_91_, 3, v_toMul_90_);
lean_closure_set(v___f_91_, 4, v_toAddCommMonoid_88_);
lean_closure_set(v___f_91_, 5, v_inv_78_);
v___f_92_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__6), 8, 6);
lean_closure_set(v___f_92_, 0, v_val_77_);
lean_closure_set(v___f_92_, 1, v_inv_78_);
lean_closure_set(v___f_92_, 2, v_val_82_);
lean_closure_set(v___f_92_, 3, v___x_75_);
lean_closure_set(v___f_92_, 4, v_toMul_90_);
lean_closure_set(v___f_92_, 5, v_toAddCommMonoid_88_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v___f_91_);
lean_ctor_set(v___x_85_, 0, v___f_92_);
v___x_94_ = v___x_85_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___f_92_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___f_91_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__8___boxed(lean_object* v_P_97_, lean_object* v_coe_98_, lean_object* v_e_99_, lean_object* v_toSemiring_100_, lean_object* v___x_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__8(v_P_97_, v_coe_98_, v_e_99_, v_toSemiring_100_, v___x_101_, v_x_102_);
lean_dec_ref(v_toSemiring_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg(lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_m_106_, lean_object* v_e_107_, lean_object* v_P_108_){
_start:
{
lean_object* v_toSemiring_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_toSemiring_112_; lean_object* v___x_113_; lean_object* v_toMul_114_; lean_object* v_toAdd_115_; lean_object* v___x_116_; lean_object* v_toMul_117_; lean_object* v_toAdd_118_; lean_object* v___x_119_; lean_object* v_coe_120_; lean_object* v___x_121_; lean_object* v___f_122_; 
v_toSemiring_109_ = lean_ctor_get(v_inst_104_, 0);
lean_inc_ref(v_toSemiring_109_);
lean_dec_ref(v_inst_104_);
v___x_110_ = lp_mathlib_Field_toSemifield___redArg(v_inst_105_);
v___x_111_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_110_);
v_toSemiring_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref_n(v_toSemiring_112_, 2);
lean_dec_ref(v___x_111_);
v___x_113_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_109_);
v_toMul_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_toMul_114_);
v_toAdd_115_ = lean_ctor_get(v___x_113_, 1);
lean_inc(v_toAdd_115_);
lean_dec_ref(v___x_113_);
v___x_116_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_112_);
v_toMul_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_toMul_117_);
v_toAdd_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_toAdd_118_);
lean_dec_ref(v___x_116_);
v___x_119_ = lp_mathlib_RingEquiv_instEquivLike(lean_box(0), lean_box(0), v_toMul_114_, v_toMul_117_, v_toAdd_115_, v_toAdd_118_);
lean_dec(v_toAdd_118_);
lean_dec(v_toAdd_115_);
lean_dec(v_toMul_117_);
lean_dec(v_toMul_114_);
v_coe_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_coe_120_);
lean_dec_ref(v___x_119_);
v___x_121_ = l_List_finRange(v_m_106_);
v___f_122_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_gLoc__hom___redArg___lam__8___boxed), 6, 5);
lean_closure_set(v___f_122_, 0, v_P_108_);
lean_closure_set(v___f_122_, 1, v_coe_120_);
lean_closure_set(v___f_122_, 2, v_e_107_);
lean_closure_set(v___f_122_, 3, v_toSemiring_112_);
lean_closure_set(v___f_122_, 4, v___x_121_);
return v___f_122_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___redArg___boxed(lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_m_125_, lean_object* v_e_126_, lean_object* v_P_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_tree_Formalism_UG_P_gLoc__hom___redArg(v_inst_123_, v_inst_124_, v_m_125_, v_e_126_, v_P_127_);
lean_dec_ref(v_inst_124_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom(lean_object* v_A_129_, lean_object* v_L_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_m_133_, lean_object* v_00_u03c3A_134_, lean_object* v_00_u03c3L_135_, lean_object* v_e_136_, lean_object* v_he_137_, lean_object* v_P_138_, lean_object* v_hP_139_, lean_object* v_H_140_, lean_object* v_hH_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lp_tree_Formalism_UG_P_gLoc__hom___redArg(v_inst_131_, v_inst_132_, v_m_133_, v_e_136_, v_P_138_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_gLoc__hom___boxed(lean_object* v_A_143_, lean_object* v_L_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_m_147_, lean_object* v_00_u03c3A_148_, lean_object* v_00_u03c3L_149_, lean_object* v_e_150_, lean_object* v_he_151_, lean_object* v_P_152_, lean_object* v_hP_153_, lean_object* v_H_154_, lean_object* v_hH_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = lp_tree_Formalism_UG_P_gLoc__hom(v_A_143_, v_L_144_, v_inst_145_, v_inst_146_, v_m_147_, v_00_u03c3A_148_, v_00_u03c3L_149_, v_e_150_, v_he_151_, v_P_152_, v_hP_153_, v_H_154_, v_hH_155_);
lean_dec(v_00_u03c3L_149_);
lean_dec(v_00_u03c3A_148_);
lean_dec_ref(v_inst_146_);
return v_res_156_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementG(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
