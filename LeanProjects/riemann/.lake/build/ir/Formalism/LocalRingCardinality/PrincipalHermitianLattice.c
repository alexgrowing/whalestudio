// Lean compiler output
// Module: Formalism.LocalRingCardinality.PrincipalHermitianLattice
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
lean_object* lp_mathlib_LinearMap_id___lam__0___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearEquiv_symm___redArg(lean_object*);
static const lean_closure_object lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_LinearMap_id___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_V0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_V0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_Usp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_Usp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_sharp(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_sharp___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_dualLat___at___00Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_dualLat___at___00Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_cc0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_cc0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg(lean_object* v_S_2_, lean_object* v_00_u03bc_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_zero_5_; uint8_t v_isZero_6_; 
v_zero_5_ = lean_unsigned_to_nat(0u);
v_isZero_6_ = lean_nat_dec_eq(v_x_4_, v_zero_5_);
if (v_isZero_6_ == 1)
{
lean_object* v___f_7_; 
lean_dec(v_00_u03bc_3_);
lean_dec_ref(v_S_2_);
v___f_7_ = ((lean_object*)(lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg___closed__0));
return v___f_7_;
}
else
{
lean_object* v_io_8_; lean_object* v_one_9_; lean_object* v_n_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___f_13_; 
v_io_8_ = lean_ctor_get(v_S_2_, 6);
lean_inc(v_io_8_);
v_one_9_ = lean_unsigned_to_nat(1u);
v_n_10_ = lean_nat_sub(v_x_4_, v_one_9_);
lean_inc(v_00_u03bc_3_);
v___x_11_ = lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg(v_S_2_, v_00_u03bc_3_, v_n_10_);
v___x_12_ = lean_apply_2(v_io_8_, v_00_u03bc_3_, v_n_10_);
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v___x_12_);
lean_closure_set(v___f_13_, 1, v___x_11_);
return v___f_13_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg___boxed(lean_object* v_S_14_, lean_object* v_00_u03bc_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg(v_S_14_, v_00_u03bc_15_, v_x_16_);
lean_dec(v_x_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo(lean_object* v_D_18_, lean_object* v_EE_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_S_23_, lean_object* v_00_u03bc_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg(v_S_23_, v_00_u03bc_24_, v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_downTo___boxed(lean_object* v_D_27_, lean_object* v_EE_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_S_32_, lean_object* v_00_u03bc_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Formalism_BasicNotions_RowSide_downTo(v_D_27_, v_EE_28_, v_inst_29_, v_inst_30_, v_inst_31_, v_S_32_, v_00_u03bc_33_, v_x_34_);
lean_dec(v_x_34_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
lean_dec_ref(v_D_27_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota___redArg(lean_object* v_D_36_, lean_object* v_S_37_, lean_object* v_00_u03bc_38_){
_start:
{
lean_object* v_multZero_39_; lean_object* v_multTop_40_; lean_object* v___x_41_; lean_object* v_R_42_; lean_object* v_toLinearMap_43_; lean_object* v_m_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v_toLinearMap_48_; lean_object* v___f_49_; lean_object* v___f_50_; 
v_multZero_39_ = lean_ctor_get(v_S_37_, 4);
v_multTop_40_ = lean_ctor_get(v_S_37_, 5);
lean_inc_ref(v_multTop_40_);
lean_inc_ref(v_multZero_39_);
lean_inc_n(v_00_u03bc_38_, 2);
v___x_41_ = lean_apply_1(v_multZero_39_, v_00_u03bc_38_);
v_R_42_ = lean_ctor_get(v_D_36_, 0);
v_toLinearMap_43_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_toLinearMap_43_);
lean_dec_ref(v___x_41_);
v_m_44_ = lean_ctor_get(v_R_42_, 2);
v___x_45_ = lp_tree_Formalism_BasicNotions_RowSide_downTo___redArg(v_S_37_, v_00_u03bc_38_, v_m_44_);
v___x_46_ = lean_apply_1(v_multTop_40_, v_00_u03bc_38_);
v___x_47_ = lp_mathlib_LinearEquiv_symm___redArg(v___x_46_);
v_toLinearMap_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_toLinearMap_48_);
lean_dec_ref(v___x_47_);
v___f_49_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_49_, 0, v_toLinearMap_48_);
lean_closure_set(v___f_49_, 1, v___x_45_);
v___f_50_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_50_, 0, v___f_49_);
lean_closure_set(v___f_50_, 1, v_toLinearMap_43_);
return v___f_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota___redArg___boxed(lean_object* v_D_51_, lean_object* v_S_52_, lean_object* v_00_u03bc_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_BasicNotions_RowSide_iota___redArg(v_D_51_, v_S_52_, v_00_u03bc_53_);
lean_dec_ref(v_D_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota(lean_object* v_D_55_, lean_object* v_EE_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_S_60_, lean_object* v_00_u03bc_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lp_tree_Formalism_BasicNotions_RowSide_iota___redArg(v_D_55_, v_S_60_, v_00_u03bc_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_iota___boxed(lean_object* v_D_63_, lean_object* v_EE_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_S_68_, lean_object* v_00_u03bc_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_BasicNotions_RowSide_iota(v_D_63_, v_EE_64_, v_inst_65_, v_inst_66_, v_inst_67_, v_S_68_, v_00_u03bc_69_);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
lean_dec_ref(v_D_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_V0(lean_object* v_D_71_, lean_object* v_EE_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_S_76_, lean_object* v_00_u03bc_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_V0___boxed(lean_object* v_D_79_, lean_object* v_EE_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_S_84_, lean_object* v_00_u03bc_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_tree_Formalism_BasicNotions_RowSide_V0(v_D_79_, v_EE_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_S_84_, v_00_u03bc_85_);
lean_dec(v_00_u03bc_85_);
lean_dec_ref(v_S_84_);
lean_dec_ref(v_inst_82_);
lean_dec_ref(v_inst_81_);
lean_dec_ref(v_D_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_Usp(lean_object* v_D_87_, lean_object* v_EE_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_S_92_, lean_object* v_00_u03bc_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_Usp___boxed(lean_object* v_D_95_, lean_object* v_EE_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_S_100_, lean_object* v_00_u03bc_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_tree_Formalism_BasicNotions_RowSide_Usp(v_D_95_, v_EE_96_, v_inst_97_, v_inst_98_, v_inst_99_, v_S_100_, v_00_u03bc_101_);
lean_dec(v_00_u03bc_101_);
lean_dec_ref(v_S_100_);
lean_dec_ref(v_inst_98_);
lean_dec_ref(v_inst_97_);
lean_dec_ref(v_D_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc(lean_object* v_D_103_, lean_object* v_EE_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_S_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___boxed(lean_object* v_D_110_, lean_object* v_EE_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_S_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_tree_Formalism_BasicNotions_RowSide_cc(v_D_110_, v_EE_111_, v_inst_112_, v_inst_113_, v_inst_114_, v_S_115_);
lean_dec_ref(v_S_115_);
lean_dec_ref(v_inst_113_);
lean_dec_ref(v_inst_112_);
lean_dec_ref(v_D_110_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_sharp(lean_object* v_D_117_){
_start:
{
lean_object* v_what_u2082_118_; lean_object* v_ntypes_119_; lean_object* v_div_120_; lean_object* v_jEE_121_; lean_object* v_instAmb_122_; lean_object* v_instAmbi_123_; lean_object* v_instMult_124_; lean_object* v_instMulti_125_; lean_object* v_multZero_126_; lean_object* v_multTop_127_; lean_object* v_io_128_; lean_object* v_Mtilde_129_; lean_object* v_eOp_130_; lean_object* v_cenAmb_131_; lean_object* v_RR_132_; lean_object* v___x_133_; 
v_what_u2082_118_ = lean_ctor_get(v_D_117_, 4);
v_ntypes_119_ = lean_ctor_get(v_D_117_, 46);
v_div_120_ = lean_ctor_get(v_D_117_, 12);
v_jEE_121_ = lean_ctor_get(v_D_117_, 25);
v_instAmb_122_ = lean_ctor_get(v_what_u2082_118_, 26);
v_instAmbi_123_ = lean_ctor_get(v_what_u2082_118_, 27);
v_instMult_124_ = lean_ctor_get(v_what_u2082_118_, 28);
v_instMulti_125_ = lean_ctor_get(v_what_u2082_118_, 29);
v_multZero_126_ = lean_ctor_get(v_what_u2082_118_, 30);
v_multTop_127_ = lean_ctor_get(v_what_u2082_118_, 31);
v_io_128_ = lean_ctor_get(v_what_u2082_118_, 32);
v_Mtilde_129_ = lean_ctor_get(v_what_u2082_118_, 33);
v_eOp_130_ = lean_ctor_get(v_what_u2082_118_, 34);
v_cenAmb_131_ = lean_ctor_get(v_ntypes_119_, 8);
v_RR_132_ = lean_ctor_get(v_div_120_, 0);
lean_inc(v_jEE_121_);
lean_inc_ref(v_RR_132_);
lean_inc(v_eOp_130_);
lean_inc(v_cenAmb_131_);
lean_inc(v_Mtilde_129_);
lean_inc(v_io_128_);
lean_inc_ref(v_multTop_127_);
lean_inc_ref(v_multZero_126_);
lean_inc_ref(v_instMulti_125_);
lean_inc_ref(v_instMult_124_);
lean_inc_ref(v_instAmbi_123_);
lean_inc_ref(v_instAmb_122_);
v___x_133_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_133_, 0, v_instAmb_122_);
lean_ctor_set(v___x_133_, 1, v_instAmbi_123_);
lean_ctor_set(v___x_133_, 2, v_instMult_124_);
lean_ctor_set(v___x_133_, 3, v_instMulti_125_);
lean_ctor_set(v___x_133_, 4, v_multZero_126_);
lean_ctor_set(v___x_133_, 5, v_multTop_127_);
lean_ctor_set(v___x_133_, 6, v_io_128_);
lean_ctor_set(v___x_133_, 7, v_Mtilde_129_);
lean_ctor_set(v___x_133_, 8, v_cenAmb_131_);
lean_ctor_set(v___x_133_, 9, v_eOp_130_);
lean_ctor_set(v___x_133_, 10, v_RR_132_);
lean_ctor_set(v___x_133_, 11, v_jEE_121_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_sharp___boxed(lean_object* v_D_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_tree_Formalism_BasicNotions_RowSide_sharp(v_D_134_);
lean_dec_ref(v_D_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___redArg(lean_object* v_X_136_){
_start:
{
lean_object* v_RR_137_; 
v_RR_137_ = lean_ctor_get(v_X_136_, 10);
lean_inc_ref(v_RR_137_);
return v_RR_137_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___redArg___boxed(lean_object* v_X_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___redArg(v_X_138_);
lean_dec_ref(v_X_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice(lean_object* v_D_140_, lean_object* v_X_141_){
_start:
{
lean_object* v_RR_142_; 
v_RR_142_ = lean_ctor_get(v_X_141_, 10);
lean_inc_ref(v_RR_142_);
return v_RR_142_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice___boxed(lean_object* v_D_143_, lean_object* v_X_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = lp_tree_Formalism_BasicNotions_BaseLevelRowSide_principalHermitianLattice(v_D_143_, v_X_144_);
lean_dec_ref(v_X_144_);
lean_dec_ref(v_D_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_dualLat___at___00Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0_spec__1(lean_object* v___x_146_, lean_object* v_A_147_, lean_object* v_A_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_dualLat___at___00Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0_spec__1___boxed(lean_object* v___x_150_, lean_object* v_A_151_, lean_object* v_A_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_tree_Formalism_HN_dualLat___at___00Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0_spec__1(v___x_150_, v_A_151_, v_A_152_);
lean_dec_ref(v_A_151_);
lean_dec_ref(v___x_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___redArg(lean_object* v___x_154_, lean_object* v_A_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___redArg___boxed(lean_object* v___x_157_, lean_object* v_A_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___redArg(v___x_157_, v_A_158_);
lean_dec_ref(v_A_158_);
lean_dec_ref(v___x_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___redArg(lean_object* v_D_160_, lean_object* v_S_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_box(0);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___redArg___boxed(lean_object* v_D_163_, lean_object* v_S_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___redArg(v_D_163_, v_S_164_);
lean_dec_ref(v_S_164_);
lean_dec_ref(v_D_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_cc0(lean_object* v_D_166_, lean_object* v_X_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_BaseLevelRowSide_cc0___boxed(lean_object* v_D_169_, lean_object* v_X_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = lp_tree_Formalism_BasicNotions_BaseLevelRowSide_cc0(v_D_169_, v_X_170_);
lean_dec_ref(v_X_170_);
lean_dec_ref(v_D_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0(lean_object* v___x_172_, lean_object* v_D_173_, lean_object* v_inst_174_, lean_object* v_S_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0___boxed(lean_object* v___x_177_, lean_object* v_D_178_, lean_object* v_inst_179_, lean_object* v_S_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = lp_tree_Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0(v___x_177_, v_D_178_, v_inst_179_, v_S_180_);
lean_dec_ref(v_S_180_);
lean_dec_ref(v_D_178_);
lean_dec_ref(v___x_177_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0(lean_object* v___x_182_, lean_object* v_D_183_, lean_object* v_inst_184_, lean_object* v_A_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0___boxed(lean_object* v___x_187_, lean_object* v_D_188_, lean_object* v_inst_189_, lean_object* v_A_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_tree_Formalism_BasicNotions_HLat_dualL___at___00Formalism_BasicNotions_RowSide_cc___at___00Formalism_BasicNotions_BaseLevelRowSide_cc0_spec__0_spec__0(v___x_187_, v_D_188_, v_inst_189_, v_A_190_);
lean_dec_ref(v_A_190_);
lean_dec_ref(v_D_188_);
lean_dec_ref(v___x_187_);
return v_res_191_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_PrincipalHermitianLattice(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalRingCardinality_RhoDetPrimeEqMuTildeMulChiPow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
