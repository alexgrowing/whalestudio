// Lean compiler output
// Module: Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.HyperbolicPlaceProducts.Statement
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Fin_castLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_flip___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_smulRight___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(lean_object*);
lean_object* lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_Xa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_Xa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_X(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_X___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_II(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_II___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Dl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Dl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gval___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_V0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_V0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_bEta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_bEta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_bEta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z___redArg(lean_object* v_r_1_, lean_object* v_F_2_){
_start:
{
lean_object* v_e_3_; lean_object* v___x_4_; 
v_e_3_ = lean_ctor_get(v_F_2_, 0);
lean_inc(v_e_3_);
lean_dec_ref(v_F_2_);
v___x_4_ = lean_apply_1(v_e_3_, v_r_1_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z(lean_object* v_K_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_V_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_H_11_, lean_object* v_r_12_, lean_object* v_F_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z___redArg(v_r_12_, v_F_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z___boxed(lean_object* v_K_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_V_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_H_21_, lean_object* v_r_22_, lean_object* v_F_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_z(v_K_15_, v_inst_16_, v_inst_17_, v_V_18_, v_inst_19_, v_inst_20_, v_H_21_, v_r_22_, v_F_23_);
lean_dec(v_H_21_);
lean_dec(v_inst_20_);
lean_dec_ref(v_inst_19_);
lean_dec(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_Xa(lean_object* v_K_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_V_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_H_31_, lean_object* v_r_32_, lean_object* v_F_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_Xa___boxed(lean_object* v_K_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_V_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_H_42_, lean_object* v_r_43_, lean_object* v_F_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_Xa(v_K_36_, v_inst_37_, v_inst_38_, v_V_39_, v_inst_40_, v_inst_41_, v_H_42_, v_r_43_, v_F_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_F_44_);
lean_dec(v_r_43_);
lean_dec(v_H_42_);
lean_dec(v_inst_41_);
lean_dec_ref(v_inst_40_);
lean_dec(v_inst_38_);
lean_dec_ref(v_inst_37_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_X(lean_object* v_K_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_V_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_H_53_, lean_object* v_r_54_, lean_object* v_F_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_X___boxed(lean_object* v_K_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_V_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_H_63_, lean_object* v_r_64_, lean_object* v_F_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_HermitianLatticeCounting_S6_FlagD_X(v_K_57_, v_inst_58_, v_inst_59_, v_V_60_, v_inst_61_, v_inst_62_, v_H_63_, v_r_64_, v_F_65_);
lean_dec_ref(v_F_65_);
lean_dec(v_r_64_);
lean_dec(v_H_63_);
lean_dec(v_inst_62_);
lean_dec_ref(v_inst_61_);
lean_dec(v_inst_59_);
lean_dec_ref(v_inst_58_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_II(lean_object* v_K_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_V_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_H_73_, lean_object* v_r_74_, lean_object* v_F_75_, lean_object* v_F_x27_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_II___boxed(lean_object* v_K_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_V_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_H_84_, lean_object* v_r_85_, lean_object* v_F_86_, lean_object* v_F_x27_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_tree_Formalism_HermitianLatticeCounting_S6_II(v_K_78_, v_inst_79_, v_inst_80_, v_V_81_, v_inst_82_, v_inst_83_, v_H_84_, v_r_85_, v_F_86_, v_F_x27_87_);
lean_dec_ref(v_F_x27_87_);
lean_dec_ref(v_F_86_);
lean_dec(v_r_85_);
lean_dec(v_H_84_);
lean_dec(v_inst_83_);
lean_dec_ref(v_inst_82_);
lean_dec(v_inst_80_);
lean_dec_ref(v_inst_79_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___lam__0(lean_object* v_F_89_, lean_object* v_F_x27_90_, lean_object* v_H_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v_e_94_; lean_object* v_e_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_e_94_ = lean_ctor_get(v_F_89_, 0);
lean_inc(v_e_94_);
lean_dec_ref(v_F_89_);
v_e_95_ = lean_ctor_get(v_F_x27_90_, 0);
lean_inc(v_e_95_);
lean_dec_ref(v_F_x27_90_);
v___x_96_ = lean_apply_1(v_e_94_, v_a_92_);
v___x_97_ = lean_apply_1(v_e_95_, v_b_93_);
v___x_98_ = lean_apply_2(v_H_91_, v___x_96_, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg(lean_object* v_H_100_, lean_object* v_F_101_, lean_object* v_F_x27_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; lean_object* v_toFun_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___closed__0, &lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___closed__0_once, _init_lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___closed__0);
v_toFun_106_ = lean_ctor_get(v___x_105_, 0);
v___f_107_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg___lam__0), 5, 3);
lean_closure_set(v___f_107_, 0, v_F_101_);
lean_closure_set(v___f_107_, 1, v_F_x27_102_);
lean_closure_set(v___f_107_, 2, v_H_100_);
lean_inc(v_toFun_106_);
v___x_108_ = lean_apply_3(v_toFun_106_, v___f_107_, v_a_103_, v_a_104_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat(lean_object* v_K_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_V_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_H_115_, lean_object* v_r_116_, lean_object* v_F_117_, lean_object* v_F_x27_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___redArg(v_H_115_, v_F_117_, v_F_x27_118_, v_a_119_, v_a_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___boxed(lean_object* v_K_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_V_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_H_128_, lean_object* v_r_129_, lean_object* v_F_130_, lean_object* v_F_x27_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat(v_K_122_, v_inst_123_, v_inst_124_, v_V_125_, v_inst_126_, v_inst_127_, v_H_128_, v_r_129_, v_F_130_, v_F_x27_131_, v_a_132_, v_a_133_);
lean_dec(v_r_129_);
lean_dec(v_inst_127_);
lean_dec_ref(v_inst_126_);
lean_dec(v_inst_124_);
lean_dec_ref(v_inst_123_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Dl___redArg(lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_H_139_, lean_object* v_r_140_, lean_object* v_F_141_, lean_object* v_F_x27_142_, lean_object* v_l_143_){
_start:
{
lean_object* v_toCommRing_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_30__overap_152_; lean_object* v___x_153_; 
v_toCommRing_144_ = lean_ctor_get(v_inst_135_, 0);
lean_inc_ref(v_toCommRing_144_);
lean_inc_n(v_l_143_, 2);
v___x_145_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_145_, 0, v_l_143_);
v___x_146_ = l_List_finRange(v_l_143_);
lean_inc(v_r_140_);
v___x_147_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_Zhat___boxed), 12, 10);
lean_closure_set(v___x_147_, 0, lean_box(0));
lean_closure_set(v___x_147_, 1, v_inst_135_);
lean_closure_set(v___x_147_, 2, v_inst_136_);
lean_closure_set(v___x_147_, 3, lean_box(0));
lean_closure_set(v___x_147_, 4, v_inst_137_);
lean_closure_set(v___x_147_, 5, v_inst_138_);
lean_closure_set(v___x_147_, 6, v_H_139_);
lean_closure_set(v___x_147_, 7, v_r_140_);
lean_closure_set(v___x_147_, 8, v_F_141_);
lean_closure_set(v___x_147_, 9, v_F_x27_142_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_r_140_, v___x_148_);
lean_dec(v_r_140_);
v___x_150_ = lean_alloc_closure((void*)(l_Fin_castLE___boxed), 4, 3);
lean_closure_set(v___x_150_, 0, v_l_143_);
lean_closure_set(v___x_150_, 1, v___x_149_);
lean_closure_set(v___x_150_, 2, lean_box(0));
lean_inc_ref(v___x_150_);
v___x_151_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_151_, 0, lean_box(0));
lean_closure_set(v___x_151_, 1, lean_box(0));
lean_closure_set(v___x_151_, 2, lean_box(0));
lean_closure_set(v___x_151_, 3, lean_box(0));
lean_closure_set(v___x_151_, 4, lean_box(0));
lean_closure_set(v___x_151_, 5, v___x_147_);
lean_closure_set(v___x_151_, 6, v___x_150_);
lean_closure_set(v___x_151_, 7, v___x_150_);
v___x_30__overap_152_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___x_145_, v___x_146_, v_toCommRing_144_);
v___x_153_ = lean_apply_1(v___x_30__overap_152_, v___x_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Dl(lean_object* v_K_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_V_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_H_160_, lean_object* v_r_161_, lean_object* v_F_162_, lean_object* v_F_x27_163_, lean_object* v_l_164_, lean_object* v_hl_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Dl___redArg(v_inst_155_, v_inst_156_, v_inst_158_, v_inst_159_, v_H_160_, v_r_161_, v_F_162_, v_F_x27_163_, v_l_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gval___redArg(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_H_171_, lean_object* v_r_172_, lean_object* v_F_173_, lean_object* v_F_x27_174_){
_start:
{
lean_object* v___x_175_; lean_object* v_toRing_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_toSub_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_toSemiring_182_; lean_object* v___x_183_; lean_object* v_toMul_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v_T_188_; lean_object* v_T_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_inc_ref_n(v_inst_167_, 2);
v___x_175_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_167_);
v_toRing_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref(v_toRing_176_);
lean_dec_ref(v___x_175_);
v___x_177_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_176_);
v___x_178_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_177_);
lean_dec_ref(v___x_177_);
v_toSub_179_ = lean_ctor_get(v___x_178_, 2);
lean_inc(v_toSub_179_);
lean_dec_ref(v___x_178_);
v___x_180_ = lp_mathlib_Field_toSemifield___redArg(v_inst_167_);
v___x_181_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_180_);
v_toSemiring_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc_ref(v_toSemiring_182_);
lean_dec_ref(v___x_181_);
v___x_183_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_182_);
v_toMul_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc_n(v_toMul_184_, 4);
lean_dec_ref(v___x_183_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_r_172_, v___x_185_);
lean_inc_ref(v_F_x27_174_);
lean_inc_ref(v_F_173_);
lean_inc_n(v_r_172_, 2);
lean_inc(v_H_171_);
lean_inc(v_inst_170_);
lean_inc_ref(v_inst_169_);
lean_inc_n(v_inst_168_, 3);
v___x_187_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Dl___redArg(v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_H_171_, v_r_172_, v_F_173_, v_F_x27_174_, v___x_186_);
v_T_188_ = lean_ctor_get(v_F_173_, 1);
v_T_189_ = lean_ctor_get(v_F_x27_174_, 1);
lean_inc(v___x_187_);
v___x_190_ = lean_apply_1(v_inst_168_, v___x_187_);
v___x_191_ = lean_apply_2(v_toMul_184_, v___x_187_, v___x_190_);
lean_inc(v_T_189_);
lean_inc(v_T_188_);
v___x_192_ = lean_apply_2(v_toMul_184_, v_T_188_, v_T_189_);
v___x_193_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Dl___redArg(v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_H_171_, v_r_172_, v_F_173_, v_F_x27_174_, v_r_172_);
lean_inc(v___x_193_);
v___x_194_ = lean_apply_1(v_inst_168_, v___x_193_);
v___x_195_ = lean_apply_2(v_toMul_184_, v___x_193_, v___x_194_);
v___x_196_ = lean_apply_2(v_toMul_184_, v___x_192_, v___x_195_);
v___x_197_ = lean_apply_2(v_toSub_179_, v___x_191_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gval(lean_object* v_K_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_V_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_H_204_, lean_object* v_r_205_, lean_object* v_F_206_, lean_object* v_F_x27_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Gval___redArg(v_inst_199_, v_inst_200_, v_inst_202_, v_inst_203_, v_H_204_, v_r_205_, v_F_206_, v_F_x27_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___lam__0(lean_object* v_F_209_, lean_object* v_F_x27_210_, lean_object* v_H_211_, lean_object* v_p_212_, lean_object* v_q_213_){
_start:
{
lean_object* v_e_214_; lean_object* v_e_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_e_214_ = lean_ctor_get(v_F_209_, 0);
lean_inc_n(v_e_214_, 2);
lean_dec_ref(v_F_209_);
v_e_215_ = lean_ctor_get(v_F_x27_210_, 0);
lean_inc_n(v_e_215_, 2);
lean_dec_ref(v_F_x27_210_);
v___x_216_ = l_Sum_elim___redArg(v_e_214_, v_e_215_, v_p_212_);
v___x_217_ = l_Sum_elim___redArg(v_e_214_, v_e_215_, v_q_213_);
v___x_218_ = lean_apply_2(v_H_211_, v___x_216_, v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___closed__0(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_219_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg(lean_object* v_H_220_, lean_object* v_F_221_, lean_object* v_F_x27_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; lean_object* v_toFun_226_; lean_object* v___f_227_; lean_object* v___x_228_; 
v___x_225_ = lean_obj_once(&lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___closed__0, &lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___closed__0_once, _init_lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___closed__0);
v_toFun_226_ = lean_ctor_get(v___x_225_, 0);
v___f_227_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg___lam__0), 5, 3);
lean_closure_set(v___f_227_, 0, v_F_221_);
lean_closure_set(v___f_227_, 1, v_F_x27_222_);
lean_closure_set(v___f_227_, 2, v_H_220_);
lean_inc(v_toFun_226_);
v___x_228_ = lean_apply_3(v_toFun_226_, v___f_227_, v_a_223_, v_a_224_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram(lean_object* v_K_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_V_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_H_235_, lean_object* v_r_236_, lean_object* v_F_237_, lean_object* v_F_x27_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___redArg(v_H_235_, v_F_237_, v_F_x27_238_, v_a_239_, v_a_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_Gram___boxed(lean_object* v_K_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_V_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_H_248_, lean_object* v_r_249_, lean_object* v_F_250_, lean_object* v_F_x27_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = lp_tree_Formalism_HermitianLatticeCounting_S6_Gram(v_K_242_, v_inst_243_, v_inst_244_, v_V_245_, v_inst_246_, v_inst_247_, v_H_248_, v_r_249_, v_F_250_, v_F_x27_251_, v_a_252_, v_a_253_);
lean_dec(v_r_249_);
lean_dec(v_inst_247_);
lean_dec_ref(v_inst_246_);
lean_dec(v_inst_244_);
lean_dec_ref(v_inst_243_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg___lam__0(lean_object* v___x_255_, lean_object* v_inst_256_, lean_object* v_x_257_, lean_object* v___x_258_, lean_object* v_v_259_, lean_object* v_toSub_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_inc(v___y_261_);
lean_inc(v_inst_256_);
v___x_262_ = lp_mathlib_LinearMap_smulRight___redArg___lam__0(v___x_255_, v_inst_256_, v_x_257_, v___y_261_);
v___x_263_ = lp_mathlib_LinearMap_smulRight___redArg___lam__0(v___x_258_, v_inst_256_, v_v_259_, v___y_261_);
v___x_264_ = lean_apply_2(v_toSub_260_, v___x_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_H_267_, lean_object* v_x_268_, lean_object* v_v_269_){
_start:
{
lean_object* v_toSub_270_; lean_object* v___x_42__overap_271_; lean_object* v___x_272_; lean_object* v___x_45__overap_273_; lean_object* v___x_274_; lean_object* v___f_275_; 
v_toSub_270_ = lean_ctor_get(v_inst_265_, 2);
lean_inc(v_toSub_270_);
lean_dec_ref(v_inst_265_);
lean_inc(v_H_267_);
v___x_42__overap_271_ = lp_mathlib_LinearMap_flip___redArg(v_H_267_);
lean_inc(v_v_269_);
v___x_272_ = lean_apply_1(v___x_42__overap_271_, v_v_269_);
v___x_45__overap_273_ = lp_mathlib_LinearMap_flip___redArg(v_H_267_);
lean_inc(v_x_268_);
v___x_274_ = lean_apply_1(v___x_45__overap_273_, v_x_268_);
v___f_275_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg___lam__0), 7, 6);
lean_closure_set(v___f_275_, 0, v___x_272_);
lean_closure_set(v___f_275_, 1, v_inst_266_);
lean_closure_set(v___f_275_, 2, v_x_268_);
lean_closure_set(v___f_275_, 3, v___x_274_);
lean_closure_set(v___f_275_, 4, v_v_269_);
lean_closure_set(v___f_275_, 5, v_toSub_270_);
return v___f_275_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv(lean_object* v_K_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_V_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_H_282_, lean_object* v_x_283_, lean_object* v_v_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg(v_inst_280_, v_inst_281_, v_H_282_, v_x_283_, v_v_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_xv___boxed(lean_object* v_K_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_V_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_H_292_, lean_object* v_x_293_, lean_object* v_v_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = lp_tree_Formalism_HermitianLatticeCounting_S6_xv(v_K_286_, v_inst_287_, v_inst_288_, v_V_289_, v_inst_290_, v_inst_291_, v_H_292_, v_x_293_, v_v_294_);
lean_dec(v_inst_288_);
lean_dec_ref(v_inst_287_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_V0(lean_object* v_K_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_V_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_H_302_, lean_object* v_r_303_, lean_object* v_F_304_, lean_object* v_F_x27_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_box(0);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_V0___boxed(lean_object* v_K_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_V_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_H_313_, lean_object* v_r_314_, lean_object* v_F_315_, lean_object* v_F_x27_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = lp_tree_Formalism_HermitianLatticeCounting_S6_V0(v_K_307_, v_inst_308_, v_inst_309_, v_V_310_, v_inst_311_, v_inst_312_, v_H_313_, v_r_314_, v_F_315_, v_F_x27_316_);
lean_dec_ref(v_F_x27_316_);
lean_dec_ref(v_F_315_);
lean_dec(v_r_314_);
lean_dec(v_H_313_);
lean_dec(v_inst_312_);
lean_dec_ref(v_inst_311_);
lean_dec(v_inst_309_);
lean_dec_ref(v_inst_308_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich___redArg___lam__0(lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_H_320_, lean_object* v_x_321_, lean_object* v_v_322_, lean_object* v_toAddSemigroup_323_, lean_object* v___x_324_, lean_object* v_c_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_365__overap_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc(v_x_321_);
lean_inc_n(v_inst_319_, 2);
v___x_365__overap_327_ = lp_tree_Formalism_HermitianLatticeCounting_S6_xv___redArg(v_inst_318_, v_inst_319_, v_H_320_, v_x_321_, v_v_322_);
lean_inc_n(v___y_326_, 2);
v___x_328_ = lean_apply_1(v___x_365__overap_327_, v___y_326_);
lean_inc(v_toAddSemigroup_323_);
v___x_329_ = lean_apply_2(v_toAddSemigroup_323_, v___y_326_, v___x_328_);
v___x_330_ = lp_mathlib_LinearMap_smulRight___redArg___lam__0(v___x_324_, v_inst_319_, v_x_321_, v___y_326_);
v___x_331_ = lean_apply_2(v_inst_319_, v_c_325_, v___x_330_);
v___x_332_ = lean_apply_2(v_toAddSemigroup_323_, v___x_329_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich___redArg(lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_H_335_, lean_object* v_x_336_, lean_object* v_v_337_, lean_object* v_c_338_){
_start:
{
lean_object* v_toAddMonoid_339_; lean_object* v_toAddSemigroup_340_; lean_object* v___x_99__overap_341_; lean_object* v___x_342_; lean_object* v___f_343_; 
v_toAddMonoid_339_ = lean_ctor_get(v_inst_333_, 0);
v_toAddSemigroup_340_ = lean_ctor_get(v_toAddMonoid_339_, 0);
lean_inc(v_toAddSemigroup_340_);
lean_inc(v_H_335_);
v___x_99__overap_341_ = lp_mathlib_LinearMap_flip___redArg(v_H_335_);
lean_inc(v_x_336_);
v___x_342_ = lean_apply_1(v___x_99__overap_341_, v_x_336_);
v___f_343_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_eich___redArg___lam__0), 9, 8);
lean_closure_set(v___f_343_, 0, v_inst_333_);
lean_closure_set(v___f_343_, 1, v_inst_334_);
lean_closure_set(v___f_343_, 2, v_H_335_);
lean_closure_set(v___f_343_, 3, v_x_336_);
lean_closure_set(v___f_343_, 4, v_v_337_);
lean_closure_set(v___f_343_, 5, v_toAddSemigroup_340_);
lean_closure_set(v___f_343_, 6, v___x_342_);
lean_closure_set(v___f_343_, 7, v_c_338_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich(lean_object* v_K_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_V_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_H_350_, lean_object* v_x_351_, lean_object* v_v_352_, lean_object* v_c_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lp_tree_Formalism_HermitianLatticeCounting_S6_eich___redArg(v_inst_348_, v_inst_349_, v_H_350_, v_x_351_, v_v_352_, v_c_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_eich___boxed(lean_object* v_K_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_V_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_H_361_, lean_object* v_x_362_, lean_object* v_v_363_, lean_object* v_c_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = lp_tree_Formalism_HermitianLatticeCounting_S6_eich(v_K_355_, v_inst_356_, v_inst_357_, v_V_358_, v_inst_359_, v_inst_360_, v_H_361_, v_x_362_, v_v_363_, v_c_364_);
lean_dec(v_inst_357_);
lean_dec_ref(v_inst_356_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_bEta___redArg(lean_object* v_inst_366_, lean_object* v_h_367_, lean_object* v_00_u03b7_368_, lean_object* v_x_x27_369_, lean_object* v_x_x27_x27_370_){
_start:
{
lean_object* v_toSub_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_toSub_371_ = lean_ctor_get(v_inst_366_, 2);
lean_inc(v_toSub_371_);
lean_dec_ref(v_inst_366_);
lean_inc(v_x_x27_x27_370_);
v___x_372_ = lean_apply_1(v_00_u03b7_368_, v_x_x27_x27_370_);
v___x_373_ = lean_apply_2(v_toSub_371_, v_x_x27_x27_370_, v___x_372_);
v___x_374_ = lean_apply_2(v_h_367_, v_x_x27_369_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_bEta(lean_object* v_K_375_, lean_object* v_U_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_h_381_, lean_object* v_00_u03b7_382_, lean_object* v_x_x27_383_, lean_object* v_x_x27_x27_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lp_tree_Formalism_HermitianLatticeCounting_S6_bEta___redArg(v_inst_379_, v_h_381_, v_00_u03b7_382_, v_x_x27_383_, v_x_x27_x27_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_bEta___boxed(lean_object* v_K_386_, lean_object* v_U_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_h_392_, lean_object* v_00_u03b7_393_, lean_object* v_x_x27_394_, lean_object* v_x_x27_x27_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = lp_tree_Formalism_HermitianLatticeCounting_S6_bEta(v_K_386_, v_U_387_, v_inst_388_, v_inst_389_, v_inst_390_, v_inst_391_, v_h_392_, v_00_u03b7_393_, v_x_x27_394_, v_x_x27_x27_395_);
lean_dec(v_inst_391_);
lean_dec(v_inst_389_);
lean_dec_ref(v_inst_388_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp___lam__0(lean_object* v_p_397_, lean_object* v___x_398_, lean_object* v_N_399_, lean_object* v_i_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_nat_pow(v_p_397_, v_i_400_);
v___x_402_ = lean_nat_sub(v_p_397_, v___x_398_);
v___x_403_ = lean_nat_mul(v___x_401_, v___x_402_);
lean_dec(v___x_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_nat_div(v_N_399_, v___x_403_);
lean_dec(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp___lam__0___boxed(lean_object* v_p_405_, lean_object* v___x_406_, lean_object* v_N_407_, lean_object* v_i_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp___lam__0(v_p_405_, v___x_406_, v_N_407_, v_i_408_);
lean_dec(v_i_408_);
lean_dec(v_N_407_);
lean_dec(v___x_406_);
lean_dec(v_p_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp(lean_object* v_N_410_, lean_object* v_p_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_412_ = lean_unsigned_to_nat(1u);
lean_inc(v_N_410_);
v___f_413_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp___lam__0___boxed), 4, 3);
lean_closure_set(v___f_413_, 0, v_p_411_);
lean_closure_set(v___f_413_, 1, v___x_412_);
lean_closure_set(v___f_413_, 2, v_N_410_);
v___x_414_ = lean_nat_add(v_N_410_, v___x_412_);
lean_dec(v_N_410_);
v___x_415_ = l_List_range(v___x_414_);
v___x_416_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_415_, v___f_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM___lam__0(lean_object* v_N_417_, lean_object* v_p_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc(v_p_418_);
v___x_419_ = lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiExp(v_N_417_, v_p_418_);
v___x_420_ = lean_nat_pow(v_p_418_, v___x_419_);
lean_dec(v___x_419_);
lean_dec(v_p_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM(lean_object* v_N_421_){
_start:
{
lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_inc(v_N_421_);
v___f_422_ = lean_alloc_closure((void*)(lp_tree_Formalism_HermitianLatticeCounting_S6_minkowskiM___lam__0), 2, 1);
lean_closure_set(v___f_422_, 0, v_N_421_);
v___x_423_ = lean_unsigned_to_nat(2u);
v___x_424_ = lean_nat_add(v_N_421_, v___x_423_);
lean_dec(v_N_421_);
v___x_425_ = l_List_range(v___x_424_);
v___x_426_ = lp_mathlib_Multiset_filter___at___00Finset_filter___at___00primorial_spec__0_spec__0___redArg(v___x_425_);
v___x_427_ = lp_mathlib_Finset_prod___at___00primorial_spec__1___redArg(v___x_426_, v___f_422_);
return v___x_427_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic(uint8_t builtin) {
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
res = initialize_tree_Formalism_HyperbolicPlaceProducts_Statement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
