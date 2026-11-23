// Lean compiler output
// Module: Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.SharpRestriction.CuspSpanNormBounds.Point
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
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instCommSemiring;
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_AddChar_compAddMonoidHom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ENNReal_toNNReal(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_psiR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_psiR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_psiR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_modK___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_modK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_modK___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_isoSetoid(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_isoSetoid___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_S_Loc_sameBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_sameBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uLow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uLow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uLow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_detMod___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_detMod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_detMod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg___lam__0(lean_object* v_g_1_, lean_object* v_toSub_2_, lean_object* v_toDiv_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_e_5_; lean_object* v_q_6_; lean_object* v_toFun_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_e_5_ = lean_ctor_get(v_g_1_, 0);
lean_inc_ref(v_e_5_);
v_q_6_ = lean_ctor_get(v_g_1_, 1);
lean_inc(v_q_6_);
lean_dec_ref(v_g_1_);
v_toFun_7_ = lean_ctor_get(v_e_5_, 0);
lean_inc(v_toFun_7_);
lean_dec_ref(v_e_5_);
v___x_8_ = lean_apply_1(v_toFun_7_, v_x_4_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_apply_2(v_toSub_2_, v_fst_9_, v_snd_10_);
v___x_12_ = lean_apply_2(v_toDiv_3_, v___x_11_, v_q_6_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg(lean_object* v_inst_13_, lean_object* v_g_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_toRing_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_toDiv_19_; lean_object* v___x_20_; lean_object* v_toSub_21_; lean_object* v___f_22_; 
v___x_15_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_13_);
v_toRing_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_toRing_16_);
v___x_17_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_16_);
v___x_18_ = lp_mathlib_DivisionRing_toDivInvMonoid___redArg(v___x_15_);
lean_dec_ref(v___x_15_);
v_toDiv_19_ = lean_ctor_get(v___x_18_, 2);
lean_inc(v_toDiv_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_17_);
lean_dec_ref(v___x_17_);
v_toSub_21_ = lean_ctor_get(v___x_20_, 2);
lean_inc(v_toSub_21_);
lean_dec_ref(v___x_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg___lam__0), 4, 3);
lean_closure_set(v___f_22_, 0, v_g_14_);
lean_closure_set(v___f_22_, 1, v_toSub_21_);
lean_closure_set(v___f_22_, 2, v_toDiv_19_);
return v___f_22_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR(lean_object* v_F_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_E_27_, lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_M_32_, lean_object* v_g_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg(v_inst_24_, v_g_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_trR___boxed(lean_object* v_F_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_E_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_M_44_, lean_object* v_g_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Formalism_MainNotions_S_Loc_Model_trR(v_F_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_E_39_, v_inst_40_, v_inst_41_, v_inst_42_, v_inst_43_, v_M_44_, v_g_45_);
lean_dec_ref(v_M_44_);
lean_dec_ref(v_inst_41_);
lean_dec_ref(v_inst_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_psiR___redArg(lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_M_49_){
_start:
{
lean_object* v___x_50_; lean_object* v_toMonoid_51_; lean_object* v___x_52_; lean_object* v_toAddMonoidWithOne_53_; lean_object* v_split_54_; 
v___x_50_ = lp_mathlib_Complex_instCommSemiring;
v_toMonoid_51_ = lean_ctor_get(v___x_50_, 1);
v___x_52_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_48_);
v_toAddMonoidWithOne_53_ = lean_ctor_get(v___x_52_, 1);
lean_inc_ref(v_toAddMonoidWithOne_53_);
lean_dec_ref(v___x_52_);
v_split_54_ = lean_ctor_get(v_M_49_, 1);
if (lean_obj_tag(v_split_54_) == 0)
{
lean_object* v_L_55_; lean_object* v_psi0_56_; 
lean_dec_ref(v_toAddMonoidWithOne_53_);
lean_dec_ref(v_inst_47_);
v_L_55_ = lean_ctor_get(v_M_49_, 0);
lean_inc_ref(v_L_55_);
lean_dec_ref(v_M_49_);
v_psi0_56_ = lean_ctor_get(v_L_55_, 2);
lean_inc_ref(v_psi0_56_);
lean_dec_ref(v_L_55_);
return v_psi0_56_;
}
else
{
lean_object* v_val_57_; lean_object* v_toAddMonoid_58_; lean_object* v_psiF_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_inc_ref(v_split_54_);
lean_dec_ref(v_M_49_);
v_val_57_ = lean_ctor_get(v_split_54_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_split_54_, 1);
v_toAddMonoid_58_ = lean_ctor_get(v_toAddMonoidWithOne_53_, 1);
lean_inc_ref(v_toAddMonoid_58_);
lean_dec_ref(v_toAddMonoidWithOne_53_);
v_psiF_59_ = lean_ctor_get(v_val_57_, 2);
lean_inc_ref(v_psiF_59_);
v___x_60_ = lp_tree_Formalism_MainNotions_S_Loc_Model_trR___redArg(v_inst_47_, v_val_57_);
v___x_61_ = lp_mathlib_AddChar_compAddMonoidHom___redArg(v_toAddMonoid_58_, v_toMonoid_51_, v_psiF_59_, v___x_60_);
lean_dec_ref(v_toAddMonoid_58_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_psiR(lean_object* v_F_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_E_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_M_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_tree_Formalism_MainNotions_S_Loc_Model_psiR___redArg(v_inst_63_, v_inst_67_, v_M_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_psiR___boxed(lean_object* v_F_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_E_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_M_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_tree_Formalism_MainNotions_S_Loc_Model_psiR(v_F_73_, v_inst_74_, v_inst_75_, v_inst_76_, v_E_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_inst_81_, v_M_82_);
lean_dec_ref(v_inst_79_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_modK___redArg(lean_object* v_M_84_){
_start:
{
lean_object* v_mu_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_mu_85_ = lean_ctor_get(v_M_84_, 2);
lean_inc_ref(v_mu_85_);
lean_dec_ref(v_M_84_);
v___x_86_ = lean_apply_1(v_mu_85_, lean_box(0));
v___x_87_ = lp_mathlib_ENNReal_toNNReal(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_modK(lean_object* v_F_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_E_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_M_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_tree_Formalism_MainNotions_S_Loc_Model_modK___redArg(v_M_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_modK___boxed(lean_object* v_F_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_E_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_M_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_tree_Formalism_MainNotions_S_Loc_Model_modK(v_F_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_E_104_, v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_M_109_, v_x_110_);
lean_dec(v_x_110_);
lean_dec_ref(v_inst_106_);
lean_dec_ref(v_inst_105_);
lean_dec_ref(v_inst_101_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_isoSetoid(lean_object* v_F_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_E_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_M_121_, lean_object* v_m_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_isoSetoid___boxed(lean_object* v_F_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_E_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_M_133_, lean_object* v_m_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_tree_Formalism_MainNotions_S_Loc_Model_isoSetoid(v_F_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_E_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_inst_132_, v_M_133_, v_m_134_);
lean_dec(v_m_134_);
lean_dec_ref(v_M_133_);
lean_dec_ref(v_inst_130_);
lean_dec_ref(v_inst_129_);
lean_dec_ref(v_inst_125_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg(lean_object* v_inst_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_toSemiring_140_; lean_object* v___x_141_; 
v_toSemiring_140_ = lean_ctor_get(v_inst_136_, 0);
lean_inc_ref(v_toSemiring_140_);
v___x_141_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_140_);
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_toZero_142_; 
lean_dec(v_x_139_);
lean_dec(v_x_138_);
lean_dec_ref(v_inst_136_);
v_toZero_142_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_toZero_142_);
lean_dec_ref(v___x_141_);
return v_toZero_142_;
}
else
{
lean_object* v_head_143_; lean_object* v_toZero_144_; lean_object* v_tail_145_; lean_object* v_fst_146_; lean_object* v_snd_147_; uint8_t v___x_154_; 
v_head_143_ = lean_ctor_get(v_x_137_, 0);
v_toZero_144_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_toZero_144_);
lean_dec_ref(v___x_141_);
v_tail_145_ = lean_ctor_get(v_x_137_, 1);
v_fst_146_ = lean_ctor_get(v_head_143_, 0);
v_snd_147_ = lean_ctor_get(v_head_143_, 1);
v___x_154_ = lean_nat_dec_lt(v_x_138_, v_snd_147_);
if (v___x_154_ == 0)
{
goto v___jp_148_;
}
else
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_lt(v_x_139_, v_snd_147_);
if (v___x_155_ == 0)
{
goto v___jp_148_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
lean_dec_ref(v_inst_136_);
v___x_156_ = lean_nat_add(v_x_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec(v_x_138_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v___x_156_, v___x_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_nat_dec_eq(v___x_158_, v_snd_147_);
lean_dec(v___x_158_);
if (v___x_159_ == 0)
{
return v_toZero_144_;
}
else
{
lean_object* v_val_160_; 
lean_dec(v_toZero_144_);
v_val_160_ = lean_ctor_get(v_fst_146_, 0);
lean_inc(v_val_160_);
return v_val_160_;
}
}
}
v___jp_148_:
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_le(v_snd_147_, v_x_138_);
if (v___x_149_ == 0)
{
lean_dec(v_x_139_);
lean_dec(v_x_138_);
lean_dec_ref(v_inst_136_);
return v_toZero_144_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v_snd_147_, v_x_139_);
if (v___x_150_ == 0)
{
lean_dec(v_x_139_);
lean_dec(v_x_138_);
lean_dec_ref(v_inst_136_);
return v_toZero_144_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_toZero_144_);
v___x_151_ = lean_nat_sub(v_x_138_, v_snd_147_);
lean_dec(v_x_138_);
v___x_152_ = lean_nat_sub(v_x_139_, v_snd_147_);
lean_dec(v_x_139_);
v_x_137_ = v_tail_145_;
v_x_138_ = v___x_151_;
v_x_139_ = v___x_152_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg___boxed(lean_object* v_inst_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg(v_inst_161_, v_x_162_, v_x_163_, v_x_164_);
lean_dec(v_x_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL(lean_object* v_E_166_, lean_object* v_inst_167_, lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg(v_inst_167_, v_x_168_, v_x_169_, v_x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___boxed(lean_object* v_E_172_, lean_object* v_inst_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = lp_tree_Formalism_MainNotions_S_Loc_ptEntryL(v_E_172_, v_inst_173_, v_x_174_, v_x_175_, v_x_176_);
lean_dec(v_x_174_);
return v_res_177_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg(lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
uint8_t v___x_181_; 
lean_dec(v_x_180_);
lean_dec(v_x_179_);
v___x_181_ = 0;
return v___x_181_;
}
else
{
lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v_snd_184_; uint8_t v___y_186_; uint8_t v___y_191_; uint8_t v___x_194_; 
v_head_182_ = lean_ctor_get(v_x_178_, 0);
v_tail_183_ = lean_ctor_get(v_x_178_, 1);
v_snd_184_ = lean_ctor_get(v_head_182_, 1);
v___x_194_ = lean_nat_dec_lt(v_x_179_, v_snd_184_);
if (v___x_194_ == 0)
{
v___y_191_ = v___x_194_;
goto v___jp_190_;
}
else
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_lt(v_x_180_, v_snd_184_);
v___y_191_ = v___x_195_;
goto v___jp_190_;
}
v___jp_185_:
{
if (v___y_186_ == 0)
{
lean_dec(v_x_180_);
lean_dec(v_x_179_);
return v___y_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_nat_sub(v_x_179_, v_snd_184_);
lean_dec(v_x_179_);
v___x_188_ = lean_nat_sub(v_x_180_, v_snd_184_);
lean_dec(v_x_180_);
v_x_178_ = v_tail_183_;
v_x_179_ = v___x_187_;
v_x_180_ = v___x_188_;
goto _start;
}
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_le(v_snd_184_, v_x_179_);
if (v___x_192_ == 0)
{
v___y_186_ = v___x_192_;
goto v___jp_185_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_le(v_snd_184_, v_x_180_);
v___y_186_ = v___x_193_;
goto v___jp_185_;
}
}
else
{
lean_dec(v_x_180_);
lean_dec(v_x_179_);
return v___y_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg___boxed(lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg(v_x_196_, v_x_197_, v_x_198_);
lean_dec(v_x_196_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_S_Loc_sameBlock(lean_object* v_E_201_, lean_object* v_inst_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg(v_x_203_, v_x_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_sameBlock___boxed(lean_object* v_E_207_, lean_object* v_inst_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = lp_tree_Formalism_MainNotions_S_Loc_sameBlock(v_E_207_, v_inst_208_, v_x_209_, v_x_210_, v_x_211_);
lean_dec(v_x_209_);
lean_dec_ref(v_inst_208_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___redArg(lean_object* v_inst_214_, lean_object* v_w_215_, lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg(v_inst_214_, v_w_215_, v_a_216_, v_b_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___redArg___boxed(lean_object* v_inst_219_, lean_object* v_w_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___redArg(v_inst_219_, v_w_220_, v_a_221_, v_b_222_);
lean_dec(v_w_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat(lean_object* v_E_224_, lean_object* v_inst_225_, lean_object* v_n_226_, lean_object* v_w_227_, lean_object* v_a_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lp_tree_Formalism_MainNotions_S_Loc_ptEntryL___redArg(v_inst_225_, v_w_227_, v_a_228_, v_b_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_mat___boxed(lean_object* v_E_231_, lean_object* v_inst_232_, lean_object* v_n_233_, lean_object* v_w_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_tree_Formalism_MainNotions_S_Loc_Pt_mat(v_E_231_, v_inst_232_, v_n_233_, v_w_234_, v_a_235_, v_b_236_);
lean_dec(v_w_234_);
lean_dec(v_n_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc___redArg(lean_object* v_h_238_, lean_object* v_t_239_, lean_object* v_s_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_t_239_);
lean_ctor_set(v___x_241_, 1, v_s_240_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_List_appendTR___redArg(v_h_238_, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc(lean_object* v_E_245_, lean_object* v_inst_246_, lean_object* v_n_247_, lean_object* v_h_248_, lean_object* v_t_249_, lean_object* v_s_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc___redArg(v_h_248_, v_t_249_, v_s_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc___boxed(lean_object* v_E_252_, lean_object* v_inst_253_, lean_object* v_n_254_, lean_object* v_h_255_, lean_object* v_t_256_, lean_object* v_s_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = lp_tree_Formalism_MainNotions_S_Loc_Pt_snoc(v_E_252_, v_inst_253_, v_n_254_, v_h_255_, v_t_256_, v_s_257_);
lean_dec(v_n_254_);
lean_dec_ref(v_inst_253_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uLow___redArg(lean_object* v_inst_259_, lean_object* v_x_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_nat_dec_eq(v_a_261_, v_b_262_);
if (v___x_263_ == 0)
{
uint8_t v___x_264_; 
v___x_264_ = lean_nat_dec_lt(v_b_262_, v_a_261_);
if (v___x_264_ == 0)
{
lean_object* v_toSemiring_265_; lean_object* v___x_266_; lean_object* v_toZero_267_; 
lean_dec(v_b_262_);
lean_dec(v_a_261_);
lean_dec(v_x_260_);
v_toSemiring_265_ = lean_ctor_get(v_inst_259_, 0);
lean_inc_ref(v_toSemiring_265_);
lean_dec_ref(v_inst_259_);
v___x_266_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_265_);
v_toZero_267_ = lean_ctor_get(v___x_266_, 1);
lean_inc(v_toZero_267_);
lean_dec_ref(v___x_266_);
return v_toZero_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v_inst_259_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_a_261_);
lean_ctor_set(v___x_268_, 1, v_b_262_);
v___x_269_ = lean_apply_1(v_x_260_, v___x_268_);
return v___x_269_;
}
}
else
{
lean_object* v___x_270_; lean_object* v_toAddMonoidWithOne_271_; lean_object* v_toOne_272_; 
lean_dec(v_b_262_);
lean_dec(v_a_261_);
lean_dec(v_x_260_);
v___x_270_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_259_);
v_toAddMonoidWithOne_271_ = lean_ctor_get(v___x_270_, 1);
lean_inc_ref(v_toAddMonoidWithOne_271_);
lean_dec_ref(v___x_270_);
v_toOne_272_ = lean_ctor_get(v_toAddMonoidWithOne_271_, 2);
lean_inc(v_toOne_272_);
lean_dec_ref(v_toAddMonoidWithOne_271_);
return v_toOne_272_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uLow(lean_object* v_E_273_, lean_object* v_inst_274_, lean_object* v_n_275_, lean_object* v_x_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lp_tree_Formalism_MainNotions_S_Loc_uLow___redArg(v_inst_274_, v_x_276_, v_a_277_, v_b_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uLow___boxed(lean_object* v_E_280_, lean_object* v_inst_281_, lean_object* v_n_282_, lean_object* v_x_283_, lean_object* v_a_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = lp_tree_Formalism_MainNotions_S_Loc_uLow(v_E_280_, v_inst_281_, v_n_282_, v_x_283_, v_a_284_, v_b_285_);
lean_dec(v_n_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp___redArg(lean_object* v_inst_287_, lean_object* v_w_288_, lean_object* v_y_289_, lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_eq(v_a_290_, v_b_291_);
if (v___x_296_ == 0)
{
uint8_t v___x_297_; 
v___x_297_ = lean_nat_dec_lt(v_a_290_, v_b_291_);
if (v___x_297_ == 0)
{
lean_dec(v_b_291_);
lean_dec(v_a_290_);
lean_dec(v_y_289_);
goto v___jp_292_;
}
else
{
uint8_t v___x_298_; 
lean_inc(v_b_291_);
lean_inc(v_a_290_);
v___x_298_ = lp_tree_Formalism_MainNotions_S_Loc_sameBlock___redArg(v_w_288_, v_a_290_, v_b_291_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_inst_287_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_a_290_);
lean_ctor_set(v___x_299_, 1, v_b_291_);
v___x_300_ = lean_apply_1(v_y_289_, v___x_299_);
return v___x_300_;
}
else
{
lean_dec(v_b_291_);
lean_dec(v_a_290_);
lean_dec(v_y_289_);
goto v___jp_292_;
}
}
}
else
{
lean_object* v___x_301_; lean_object* v_toAddMonoidWithOne_302_; lean_object* v_toOne_303_; 
lean_dec(v_b_291_);
lean_dec(v_a_290_);
lean_dec(v_y_289_);
v___x_301_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_287_);
v_toAddMonoidWithOne_302_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_toAddMonoidWithOne_302_);
lean_dec_ref(v___x_301_);
v_toOne_303_ = lean_ctor_get(v_toAddMonoidWithOne_302_, 2);
lean_inc(v_toOne_303_);
lean_dec_ref(v_toAddMonoidWithOne_302_);
return v_toOne_303_;
}
v___jp_292_:
{
lean_object* v_toSemiring_293_; lean_object* v___x_294_; lean_object* v_toZero_295_; 
v_toSemiring_293_ = lean_ctor_get(v_inst_287_, 0);
lean_inc_ref(v_toSemiring_293_);
lean_dec_ref(v_inst_287_);
v___x_294_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_293_);
v_toZero_295_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_toZero_295_);
lean_dec_ref(v___x_294_);
return v_toZero_295_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp___redArg___boxed(lean_object* v_inst_304_, lean_object* v_w_305_, lean_object* v_y_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = lp_tree_Formalism_MainNotions_S_Loc_uUp___redArg(v_inst_304_, v_w_305_, v_y_306_, v_a_307_, v_b_308_);
lean_dec(v_w_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp(lean_object* v_E_310_, lean_object* v_inst_311_, lean_object* v_n_312_, lean_object* v_w_313_, lean_object* v_y_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lp_tree_Formalism_MainNotions_S_Loc_uUp___redArg(v_inst_311_, v_w_313_, v_y_314_, v_a_315_, v_b_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_uUp___boxed(lean_object* v_E_318_, lean_object* v_inst_319_, lean_object* v_n_320_, lean_object* v_w_321_, lean_object* v_y_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = lp_tree_Formalism_MainNotions_S_Loc_uUp(v_E_318_, v_inst_319_, v_n_320_, v_w_321_, v_y_322_, v_a_323_, v_b_324_);
lean_dec(v_w_321_);
lean_dec(v_n_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__0(lean_object* v_a_326_, lean_object* v_toSemiring_327_, lean_object* v_A_328_, lean_object* v_b_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_b_329_, v___x_330_);
v___x_332_ = lean_nat_dec_eq(v_a_326_, v___x_331_);
lean_dec(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v_toZero_334_; 
lean_dec(v_b_329_);
lean_dec(v_A_328_);
lean_dec(v_a_326_);
v___x_333_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_327_);
v_toZero_334_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_toZero_334_);
lean_dec_ref(v___x_333_);
return v_toZero_334_;
}
else
{
lean_object* v___x_335_; 
lean_dec_ref(v_toSemiring_327_);
v___x_335_ = lean_apply_2(v_A_328_, v_a_326_, v_b_329_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__1(lean_object* v_toSemiring_336_, lean_object* v_A_337_, lean_object* v_toAddCommMonoid_338_, lean_object* v___x_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___f_341_; lean_object* v___x_342_; 
v___f_341_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__0), 4, 3);
lean_closure_set(v___f_341_, 0, v_a_340_);
lean_closure_set(v___f_341_, 1, v_toSemiring_336_);
lean_closure_set(v___f_341_, 2, v_A_337_);
v___x_342_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_338_, v___x_339_, v___f_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__1___boxed(lean_object* v_toSemiring_343_, lean_object* v_A_344_, lean_object* v_toAddCommMonoid_345_, lean_object* v___x_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__1(v_toSemiring_343_, v_A_344_, v_toAddCommMonoid_345_, v___x_346_, v_a_347_);
lean_dec_ref(v_toAddCommMonoid_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg(lean_object* v_inst_349_, lean_object* v_n_350_, lean_object* v_A_351_){
_start:
{
lean_object* v_toSemiring_352_; lean_object* v_toAddCommMonoid_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___x_356_; 
v_toSemiring_352_ = lean_ctor_get(v_inst_349_, 0);
lean_inc_ref(v_toSemiring_352_);
lean_dec_ref(v_inst_349_);
v_toAddCommMonoid_353_ = lean_ctor_get(v_toSemiring_352_, 0);
lean_inc_ref_n(v_toAddCommMonoid_353_, 2);
v___x_354_ = l_List_finRange(v_n_350_);
lean_inc(v___x_354_);
v___f_355_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_355_, 0, v_toSemiring_352_);
lean_closure_set(v___f_355_, 1, v_A_351_);
lean_closure_set(v___f_355_, 2, v_toAddCommMonoid_353_);
lean_closure_set(v___f_355_, 3, v___x_354_);
v___x_356_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_353_, v___x_354_, v___f_355_);
lean_dec_ref(v_toAddCommMonoid_353_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleLow(lean_object* v_E_357_, lean_object* v_inst_358_, lean_object* v_n_359_, lean_object* v_A_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lp_tree_Formalism_MainNotions_S_Loc_simpleLow___redArg(v_inst_358_, v_n_359_, v_A_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__0(lean_object* v_a_362_, lean_object* v_toSemiring_363_, lean_object* v_A_364_, lean_object* v_b_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_a_362_, v___x_366_);
v___x_368_ = lean_nat_dec_eq(v_b_365_, v___x_367_);
lean_dec(v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v_toZero_370_; 
lean_dec(v_b_365_);
lean_dec(v_A_364_);
lean_dec(v_a_362_);
v___x_369_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_363_);
v_toZero_370_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_toZero_370_);
lean_dec_ref(v___x_369_);
return v_toZero_370_;
}
else
{
lean_object* v___x_371_; 
lean_dec_ref(v_toSemiring_363_);
v___x_371_ = lean_apply_2(v_A_364_, v_a_362_, v_b_365_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__1(lean_object* v_toSemiring_372_, lean_object* v_A_373_, lean_object* v_toAddCommMonoid_374_, lean_object* v___x_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___f_377_; lean_object* v___x_378_; 
v___f_377_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_377_, 0, v_a_376_);
lean_closure_set(v___f_377_, 1, v_toSemiring_372_);
lean_closure_set(v___f_377_, 2, v_A_373_);
v___x_378_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_374_, v___x_375_, v___f_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__1___boxed(lean_object* v_toSemiring_379_, lean_object* v_A_380_, lean_object* v_toAddCommMonoid_381_, lean_object* v___x_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__1(v_toSemiring_379_, v_A_380_, v_toAddCommMonoid_381_, v___x_382_, v_a_383_);
lean_dec_ref(v_toAddCommMonoid_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg(lean_object* v_inst_385_, lean_object* v_n_386_, lean_object* v_A_387_){
_start:
{
lean_object* v_toSemiring_388_; lean_object* v_toAddCommMonoid_389_; lean_object* v___x_390_; lean_object* v___f_391_; lean_object* v___x_392_; 
v_toSemiring_388_ = lean_ctor_get(v_inst_385_, 0);
lean_inc_ref(v_toSemiring_388_);
lean_dec_ref(v_inst_385_);
v_toAddCommMonoid_389_ = lean_ctor_get(v_toSemiring_388_, 0);
lean_inc_ref_n(v_toAddCommMonoid_389_, 2);
v___x_390_ = l_List_finRange(v_n_386_);
lean_inc(v___x_390_);
v___f_391_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_391_, 0, v_toSemiring_388_);
lean_closure_set(v___f_391_, 1, v_A_387_);
lean_closure_set(v___f_391_, 2, v_toAddCommMonoid_389_);
lean_closure_set(v___f_391_, 3, v___x_390_);
v___x_392_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_389_, v___x_390_, v___f_391_);
lean_dec_ref(v_toAddCommMonoid_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_simpleUp(lean_object* v_E_393_, lean_object* v_inst_394_, lean_object* v_n_395_, lean_object* v_A_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lp_tree_Formalism_MainNotions_S_Loc_simpleUp___redArg(v_inst_394_, v_n_395_, v_A_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_detMod___redArg(lean_object* v_M_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lp_tree_Formalism_MainNotions_S_Loc_Model_modK___redArg(v_M_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_detMod(lean_object* v_F_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_E_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_M_409_, lean_object* v_m_410_, lean_object* v_h_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lp_tree_Formalism_MainNotions_S_Loc_Model_modK___redArg(v_M_409_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Model_detMod___boxed(lean_object* v_F_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_E_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_M_422_, lean_object* v_m_423_, lean_object* v_h_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = lp_tree_Formalism_MainNotions_S_Loc_Model_detMod(v_F_413_, v_inst_414_, v_inst_415_, v_inst_416_, v_E_417_, v_inst_418_, v_inst_419_, v_inst_420_, v_inst_421_, v_M_422_, v_m_423_, v_h_424_);
lean_dec(v_h_424_);
lean_dec(v_m_423_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
lean_dec_ref(v_inst_414_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___redArg(lean_object* v_w_426_){
_start:
{
lean_inc(v_w_426_);
return v_w_426_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___redArg___boxed(lean_object* v_w_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___redArg(v_w_427_);
lean_dec(v_w_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast(lean_object* v_E_429_, lean_object* v_inst_430_, lean_object* v_n_431_, lean_object* v_n_x27_432_, lean_object* v_e_433_, lean_object* v_w_434_){
_start:
{
lean_inc(v_w_434_);
return v_w_434_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_S_Loc_Pt_cast___boxed(lean_object* v_E_435_, lean_object* v_inst_436_, lean_object* v_n_437_, lean_object* v_n_x27_438_, lean_object* v_e_439_, lean_object* v_w_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = lp_tree_Formalism_MainNotions_S_Loc_Pt_cast(v_E_435_, v_inst_436_, v_n_437_, v_n_x27_438_, v_e_439_, v_w_440_);
lean_dec(v_w_440_);
lean_dec(v_n_x27_438_);
lean_dec(v_n_437_);
lean_dec_ref(v_inst_436_);
return v_res_441_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_Point(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq(uint8_t builtin) {
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
res = initialize_tree_Formalism_SharpRestriction_CuspSpanNormBounds_Point(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
