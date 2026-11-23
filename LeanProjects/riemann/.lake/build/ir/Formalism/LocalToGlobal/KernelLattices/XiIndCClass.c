// Lean compiler output
// Module: Formalism.LocalToGlobal.KernelLattices.XiIndCClass
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.GoodLat public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Pi_single___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_resA___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_resA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_resA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_homO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_homO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_perO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_perO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_twist_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_twist_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_laV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_laV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_LamC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_LamC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_resA___redArg(lean_object* v_00_u03a6_1_, lean_object* v_t_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_00_u03a6_1_, v_t_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_resA(lean_object* v_V_4_, lean_object* v_inst_5_, lean_object* v_A_6_, lean_object* v_00_u03a6_7_, lean_object* v_t_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_1(v_00_u03a6_7_, v_t_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_resA___boxed(lean_object* v_V_10_, lean_object* v_inst_11_, lean_object* v_A_12_, lean_object* v_00_u03a6_13_, lean_object* v_t_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_tree_Formalism_L2_Ker_resA(v_V_10_, v_inst_11_, v_A_12_, v_00_u03a6_13_, v_t_14_);
lean_dec_ref(v_inst_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__0(lean_object* v_toZero_16_, lean_object* v_i_17_){
_start:
{
lean_inc(v_toZero_16_);
return v_toZero_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__0___boxed(lean_object* v_toZero_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_L2_Ker_embH___redArg___lam__0(v_toZero_18_, v_i_19_);
lean_dec(v_i_19_);
lean_dec(v_toZero_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg___lam__1(lean_object* v_00_u03b4_24_, lean_object* v_a_25_, lean_object* v___f_26_, lean_object* v_toOne_27_, lean_object* v_emb_28_, lean_object* v_x_29_, lean_object* v_00_u03c4_30_, lean_object* v_i_31_, lean_object* v_j_32_){
_start:
{
lean_object* v_re_33_; lean_object* v_im_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___f_39_; lean_object* v___x_40_; 
v_re_33_ = lean_ctor_get(v_00_u03b4_24_, 0);
lean_inc(v_re_33_);
v_im_34_ = lean_ctor_get(v_00_u03b4_24_, 1);
lean_inc(v_im_34_);
lean_dec_ref(v_00_u03b4_24_);
v___x_35_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_35_, 0, v_a_25_);
v___x_36_ = lean_alloc_closure((void*)(lp_mathlib_Pi_single___boxed), 7, 6);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, v___f_26_);
lean_closure_set(v___x_36_, 3, v___x_35_);
lean_closure_set(v___x_36_, 4, v_j_32_);
lean_closure_set(v___x_36_, 5, v_toOne_27_);
v___x_37_ = lean_apply_2(v_x_29_, v___x_36_, v_i_31_);
v___x_38_ = lean_apply_2(v_emb_28_, v_00_u03c4_30_, v___x_37_);
v___f_39_ = ((lean_object*)(lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__1));
v___x_40_ = lp_mathlib_Complex_mulAux___redArg(v___f_39_, v_re_33_, v_im_34_, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___redArg(lean_object* v_inst_41_, lean_object* v_a_42_, lean_object* v_emb_43_, lean_object* v_00_u03b4_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toSemiring_47_; lean_object* v___x_48_; lean_object* v_toZero_49_; lean_object* v___x_50_; lean_object* v_toRing_51_; lean_object* v___x_52_; lean_object* v_toAddMonoidWithOne_53_; lean_object* v_toOne_54_; lean_object* v___f_55_; lean_object* v___f_56_; 
v___x_45_ = lp_mathlib_Field_toSemifield___redArg(v_inst_41_);
v___x_46_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_45_);
v_toSemiring_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_toSemiring_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_47_);
v_toZero_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_toZero_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_41_);
v_toRing_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc_ref(v_toRing_51_);
lean_dec_ref(v___x_50_);
v___x_52_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_51_);
v_toAddMonoidWithOne_53_ = lean_ctor_get(v___x_52_, 1);
lean_inc_ref(v_toAddMonoidWithOne_53_);
lean_dec_ref(v___x_52_);
v_toOne_54_ = lean_ctor_get(v_toAddMonoidWithOne_53_, 2);
lean_inc(v_toOne_54_);
lean_dec_ref(v_toAddMonoidWithOne_53_);
v___f_55_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_embH___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_55_, 0, v_toZero_49_);
v___f_56_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_embH___redArg___lam__1), 9, 5);
lean_closure_set(v___f_56_, 0, v_00_u03b4_44_);
lean_closure_set(v___f_56_, 1, v_a_42_);
lean_closure_set(v___f_56_, 2, v___f_55_);
lean_closure_set(v___f_56_, 3, v_toOne_54_);
lean_closure_set(v___f_56_, 4, v_emb_43_);
return v___f_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH(lean_object* v_E_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_00_u03b9_60_, lean_object* v_a_61_, lean_object* v_b_62_, lean_object* v_emb_63_, lean_object* v_00_u03b4_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_tree_Formalism_L2_Ker_embH___redArg(v_inst_58_, v_a_61_, v_emb_63_, v_00_u03b4_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_embH___boxed(lean_object* v_E_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_00_u03b9_69_, lean_object* v_a_70_, lean_object* v_b_71_, lean_object* v_emb_72_, lean_object* v_00_u03b4_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_L2_Ker_embH(v_E_66_, v_inst_67_, v_inst_68_, v_00_u03b9_69_, v_a_70_, v_b_71_, v_emb_72_, v_00_u03b4_73_);
lean_dec(v_b_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__0(lean_object* v_z_75_, lean_object* v_00_u03c4_76_, lean_object* v_i_77_, lean_object* v_w_78_, lean_object* v_j_79_){
_start:
{
lean_object* v___x_80_; lean_object* v_re_81_; lean_object* v_im_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___x_86_; 
lean_inc(v_j_79_);
lean_inc(v_i_77_);
lean_inc(v_00_u03c4_76_);
v___x_80_ = lean_apply_3(v_z_75_, v_00_u03c4_76_, v_i_77_, v_j_79_);
v_re_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_re_81_);
v_im_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_im_82_);
lean_dec_ref(v___x_80_);
v___x_83_ = lean_apply_3(v_w_78_, v_00_u03c4_76_, v_i_77_, v_j_79_);
v___x_84_ = lp_mathlib_Complex_instStarRing___lam__0(v___x_83_);
v___f_85_ = ((lean_object*)(lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__1));
v___x_86_ = lp_mathlib_Complex_mulAux___redArg(v___f_85_, v_re_81_, v_im_82_, v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__1(lean_object* v_z_87_, lean_object* v_00_u03c4_88_, lean_object* v_w_89_, lean_object* v_a_90_, lean_object* v___x_91_, lean_object* v_i_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_HV___redArg___lam__0), 5, 4);
lean_closure_set(v___f_93_, 0, v_z_87_);
lean_closure_set(v___f_93_, 1, v_00_u03c4_88_);
lean_closure_set(v___f_93_, 2, v_i_92_);
lean_closure_set(v___f_93_, 3, v_w_89_);
v___x_94_ = l_List_finRange(v_a_90_);
v___x_95_ = lp_mathlib_Finset_sum___redArg(v___x_91_, v___x_94_, v___f_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__1___boxed(lean_object* v_z_96_, lean_object* v_00_u03c4_97_, lean_object* v_w_98_, lean_object* v_a_99_, lean_object* v___x_100_, lean_object* v_i_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_tree_Formalism_L2_Ker_HV___redArg___lam__1(v_z_96_, v_00_u03c4_97_, v_w_98_, v_a_99_, v___x_100_, v_i_101_);
lean_dec_ref(v___x_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__2(lean_object* v_z_103_, lean_object* v_w_104_, lean_object* v_a_105_, lean_object* v___x_106_, lean_object* v_b_107_, lean_object* v_00_u03c4_108_){
_start:
{
lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
lean_inc_ref(v___x_106_);
v___f_109_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_HV___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_109_, 0, v_z_103_);
lean_closure_set(v___f_109_, 1, v_00_u03c4_108_);
lean_closure_set(v___f_109_, 2, v_w_104_);
lean_closure_set(v___f_109_, 3, v_a_105_);
lean_closure_set(v___f_109_, 4, v___x_106_);
v___x_110_ = l_List_finRange(v_b_107_);
v___x_111_ = lp_mathlib_Finset_sum___redArg(v___x_106_, v___x_110_, v___f_109_);
lean_dec_ref(v___x_106_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg___lam__3(lean_object* v_sc_112_, lean_object* v_a_113_, lean_object* v___x_114_, lean_object* v_b_115_, lean_object* v_inst_116_, lean_object* v_z_117_, lean_object* v_w_118_){
_start:
{
lean_object* v___x_119_; lean_object* v_re_120_; lean_object* v_im_121_; lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___f_124_; lean_object* v___x_125_; 
v___x_119_ = lp_mathlib_Complex_ofReal(v_sc_112_);
v_re_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_re_120_);
v_im_121_ = lean_ctor_get(v___x_119_, 1);
lean_inc(v_im_121_);
lean_dec_ref(v___x_119_);
lean_inc_ref(v___x_114_);
v___f_122_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_HV___redArg___lam__2), 6, 5);
lean_closure_set(v___f_122_, 0, v_z_117_);
lean_closure_set(v___f_122_, 1, v_w_118_);
lean_closure_set(v___f_122_, 2, v_a_113_);
lean_closure_set(v___f_122_, 3, v___x_114_);
lean_closure_set(v___f_122_, 4, v_b_115_);
v___x_123_ = lp_mathlib_Finset_sum___redArg(v___x_114_, v_inst_116_, v___f_122_);
lean_dec_ref(v___x_114_);
v___f_124_ = ((lean_object*)(lp_tree_Formalism_L2_Ker_embH___redArg___lam__1___closed__1));
v___x_125_ = lp_mathlib_Complex_mulAux___redArg(v___f_124_, v_re_120_, v_im_121_, v___x_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV___redArg(lean_object* v_inst_126_, lean_object* v_a_127_, lean_object* v_b_128_, lean_object* v_sc_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___f_131_; lean_object* v___f_132_; 
v___x_130_ = lp_mathlib_Complex_instAddCommMonoid;
v___f_131_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Ker_HV___redArg___lam__3), 7, 5);
lean_closure_set(v___f_131_, 0, v_sc_129_);
lean_closure_set(v___f_131_, 1, v_a_127_);
lean_closure_set(v___f_131_, 2, v___x_130_);
lean_closure_set(v___f_131_, 3, v_b_128_);
lean_closure_set(v___f_131_, 4, v_inst_126_);
v___f_132_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_mk_u2082_x27_u209b_u2097___redArg___lam__0), 3, 1);
lean_closure_set(v___f_132_, 0, v___f_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_HV(lean_object* v_00_u03b9_133_, lean_object* v_inst_134_, lean_object* v_a_135_, lean_object* v_b_136_, lean_object* v_sc_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_tree_Formalism_L2_Ker_HV___redArg(v_inst_134_, v_a_135_, v_b_136_, v_sc_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_homO(lean_object* v_E_139_, lean_object* v_inst_140_, lean_object* v_a_141_, lean_object* v_b_142_, lean_object* v_N_143_, lean_object* v_N_x27_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_homO___boxed(lean_object* v_E_146_, lean_object* v_inst_147_, lean_object* v_a_148_, lean_object* v_b_149_, lean_object* v_N_150_, lean_object* v_N_x27_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_tree_Formalism_L2_Ker_homO(v_E_146_, v_inst_147_, v_a_148_, v_b_149_, v_N_150_, v_N_x27_151_);
lean_dec(v_b_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_inst_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_perO(lean_object* v_E_153_, lean_object* v_inst_154_, lean_object* v_a_155_, lean_object* v_b_156_, lean_object* v_AA0_157_, lean_object* v_N_158_, lean_object* v_N_x27_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_perO___boxed(lean_object* v_E_161_, lean_object* v_inst_162_, lean_object* v_a_163_, lean_object* v_b_164_, lean_object* v_AA0_165_, lean_object* v_N_166_, lean_object* v_N_x27_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_tree_Formalism_L2_Ker_perO(v_E_161_, v_inst_162_, v_a_163_, v_b_164_, v_AA0_165_, v_N_166_, v_N_x27_167_);
lean_dec(v_b_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_inst_162_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_twist_u2082(lean_object* v_E_169_, lean_object* v_inst_170_, lean_object* v_W_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_M_176_, lean_object* v_c_177_, lean_object* v_e_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_box(0);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_twist_u2082___boxed(lean_object* v_E_180_, lean_object* v_inst_181_, lean_object* v_W_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_M_187_, lean_object* v_c_188_, lean_object* v_e_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_tree_Formalism_L2_Ker_twist_u2082(v_E_180_, v_inst_181_, v_W_182_, v_inst_183_, v_inst_184_, v_inst_185_, v_inst_186_, v_M_187_, v_c_188_, v_e_189_);
lean_dec_ref(v_e_189_);
lean_dec(v_c_188_);
lean_dec(v_inst_185_);
lean_dec(v_inst_184_);
lean_dec_ref(v_inst_183_);
lean_dec_ref(v_inst_181_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_laV(lean_object* v_E_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_00_u03b9_194_, lean_object* v_a_195_, lean_object* v_b_196_, lean_object* v_emb_197_, lean_object* v_00_u03b4_198_, lean_object* v_M_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_laV___boxed(lean_object* v_E_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_00_u03b9_204_, lean_object* v_a_205_, lean_object* v_b_206_, lean_object* v_emb_207_, lean_object* v_00_u03b4_208_, lean_object* v_M_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = lp_tree_Formalism_L2_Ker_laV(v_E_201_, v_inst_202_, v_inst_203_, v_00_u03b9_204_, v_a_205_, v_b_206_, v_emb_207_, v_00_u03b4_208_, v_M_209_);
lean_dec_ref(v_00_u03b4_208_);
lean_dec_ref(v_emb_207_);
lean_dec(v_b_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_inst_202_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_LamC(lean_object* v_E_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_00_u03b9_214_, lean_object* v_a_215_, lean_object* v_b_216_, lean_object* v_emb_217_, lean_object* v_00_u03b4_218_, lean_object* v_AA0_219_, lean_object* v_N_220_, lean_object* v_N_x27_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Ker_LamC___boxed(lean_object* v_E_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_00_u03b9_226_, lean_object* v_a_227_, lean_object* v_b_228_, lean_object* v_emb_229_, lean_object* v_00_u03b4_230_, lean_object* v_AA0_231_, lean_object* v_N_232_, lean_object* v_N_x27_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = lp_tree_Formalism_L2_Ker_LamC(v_E_223_, v_inst_224_, v_inst_225_, v_00_u03b9_226_, v_a_227_, v_b_228_, v_emb_229_, v_00_u03b4_230_, v_AA0_231_, v_N_232_, v_N_x27_233_);
lean_dec_ref(v_00_u03b4_230_);
lean_dec_ref(v_emb_229_);
lean_dec(v_b_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_inst_224_);
return v_res_234_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GoodLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_KernelLattices_XiIndCClass(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_GoodLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_FiniteSumNonzeroLargeDepth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
