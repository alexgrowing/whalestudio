// Lean compiler output
// Module: Lib.GLn.SchurModule.LeadingRows
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.GramMatrix
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Fin_castAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_natAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_attach___redArg(lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_leadingWedge___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_leadingWedge___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_leadingWedge___redArg___closed__0 = (const lean_object*)&lp_GRH_New_leadingWedge___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_GLn_SchurModule_LeadingRows_0__New_schurComplementArray_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_GLn_SchurModule_LeadingRows_0__New_schurComplementArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__0;
static lean_once_cell_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_leadingWedgeMatrix___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___closed__0;
static const lean_closure_object lp_GRH_New_leadingWedgeMatrix___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_leadingWedgeMatrix___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___closed__1 = (const lean_object*)&lp_GRH_New_leadingWedgeMatrix___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns___redArg(lean_object* v_q_1_, lean_object* v_00_u03ba_2_, lean_object* v_00_u03c4_3_, lean_object* v_h_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_00_u03c4_3_);
v___x_5_ = lean_apply_1(v_q_1_, v_00_u03c4_3_);
v___x_6_ = lean_nat_add(v___x_5_, v_h_4_);
lean_dec(v___x_5_);
v___x_7_ = lean_apply_2(v_00_u03ba_2_, v_00_u03c4_3_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns___redArg___boxed(lean_object* v_q_8_, lean_object* v_00_u03ba_9_, lean_object* v_00_u03c4_10_, lean_object* v_h_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GRH_New_flatColumns___redArg(v_q_8_, v_00_u03ba_9_, v_00_u03c4_10_, v_h_11_);
lean_dec(v_h_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns(lean_object* v_00_u03a6_13_, lean_object* v_q_14_, lean_object* v_00_u03ba_15_, lean_object* v_00_u03c4_16_, lean_object* v_h_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc(v_00_u03c4_16_);
v___x_18_ = lean_apply_1(v_q_14_, v_00_u03c4_16_);
v___x_19_ = lean_nat_add(v___x_18_, v_h_17_);
lean_dec(v___x_18_);
v___x_20_ = lean_apply_2(v_00_u03ba_15_, v_00_u03c4_16_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_flatColumns___boxed(lean_object* v_00_u03a6_21_, lean_object* v_q_22_, lean_object* v_00_u03ba_23_, lean_object* v_00_u03c4_24_, lean_object* v_h_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_GRH_New_flatColumns(v_00_u03a6_21_, v_q_22_, v_00_u03ba_23_, v_00_u03c4_24_, v_h_25_);
lean_dec(v_h_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg___lam__0(lean_object* v_h_27_, lean_object* v_x_28_, lean_object* v___y_29_){
_start:
{
lean_inc(v___y_29_);
return v___y_29_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg___lam__0___boxed(lean_object* v_h_30_, lean_object* v_x_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH_New_leadingWedge___redArg___lam__0(v_h_30_, v_x_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec(v_x_31_);
lean_dec(v_h_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg___lam__1(lean_object* v___x_34_, lean_object* v___x_35_, lean_object* v_T_36_, lean_object* v_00_u03c4_37_, lean_object* v_k_38_, lean_object* v_j_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
lean_inc(v___x_35_);
lean_inc_n(v___x_34_, 2);
v___x_41_ = lean_alloc_closure((void*)(l_Fin_castAdd___boxed), 3, 2);
lean_closure_set(v___x_41_, 0, v___x_34_);
lean_closure_set(v___x_41_, 1, v___x_35_);
v___x_42_ = lean_alloc_closure((void*)(l_Fin_natAdd___boxed), 3, 2);
lean_closure_set(v___x_42_, 0, v___x_35_);
lean_closure_set(v___x_42_, 1, v___x_34_);
v___x_43_ = lean_apply_3(v_T_36_, v_00_u03c4_37_, v_k_38_, v_j_39_);
v___x_44_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_44_, 0, lean_box(0));
lean_closure_set(v___x_44_, 1, lean_box(0));
lean_closure_set(v___x_44_, 2, lean_box(0));
lean_closure_set(v___x_44_, 3, v___x_42_);
lean_closure_set(v___x_44_, 4, v___x_43_);
v___x_45_ = l_Fin_addCases___redArg(v___x_34_, v___x_41_, v___x_44_, v___y_40_);
lean_dec(v___x_34_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___redArg(lean_object* v_inst_47_, lean_object* v_q_48_, lean_object* v_T_49_, lean_object* v_00_u03c4_50_, lean_object* v_h_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___x_77__overap_58_; lean_object* v___x_59_; 
v___f_53_ = ((lean_object*)(lp_GRH_New_leadingWedge___redArg___closed__0));
lean_inc_n(v_00_u03c4_50_, 2);
v___x_54_ = lean_apply_1(v_q_48_, v_00_u03c4_50_);
v___x_55_ = lean_apply_1(v_inst_47_, v_00_u03c4_50_);
v___x_56_ = l_List_lengthTR___redArg(v___x_55_);
lean_dec(v___x_55_);
lean_inc(v___x_54_);
v___f_57_ = lean_alloc_closure((void*)(lp_GRH_New_leadingWedge___redArg___lam__1), 7, 4);
lean_closure_set(v___f_57_, 0, v___x_54_);
lean_closure_set(v___f_57_, 1, v___x_56_);
lean_closure_set(v___f_57_, 2, v_T_49_);
lean_closure_set(v___f_57_, 3, v_00_u03c4_50_);
v___x_77__overap_58_ = l_Fin_addCases___redArg(v___x_54_, v___f_53_, v___f_57_, v_h_51_);
lean_dec(v___x_54_);
v___x_59_ = lean_apply_1(v___x_77__overap_58_, v_a_52_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge(lean_object* v_00_u03a6_60_, lean_object* v_n_61_, lean_object* v_m_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_q_65_, lean_object* v_00_u03ba_66_, lean_object* v_h__rank_67_, lean_object* v_T_68_, lean_object* v_00_u03c4_69_, lean_object* v_h_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_GRH_New_leadingWedge___redArg(v_inst_64_, v_q_65_, v_T_68_, v_00_u03c4_69_, v_h_70_, v_a_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedge___boxed(lean_object* v_00_u03a6_73_, lean_object* v_n_74_, lean_object* v_m_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_q_78_, lean_object* v_00_u03ba_79_, lean_object* v_h__rank_80_, lean_object* v_T_81_, lean_object* v_00_u03c4_82_, lean_object* v_h_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_GRH_New_leadingWedge(v_00_u03a6_73_, v_n_74_, v_m_75_, v_inst_76_, v_inst_77_, v_q_78_, v_00_u03ba_79_, v_h__rank_80_, v_T_81_, v_00_u03c4_82_, v_h_83_, v_a_84_);
lean_dec_ref(v_00_u03ba_79_);
lean_dec(v_inst_76_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_GLn_SchurModule_LeadingRows_0__New_schurComplementArray_match__1_splitter___redArg(lean_object* v_x_86_, lean_object* v_h__1_87_){
_start:
{
lean_object* v_fst_88_; lean_object* v_snd_89_; lean_object* v_fst_90_; lean_object* v_snd_91_; lean_object* v___x_92_; 
v_fst_88_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_fst_88_);
v_snd_89_ = lean_ctor_get(v_x_86_, 1);
lean_inc(v_snd_89_);
lean_dec_ref(v_x_86_);
v_fst_90_ = lean_ctor_get(v_fst_88_, 0);
lean_inc(v_fst_90_);
v_snd_91_ = lean_ctor_get(v_fst_88_, 1);
lean_inc(v_snd_91_);
lean_dec(v_fst_88_);
v___x_92_ = lean_apply_3(v_h__1_87_, v_fst_90_, v_snd_91_, v_snd_89_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_GLn_SchurModule_LeadingRows_0__New_schurComplementArray_match__1_splitter(lean_object* v_00_u03a6_93_, lean_object* v_m_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_){
_start:
{
lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v_fst_100_; lean_object* v_snd_101_; lean_object* v___x_102_; 
v_fst_98_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_fst_98_);
v_snd_99_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v_x_96_);
v_fst_100_ = lean_ctor_get(v_fst_98_, 0);
lean_inc(v_fst_100_);
v_snd_101_ = lean_ctor_get(v_fst_98_, 1);
lean_inc(v_snd_101_);
lean_dec(v_fst_98_);
v___x_102_ = lean_apply_3(v_h__1_97_, v_fst_100_, v_snd_101_, v_snd_99_);
return v___x_102_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__0(lean_object* v_a_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_eq(v___y_104_, v___y_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__0___boxed(lean_object* v_a_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = lp_GRH_New_leadingWedgeMatrix___redArg___lam__0(v_a_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
lean_dec(v_a_107_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__1(lean_object* v___y_112_, lean_object* v___f_113_, lean_object* v_a_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = l_List_finRange(v___y_112_);
v___x_118_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_113_, v___x_117_, v___y_115_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__1___boxed(lean_object* v___y_119_, lean_object* v___f_120_, lean_object* v_a_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = lp_GRH_New_leadingWedgeMatrix___redArg___lam__1(v___y_119_, v___f_120_, v_a_121_, v___y_122_, v___y_123_);
lean_dec(v_a_121_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__2(lean_object* v___f_126_, lean_object* v_00_u03ba_127_, lean_object* v_a_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
lean_inc(v___y_129_);
v___f_132_ = lean_alloc_closure((void*)(lp_GRH_New_leadingWedgeMatrix___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_132_, 0, v___y_129_);
lean_closure_set(v___f_132_, 1, v___f_126_);
v___x_133_ = lean_apply_2(v_00_u03ba_127_, v_a_128_, v___y_129_);
v___x_134_ = l_List_finRange(v___x_133_);
v___x_135_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_132_, v___x_134_, v___y_130_, v___y_131_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__2___boxed(lean_object* v___f_136_, lean_object* v_00_u03ba_137_, lean_object* v_a_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = lp_GRH_New_leadingWedgeMatrix___redArg___lam__2(v___f_136_, v_00_u03ba_137_, v_a_138_, v___y_139_, v___y_140_, v___y_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_leadingWedgeMatrix___redArg___lam__3(lean_object* v___f_144_, lean_object* v_00_u03ba_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_q_148_, lean_object* v_T_149_, lean_object* v_U_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
lean_inc_n(v_a_151_, 3);
lean_inc_ref(v_00_u03ba_145_);
v___f_152_ = lean_alloc_closure((void*)(lp_GRH_New_leadingWedgeMatrix___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_152_, 0, v___f_144_);
lean_closure_set(v___f_152_, 1, v_00_u03ba_145_);
lean_closure_set(v___f_152_, 2, v_a_151_);
lean_inc(v_inst_146_);
v___x_153_ = lean_alloc_closure((void*)(lp_GRH_New_leadingWedge___boxed), 12, 10);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, lean_box(0));
lean_closure_set(v___x_153_, 3, v_inst_146_);
lean_closure_set(v___x_153_, 4, v_inst_147_);
lean_closure_set(v___x_153_, 5, v_q_148_);
lean_closure_set(v___x_153_, 6, v_00_u03ba_145_);
lean_closure_set(v___x_153_, 7, lean_box(0));
lean_closure_set(v___x_153_, 8, v_T_149_);
lean_closure_set(v___x_153_, 9, v_a_151_);
v___x_154_ = lean_apply_1(v_U_150_, v_a_151_);
v___x_155_ = lean_apply_1(v_inst_146_, v_a_151_);
v___x_156_ = l_List_lengthTR___redArg(v___x_155_);
lean_dec(v___x_155_);
v___x_157_ = l_List_finRange(v___x_156_);
v___x_158_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_152_, v___x_157_, v___x_153_, v___x_154_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__3___boxed(lean_object* v___f_159_, lean_object* v_00_u03ba_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_q_163_, lean_object* v_T_164_, lean_object* v_U_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = lp_GRH_New_leadingWedgeMatrix___redArg___lam__3(v___f_159_, v_00_u03ba_160_, v_inst_161_, v_inst_162_, v_q_163_, v_T_164_, v_U_165_, v_a_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
static lean_object* _init_lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_nat_to_int(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_to_int(v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg___lam__4(lean_object* v___f_173_, lean_object* v_00_u03ba_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_q_177_, lean_object* v_inst_178_, lean_object* v_U_179_, lean_object* v_T_180_){
_start:
{
lean_object* v___f_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___f_181_ = lean_alloc_closure((void*)(lp_GRH_New_leadingWedgeMatrix___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_181_, 0, v___f_173_);
lean_closure_set(v___f_181_, 1, v_00_u03ba_174_);
lean_closure_set(v___f_181_, 2, v_inst_175_);
lean_closure_set(v___f_181_, 3, v_inst_176_);
lean_closure_set(v___f_181_, 4, v_q_177_);
lean_closure_set(v___f_181_, 5, v_T_180_);
lean_closure_set(v___f_181_, 6, v_U_179_);
v___x_182_ = lp_mathlib_Multiset_attach___redArg(v_inst_178_);
v___x_183_ = l_List_decidableBAll___redArg(v___f_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__0, &lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__0_once, _init_lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__0);
return v___x_184_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__1, &lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__1_once, _init_lp_GRH_New_leadingWedgeMatrix___redArg___lam__4___closed__1);
return v___x_185_;
}
}
}
static lean_object* _init_lp_GRH_New_leadingWedgeMatrix___redArg___closed__0(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lp_mathlib_Equiv_refl___redArg();
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix___redArg(lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_q_190_, lean_object* v_00_u03ba_191_, lean_object* v_inst_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; lean_object* v_toFun_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_199_; 
v___x_195_ = lean_obj_once(&lp_GRH_New_leadingWedgeMatrix___redArg___closed__0, &lp_GRH_New_leadingWedgeMatrix___redArg___closed__0_once, _init_lp_GRH_New_leadingWedgeMatrix___redArg___closed__0);
v_toFun_196_ = lean_ctor_get(v___x_195_, 0);
v___f_197_ = ((lean_object*)(lp_GRH_New_leadingWedgeMatrix___redArg___closed__1));
v___f_198_ = lean_alloc_closure((void*)(lp_GRH_New_leadingWedgeMatrix___redArg___lam__4), 8, 6);
lean_closure_set(v___f_198_, 0, v___f_197_);
lean_closure_set(v___f_198_, 1, v_00_u03ba_191_);
lean_closure_set(v___f_198_, 2, v_inst_188_);
lean_closure_set(v___f_198_, 3, v_inst_189_);
lean_closure_set(v___f_198_, 4, v_q_190_);
lean_closure_set(v___f_198_, 5, v_inst_192_);
lean_inc(v_toFun_196_);
v___x_199_ = lean_apply_3(v_toFun_196_, v___f_198_, v_a_193_, v_a_194_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_leadingWedgeMatrix(lean_object* v_00_u03a6_200_, lean_object* v_n_201_, lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_q_205_, lean_object* v_00_u03ba_206_, lean_object* v_inst_207_, lean_object* v_h__rank_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lp_GRH_New_leadingWedgeMatrix___redArg(v_inst_203_, v_inst_204_, v_q_205_, v_00_u03ba_206_, v_inst_207_, v_a_209_, v_a_210_);
return v___x_211_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_GramMatrix(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GLn_SchurModule_LeadingRows(uint8_t builtin) {
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
res = initialize_GRH_Lib_GLn_SchurModule_GramMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
