// Lean compiler output
// Module: Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
// Imports: public import Init public meta import Init public import Formalism.GradedWeylDivisibility.StatementD public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
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
uint8_t lp_mathlib_Nat_instDecidablePredEven(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_npowBinRec_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_MainNotions_G_twistVec___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__0_value;
static lean_once_cell_t lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_posAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_posAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nuOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_LeAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_LeAt___boxed(lean_object**);
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_Ar___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__0 = (const lean_object*)&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__0_value;
static lean_once_cell_t lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_scale(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_scale___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_order(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_order___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_predual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_predual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_latDual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_latDual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_tree_Formalism_MainNotions_G_Edge_dual___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree_Formalism_MainNotions_G_Edge_dual___closed__0 = (const lean_object*)&lp_tree_Formalism_MainNotions_G_Edge_dual___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Edge_dual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Edge_dual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colSpan(lean_object* v_R_1_, lean_object* v_K_2_, lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_k_6_, lean_object* v_g_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_colSpan___boxed(lean_object* v_R_9_, lean_object* v_K_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_k_14_, lean_object* v_g_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_MainNotions_G_colSpan(v_R_9_, v_K_10_, v_inst_11_, v_inst_12_, v_inst_13_, v_k_14_, v_g_15_);
lean_dec(v_g_15_);
lean_dec(v_k_14_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg___lam__0(lean_object* v_g_17_, lean_object* v_h_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_mathlib_Equiv_trans___redArg(v_h_18_, v_g_17_);
return v___x_19_;
}
}
static lean_object* _init_lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__1(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg(lean_object* v_00_u03b9_22_, lean_object* v_00_u03c3_23_, lean_object* v_s_24_, lean_object* v_v_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v_toFun_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___f_27_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__0));
v___x_28_ = lean_obj_once(&lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__1, &lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__1_once, _init_lp_tree_Formalism_MainNotions_G_twistVec___redArg___closed__1);
v___x_29_ = lp_mathlib_npowBinRec_go___redArg(v___f_27_, v_s_24_, v___x_28_, v_00_u03c3_23_);
v_toFun_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_toFun_30_);
lean_dec(v___x_29_);
v___x_31_ = lean_apply_1(v_v_25_, v_i_26_);
v___x_32_ = lean_apply_1(v_toFun_30_, v___x_31_);
v___x_33_ = lean_apply_1(v_00_u03b9_22_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___redArg___boxed(lean_object* v_00_u03b9_34_, lean_object* v_00_u03c3_35_, lean_object* v_s_36_, lean_object* v_v_37_, lean_object* v_i_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_MainNotions_G_twistVec___redArg(v_00_u03b9_34_, v_00_u03c3_35_, v_s_36_, v_v_37_, v_i_38_);
lean_dec(v_s_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec(lean_object* v_Qq_40_, lean_object* v_Kf_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_00_u03b9_44_, lean_object* v_00_u03c3_45_, lean_object* v_s_46_, lean_object* v_k_47_, lean_object* v_v_48_, lean_object* v_i_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_tree_Formalism_MainNotions_G_twistVec___redArg(v_00_u03b9_44_, v_00_u03c3_45_, v_s_46_, v_v_48_, v_i_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_twistVec___boxed(lean_object* v_Qq_51_, lean_object* v_Kf_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_00_u03b9_55_, lean_object* v_00_u03c3_56_, lean_object* v_s_57_, lean_object* v_k_58_, lean_object* v_v_59_, lean_object* v_i_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_MainNotions_G_twistVec(v_Qq_51_, v_Kf_52_, v_inst_53_, v_inst_54_, v_00_u03b9_55_, v_00_u03c3_56_, v_s_57_, v_k_58_, v_v_59_, v_i_60_);
lean_dec(v_k_58_);
lean_dec(v_s_57_);
lean_dec_ref(v_inst_54_);
lean_dec_ref(v_inst_53_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extO(lean_object* v_O_62_, lean_object* v_W_63_, lean_object* v_Qq_64_, lean_object* v_Kf_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_00_u03b9_72_, lean_object* v_00_u03c3_73_, lean_object* v_s_74_, lean_object* v_k_75_, lean_object* v_L_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_extO___boxed(lean_object* v_O_78_, lean_object* v_W_79_, lean_object* v_Qq_80_, lean_object* v_Kf_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_00_u03b9_88_, lean_object* v_00_u03c3_89_, lean_object* v_s_90_, lean_object* v_k_91_, lean_object* v_L_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_Formalism_MainNotions_G_extO(v_O_78_, v_W_79_, v_Qq_80_, v_Kf_81_, v_inst_82_, v_inst_83_, v_inst_84_, v_inst_85_, v_inst_86_, v_inst_87_, v_00_u03b9_88_, v_00_u03c3_89_, v_s_90_, v_k_91_, v_L_92_);
lean_dec(v_k_91_);
lean_dec(v_s_90_);
lean_dec_ref(v_00_u03c3_89_);
lean_dec(v_00_u03b9_88_);
lean_dec_ref(v_inst_87_);
lean_dec_ref(v_inst_86_);
lean_dec_ref(v_inst_85_);
lean_dec_ref(v_inst_84_);
lean_dec_ref(v_inst_83_);
lean_dec_ref(v_inst_82_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_posAdd(lean_object* v_n_x27_94_, lean_object* v_s_95_, lean_object* v_e_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_nat_add(v_s_95_, v_e_96_);
v___x_98_ = lean_nat_mod(v___x_97_, v_n_x27_94_);
lean_dec(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_posAdd___boxed(lean_object* v_n_x27_99_, lean_object* v_s_100_, lean_object* v_e_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_tree_Formalism_MainNotions_G_posAdd(v_n_x27_99_, v_s_100_, v_e_101_);
lean_dec(v_e_101_);
lean_dec(v_s_100_);
lean_dec(v_n_x27_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt___redArg(lean_object* v_m_103_, lean_object* v_lam0_104_, lean_object* v_s_105_, lean_object* v_a_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = lp_mathlib_Nat_instDecidablePredEven(v_s_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_m_103_, v___x_108_);
v___x_110_ = lean_nat_add(v_a_106_, v___x_108_);
lean_dec(v_a_106_);
v___x_111_ = lean_nat_sub(v___x_109_, v___x_110_);
lean_dec(v___x_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_apply_2(v_lam0_104_, v_s_105_, v___x_111_);
v___x_113_ = lean_int_neg(v___x_112_);
lean_dec(v___x_112_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_apply_2(v_lam0_104_, v_s_105_, v_a_106_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt___redArg___boxed(lean_object* v_m_115_, lean_object* v_lam0_116_, lean_object* v_s_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_tree_Formalism_MainNotions_G_lamAt___redArg(v_m_115_, v_lam0_116_, v_s_117_, v_a_118_);
lean_dec(v_m_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt(lean_object* v_n_x27_120_, lean_object* v_m_121_, lean_object* v_lam0_122_, lean_object* v_s_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lp_tree_Formalism_MainNotions_G_lamAt___redArg(v_m_121_, v_lam0_122_, v_s_123_, v_a_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_lamAt___boxed(lean_object* v_n_x27_126_, lean_object* v_m_127_, lean_object* v_lam0_128_, lean_object* v_s_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_tree_Formalism_MainNotions_G_lamAt(v_n_x27_126_, v_m_127_, v_lam0_128_, v_s_129_, v_a_130_);
lean_dec(v_m_127_);
lean_dec(v_n_x27_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_nuOf(lean_object* v_m_132_, lean_object* v_lam_133_, lean_object* v_t_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_inc_ref(v_lam_133_);
v___x_135_ = lean_apply_1(v_lam_133_, v_t_134_);
v___x_136_ = lean_apply_1(v_lam_133_, v_m_132_);
v___x_137_ = lean_int_sub(v___x_135_, v___x_136_);
lean_dec(v___x_136_);
lean_dec(v___x_135_);
v___x_138_ = l_Int_toNat(v___x_137_);
lean_dec(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_LeAt(lean_object* v_W_139_, lean_object* v_Qq_140_, lean_object* v_O_141_, lean_object* v_Kf_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_p_149_, lean_object* v_00_u03b9_150_, lean_object* v_00_u03c3_151_, lean_object* v_w_152_, lean_object* v_s_153_, lean_object* v_k_154_, lean_object* v_e_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_LeAt___boxed(lean_object** _args){
lean_object* v_W_157_ = _args[0];
lean_object* v_Qq_158_ = _args[1];
lean_object* v_O_159_ = _args[2];
lean_object* v_Kf_160_ = _args[3];
lean_object* v_inst_161_ = _args[4];
lean_object* v_inst_162_ = _args[5];
lean_object* v_inst_163_ = _args[6];
lean_object* v_inst_164_ = _args[7];
lean_object* v_inst_165_ = _args[8];
lean_object* v_inst_166_ = _args[9];
lean_object* v_p_167_ = _args[10];
lean_object* v_00_u03b9_168_ = _args[11];
lean_object* v_00_u03c3_169_ = _args[12];
lean_object* v_w_170_ = _args[13];
lean_object* v_s_171_ = _args[14];
lean_object* v_k_172_ = _args[15];
lean_object* v_e_173_ = _args[16];
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_tree_Formalism_MainNotions_G_LeAt(v_W_157_, v_Qq_158_, v_O_159_, v_Kf_160_, v_inst_161_, v_inst_162_, v_inst_163_, v_inst_164_, v_inst_165_, v_inst_166_, v_p_167_, v_00_u03b9_168_, v_00_u03c3_169_, v_w_170_, v_s_171_, v_k_172_, v_e_173_);
lean_dec_ref(v_e_173_);
lean_dec(v_k_172_);
lean_dec(v_s_171_);
lean_dec(v_w_170_);
lean_dec_ref(v_00_u03c3_169_);
lean_dec(v_00_u03b9_168_);
lean_dec(v_p_167_);
lean_dec_ref(v_inst_166_);
lean_dec_ref(v_inst_165_);
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
lean_dec_ref(v_inst_162_);
lean_dec_ref(v_inst_161_);
return v_res_174_;
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_MainNotions_G_Ar___lam__0(lean_object* v_r_175_, lean_object* v_a_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = lean_nat_dec_lt(v_a_176_, v_r_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__0___boxed(lean_object* v_r_178_, lean_object* v_a_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = lp_tree_Formalism_MainNotions_G_Ar___lam__0(v_r_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec(v_r_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__1(lean_object* v_m_182_, lean_object* v_lam0_183_, lean_object* v_s_184_, lean_object* v_i_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lp_tree_Formalism_MainNotions_G_lamAt___redArg(v_m_182_, v_lam0_183_, v_s_184_, v_i_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__1___boxed(lean_object* v_m_187_, lean_object* v_lam0_188_, lean_object* v_s_189_, lean_object* v_i_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lp_tree_Formalism_MainNotions_G_Ar___lam__1(v_m_187_, v_lam0_188_, v_s_189_, v_i_190_);
lean_dec(v_m_187_);
return v_res_191_;
}
}
static lean_object* _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0(lean_object* v_s_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___f_196_ = ((lean_object*)(lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__0));
v___x_197_ = lean_obj_once(&lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__1, &lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__1_once, _init_lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0___closed__1);
v___x_198_ = l_List_foldrTR___redArg(v___f_196_, v___x_197_, v_s_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object* v_s_199_, lean_object* v_f_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lp_mathlib_Multiset_map___redArg(v_f_200_, v_s_199_);
v___x_202_ = lp_tree_Multiset_sum___at___00Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0_spec__0(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar___lam__2(lean_object* v_m_203_, lean_object* v_lam0_204_, lean_object* v___f_205_, lean_object* v_s_206_){
_start:
{
lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc(v_m_203_);
v___f_207_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_Ar___lam__1___boxed), 4, 3);
lean_closure_set(v___f_207_, 0, v_m_203_);
lean_closure_set(v___f_207_, 1, v_lam0_204_);
lean_closure_set(v___f_207_, 2, v_s_206_);
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_m_203_, v___x_208_);
lean_dec(v_m_203_);
v___x_210_ = l_List_finRange(v___x_209_);
v___x_211_ = lp_mathlib_Multiset_filter___redArg(v___f_205_, v___x_210_);
v___x_212_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_211_, v___f_207_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Ar(lean_object* v_n_x27_213_, lean_object* v_m_214_, lean_object* v_r_215_, lean_object* v_lam0_216_){
_start:
{
lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___f_217_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_Ar___lam__0___boxed), 2, 1);
lean_closure_set(v___f_217_, 0, v_r_215_);
v___f_218_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_G_Ar___lam__2), 4, 3);
lean_closure_set(v___f_218_, 0, v_m_214_);
lean_closure_set(v___f_218_, 1, v_lam0_216_);
lean_closure_set(v___f_218_, 2, v___f_217_);
v___x_219_ = l_List_finRange(v_n_x27_213_);
v___x_220_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_219_, v___f_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0(lean_object* v_00_u03b9_221_, lean_object* v_s_222_, lean_object* v_f_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v_s_222_, v_f_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_scale(lean_object* v_O_225_, lean_object* v_Kf_226_, lean_object* v_X_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_c_235_, lean_object* v_M_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(0);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_scale___boxed(lean_object* v_O_238_, lean_object* v_Kf_239_, lean_object* v_X_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_c_248_, lean_object* v_M_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = lp_tree_Formalism_MainNotions_G_scale(v_O_238_, v_Kf_239_, v_X_240_, v_inst_241_, v_inst_242_, v_inst_243_, v_inst_244_, v_inst_245_, v_inst_246_, v_inst_247_, v_c_248_, v_M_249_);
lean_dec(v_c_248_);
lean_dec(v_inst_246_);
lean_dec(v_inst_245_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
lean_dec_ref(v_inst_242_);
lean_dec_ref(v_inst_241_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_order(lean_object* v_n_x27_251_, lean_object* v_m_252_, lean_object* v_r_253_, lean_object* v_lam0_254_, lean_object* v_00_u03c0_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lp_tree_Formalism_MainNotions_G_Ar(v_n_x27_251_, v_m_252_, v_r_253_, v_lam0_254_);
v___x_257_ = lean_int_sub(v___x_256_, v_00_u03c0_255_);
lean_dec(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_order___boxed(lean_object* v_n_x27_258_, lean_object* v_m_259_, lean_object* v_r_260_, lean_object* v_lam0_261_, lean_object* v_00_u03c0_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = lp_tree_Formalism_MainNotions_G_order(v_n_x27_258_, v_m_259_, v_r_260_, v_lam0_261_, v_00_u03c0_262_);
lean_dec(v_00_u03c0_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_predual(lean_object* v_O_264_, lean_object* v_Kf_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_V_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_A_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_box(0);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_predual___boxed(lean_object* v_O_276_, lean_object* v_Kf_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_V_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_A_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = lp_tree_Formalism_MainNotions_G_predual(v_O_276_, v_Kf_277_, v_inst_278_, v_inst_279_, v_inst_280_, v_V_281_, v_inst_282_, v_inst_283_, v_inst_284_, v_inst_285_, v_A_286_);
lean_dec(v_inst_284_);
lean_dec(v_inst_283_);
lean_dec_ref(v_inst_282_);
lean_dec_ref(v_inst_280_);
lean_dec_ref(v_inst_279_);
lean_dec_ref(v_inst_278_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_latDual(lean_object* v_W_288_, lean_object* v_Qq_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_k_293_, lean_object* v_L_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_latDual___boxed(lean_object* v_W_296_, lean_object* v_Qq_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_k_301_, lean_object* v_L_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = lp_tree_Formalism_MainNotions_G_latDual(v_W_296_, v_Qq_297_, v_inst_298_, v_inst_299_, v_inst_300_, v_k_301_, v_L_302_);
lean_dec(v_k_301_);
lean_dec_ref(v_inst_300_);
lean_dec_ref(v_inst_299_);
lean_dec_ref(v_inst_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Edge_dual(lean_object* v_W_306_, lean_object* v_Qq_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_k_311_, lean_object* v_e_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = ((lean_object*)(lp_tree_Formalism_MainNotions_G_Edge_dual___closed__0));
return v___x_313_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_G_Edge_dual___boxed(lean_object* v_W_314_, lean_object* v_Qq_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_k_319_, lean_object* v_e_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = lp_tree_Formalism_MainNotions_G_Edge_dual(v_W_314_, v_Qq_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_k_319_, v_e_320_);
lean_dec_ref(v_e_320_);
lean_dec(v_k_319_);
lean_dec_ref(v_inst_318_);
lean_dec_ref(v_inst_317_);
lean_dec_ref(v_inst_316_);
return v_res_321_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_GradedWeylDivisibility_StatementD(uint8_t builtin);
lean_object* initialize_tree_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_GradedWeylDivisibility_StatementD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
