// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.LiftLat
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.RowLat
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
lean_object* lp_tree_Formalism_L2_Col_firstValA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_firstValB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_liftDat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_liftDat___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale___redArg(lean_object* v_inst_1_, lean_object* v_r_2_, lean_object* v_m_3_, lean_object* v_t_4_, lean_object* v_q_5_, lean_object* v_etaV_6_, lean_object* v_P_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toSemiring_10_; lean_object* v___x_11_; lean_object* v_toMul_12_; lean_object* v___x_13_; lean_object* v_toMonoid_14_; lean_object* v_val_15_; lean_object* v_toNPow_16_; lean_object* v___x_17_; lean_object* v_toRing_18_; lean_object* v___x_19_; lean_object* v_toAddMonoidWithOne_20_; lean_object* v_toNatCast_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_9_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_8_);
v_toSemiring_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref_n(v_toSemiring_10_, 2);
lean_dec_ref(v___x_9_);
v___x_11_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_10_);
v_toMul_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_toMul_12_);
lean_dec_ref(v___x_11_);
lean_inc(v_P_7_);
v___x_13_ = lean_apply_1(v_etaV_6_, v_P_7_);
v_toMonoid_14_ = lean_ctor_get(v_toSemiring_10_, 1);
lean_inc_ref(v_toMonoid_14_);
lean_dec_ref(v_toSemiring_10_);
v_val_15_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_val_15_);
lean_dec_ref(v___x_13_);
v_toNPow_16_ = lean_ctor_get(v_toMonoid_14_, 2);
lean_inc(v_toNPow_16_);
lean_dec_ref(v_toMonoid_14_);
v___x_17_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_1_);
v_toRing_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_toRing_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_18_);
v_toAddMonoidWithOne_20_ = lean_ctor_get(v___x_19_, 1);
lean_inc_ref(v_toAddMonoidWithOne_20_);
lean_dec_ref(v___x_19_);
v_toNatCast_21_ = lean_ctor_get(v_toAddMonoidWithOne_20_, 0);
lean_inc(v_toNatCast_21_);
lean_dec_ref(v_toAddMonoidWithOne_20_);
v___x_22_ = lean_apply_1(v_q_5_, v_P_7_);
v___x_23_ = lean_apply_1(v_toNatCast_21_, v___x_22_);
v___x_24_ = lean_unsigned_to_nat(2u);
v___x_25_ = lean_nat_mul(v___x_24_, v_r_2_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_m_3_, v___x_26_);
v___x_28_ = lean_nat_mul(v___x_27_, v_t_4_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_add(v___x_25_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_25_);
v___x_30_ = lean_nat_sub(v___x_29_, v___x_26_);
lean_dec(v___x_29_);
v___x_31_ = lean_nat_shiftr(v___x_30_, v___x_26_);
lean_dec(v___x_30_);
v___x_32_ = lean_apply_2(v_toNPow_16_, v___x_31_, v___x_23_);
v___x_33_ = lean_apply_2(v_toMul_12_, v_val_15_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale___redArg___boxed(lean_object* v_inst_34_, lean_object* v_r_35_, lean_object* v_m_36_, lean_object* v_t_37_, lean_object* v_q_38_, lean_object* v_etaV_39_, lean_object* v_P_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_Formalism_L2_DIV_trScale___redArg(v_inst_34_, v_r_35_, v_m_36_, v_t_37_, v_q_38_, v_etaV_39_, v_P_40_);
lean_dec(v_t_37_);
lean_dec(v_m_36_);
lean_dec(v_r_35_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale(lean_object* v_K_42_, lean_object* v_inst_43_, lean_object* v_Pl_44_, lean_object* v_r_45_, lean_object* v_m_46_, lean_object* v_t_47_, lean_object* v_q_48_, lean_object* v_etaV_49_, lean_object* v_P_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_tree_Formalism_L2_DIV_trScale___redArg(v_inst_43_, v_r_45_, v_m_46_, v_t_47_, v_q_48_, v_etaV_49_, v_P_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_trScale___boxed(lean_object* v_K_52_, lean_object* v_inst_53_, lean_object* v_Pl_54_, lean_object* v_r_55_, lean_object* v_m_56_, lean_object* v_t_57_, lean_object* v_q_58_, lean_object* v_etaV_59_, lean_object* v_P_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_tree_Formalism_L2_DIV_trScale(v_K_52_, v_inst_53_, v_Pl_54_, v_r_55_, v_m_56_, v_t_57_, v_q_58_, v_etaV_59_, v_P_60_);
lean_dec(v_t_57_);
lean_dec(v_m_56_);
lean_dec(v_r_55_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__0(lean_object* v_self_62_){
_start:
{
lean_inc(v_self_62_);
return v_self_62_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__0___boxed(lean_object* v_self_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__0(v_self_63_);
lean_dec(v_self_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__1(lean_object* v_q_65_, lean_object* v_P_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_1(v_q_65_, v_P_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__2(lean_object* v_inst_68_, lean_object* v_muV_69_, lean_object* v_etaV_70_, lean_object* v_q_71_, lean_object* v_r_72_, lean_object* v_P_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_tree_Formalism_L2_Col_firstValA___redArg(v_inst_68_, v_muV_69_, v_etaV_70_, v_q_71_, v_r_72_, v_P_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__2___boxed(lean_object* v_inst_75_, lean_object* v_muV_76_, lean_object* v_etaV_77_, lean_object* v_q_78_, lean_object* v_r_79_, lean_object* v_P_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__2(v_inst_75_, v_muV_76_, v_etaV_77_, v_q_78_, v_r_79_, v_P_80_);
lean_dec(v_r_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___redArg(lean_object* v_inst_83_, lean_object* v_S_84_, lean_object* v_00_u03c1_85_, lean_object* v_op_86_, lean_object* v_r_87_, lean_object* v_t_88_, lean_object* v_q_89_, lean_object* v_muV_90_, lean_object* v_etaV_91_){
_start:
{
lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___f_92_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_liftDat___redArg___closed__0));
lean_inc_ref(v_q_89_);
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__1), 2, 1);
lean_closure_set(v___f_93_, 0, v_q_89_);
lean_inc(v_r_87_);
v___f_94_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_94_, 0, v_inst_83_);
lean_closure_set(v___f_94_, 1, v_muV_90_);
lean_closure_set(v___f_94_, 2, v_etaV_91_);
lean_closure_set(v___f_94_, 3, v_q_89_);
lean_closure_set(v___f_94_, 4, v_r_87_);
v___x_95_ = lean_nat_add(v_r_87_, v_t_88_);
lean_dec(v_r_87_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___f_94_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_98_, 0, v_S_84_);
lean_ctor_set(v___x_98_, 1, v_00_u03c1_85_);
lean_ctor_set(v___x_98_, 2, v___f_92_);
lean_ctor_set(v___x_98_, 3, v___f_93_);
lean_ctor_set(v___x_98_, 4, v___x_95_);
lean_ctor_set(v___x_98_, 5, v_t_88_);
lean_ctor_set(v___x_98_, 6, v_op_86_);
lean_ctor_set(v___x_98_, 7, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat(lean_object* v_K_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_G_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_Pl0_106_, lean_object* v_S_107_, lean_object* v_00_u03c1_108_, lean_object* v_ok_109_, lean_object* v_op_110_, lean_object* v_r_111_, lean_object* v_t_112_, lean_object* v_q_113_, lean_object* v_muV_114_, lean_object* v_etaV_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lp_tree_Formalism_L2_DIV_liftDat___redArg(v_inst_100_, v_S_107_, v_00_u03c1_108_, v_op_110_, v_r_111_, v_t_112_, v_q_113_, v_muV_114_, v_etaV_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_liftDat___boxed(lean_object** _args){
lean_object* v_K_117_ = _args[0];
lean_object* v_inst_118_ = _args[1];
lean_object* v_inst_119_ = _args[2];
lean_object* v_inst_120_ = _args[3];
lean_object* v_G_121_ = _args[4];
lean_object* v_inst_122_ = _args[5];
lean_object* v_inst_123_ = _args[6];
lean_object* v_Pl0_124_ = _args[7];
lean_object* v_S_125_ = _args[8];
lean_object* v_00_u03c1_126_ = _args[9];
lean_object* v_ok_127_ = _args[10];
lean_object* v_op_128_ = _args[11];
lean_object* v_r_129_ = _args[12];
lean_object* v_t_130_ = _args[13];
lean_object* v_q_131_ = _args[14];
lean_object* v_muV_132_ = _args[15];
lean_object* v_etaV_133_ = _args[16];
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_tree_Formalism_L2_DIV_liftDat(v_K_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_G_121_, v_inst_122_, v_inst_123_, v_Pl0_124_, v_S_125_, v_00_u03c1_126_, v_ok_127_, v_op_128_, v_r_129_, v_t_130_, v_q_131_, v_muV_132_, v_etaV_133_);
lean_dec(v_inst_123_);
lean_dec_ref(v_inst_122_);
lean_dec(v_inst_120_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___redArg___lam__2(lean_object* v_muV_135_, lean_object* v_inst_136_, lean_object* v_q_137_, lean_object* v_r_138_, lean_object* v_m_139_, lean_object* v_t_140_, lean_object* v_j_141_, lean_object* v_P_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_apply_1(v_muV_135_, v_j_141_);
v___x_144_ = lp_tree_Formalism_L2_Col_firstValB___redArg(v_inst_136_, v___x_143_, v_q_137_, v_r_138_, v_m_139_, v_t_140_, v_P_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___redArg___lam__2___boxed(lean_object* v_muV_145_, lean_object* v_inst_146_, lean_object* v_q_147_, lean_object* v_r_148_, lean_object* v_m_149_, lean_object* v_t_150_, lean_object* v_j_151_, lean_object* v_P_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_tree_Formalism_L2_DIV_rowDat___redArg___lam__2(v_muV_145_, v_inst_146_, v_q_147_, v_r_148_, v_m_149_, v_t_150_, v_j_151_, v_P_152_);
lean_dec(v_t_150_);
lean_dec(v_m_149_);
lean_dec(v_r_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___redArg(lean_object* v_inst_154_, lean_object* v_S_155_, lean_object* v_00_u03c1_156_, lean_object* v_op_157_, lean_object* v_r_158_, lean_object* v_m_159_, lean_object* v_t_160_, lean_object* v_q_161_, lean_object* v_muV_162_){
_start:
{
lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___f_163_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_liftDat___redArg___closed__0));
lean_inc_ref(v_q_161_);
v___f_164_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_liftDat___redArg___lam__1), 2, 1);
lean_closure_set(v___f_164_, 0, v_q_161_);
lean_inc(v_t_160_);
lean_inc(v_m_159_);
lean_inc(v_r_158_);
v___f_165_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_DIV_rowDat___redArg___lam__2___boxed), 8, 6);
lean_closure_set(v___f_165_, 0, v_muV_162_);
lean_closure_set(v___f_165_, 1, v_inst_154_);
lean_closure_set(v___f_165_, 2, v_q_161_);
lean_closure_set(v___f_165_, 3, v_r_158_);
lean_closure_set(v___f_165_, 4, v_m_159_);
lean_closure_set(v___f_165_, 5, v_t_160_);
v___x_166_ = lean_nat_mul(v_m_159_, v_t_160_);
v___x_167_ = lean_nat_add(v_r_158_, v___x_166_);
lean_dec(v___x_166_);
lean_dec(v_r_158_);
v___x_168_ = l_List_ofFn___redArg(v_m_159_, v___f_165_);
v___x_169_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_169_, 0, v_S_155_);
lean_ctor_set(v___x_169_, 1, v_00_u03c1_156_);
lean_ctor_set(v___x_169_, 2, v___f_163_);
lean_ctor_set(v___x_169_, 3, v___f_164_);
lean_ctor_set(v___x_169_, 4, v___x_167_);
lean_ctor_set(v___x_169_, 5, v_t_160_);
lean_ctor_set(v___x_169_, 6, v_op_157_);
lean_ctor_set(v___x_169_, 7, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat(lean_object* v_K_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_G_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_Pl0_177_, lean_object* v_S_178_, lean_object* v_00_u03c1_179_, lean_object* v_ok_180_, lean_object* v_op_181_, lean_object* v_r_182_, lean_object* v_m_183_, lean_object* v_t_184_, lean_object* v_q_185_, lean_object* v_muV_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lp_tree_Formalism_L2_DIV_rowDat___redArg(v_inst_171_, v_S_178_, v_00_u03c1_179_, v_op_181_, v_r_182_, v_m_183_, v_t_184_, v_q_185_, v_muV_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_rowDat___boxed(lean_object** _args){
lean_object* v_K_188_ = _args[0];
lean_object* v_inst_189_ = _args[1];
lean_object* v_inst_190_ = _args[2];
lean_object* v_inst_191_ = _args[3];
lean_object* v_G_192_ = _args[4];
lean_object* v_inst_193_ = _args[5];
lean_object* v_inst_194_ = _args[6];
lean_object* v_Pl0_195_ = _args[7];
lean_object* v_S_196_ = _args[8];
lean_object* v_00_u03c1_197_ = _args[9];
lean_object* v_ok_198_ = _args[10];
lean_object* v_op_199_ = _args[11];
lean_object* v_r_200_ = _args[12];
lean_object* v_m_201_ = _args[13];
lean_object* v_t_202_ = _args[14];
lean_object* v_q_203_ = _args[15];
lean_object* v_muV_204_ = _args[16];
_start:
{
lean_object* v_res_205_; 
v_res_205_ = lp_tree_Formalism_L2_DIV_rowDat(v_K_188_, v_inst_189_, v_inst_190_, v_inst_191_, v_G_192_, v_inst_193_, v_inst_194_, v_Pl0_195_, v_S_196_, v_00_u03c1_197_, v_ok_198_, v_op_199_, v_r_200_, v_m_201_, v_t_202_, v_q_203_, v_muV_204_);
lean_dec(v_inst_194_);
lean_dec_ref(v_inst_193_);
lean_dec(v_inst_191_);
return v_res_205_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
